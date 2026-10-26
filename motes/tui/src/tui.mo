// Terminal UI Library - the application loop (Phase 7, v3: async performs)
//
// `run_app` is the Elm-architecture entry point: the app is a record
// of `init`/`on_event`/`update`/`view` plus a frame clock, and the loop
// wires the pull reader (input.mo), the fold semantics (frp.mo pins
// them) and the renderer (render.mo) around it. One loop, one write per
// changed model:
//
//   poll_turns (pending async turns)                   ->  drained Msgs
//   Input.produce (poll/read/decode + resize + tick)  ->  List Event
//   on_event lifts each Event into the app's own Msg
//   fold update over the model (dispatch/perform -> next frame)  ->  S * Cmd
//   view -> render -> diff (or a forced full repaint) -> apply_deltas  ->  write
//
// `Cmd` is the side-channel: `update` returns commands rather than
// performing them itself. `dispatch` re-enters the message list one frame
// later (the same step semantics `EventStream.fold` table-tests); `perform`
// runs real IO INLINE, during the same fold, and feeds its result back the
// same way `dispatch` does -- the one thing `update` cannot express on its
// own, since `update` itself stays pure.
//
// v2 shape change, recorded here so it is a decision, not drift: `App`/
// `Cmd` gained a second type parameter `M` (the app's own message type),
// and `App` gained `on_event : Event -> M`. v1 had
// `update : S -> Event -> Pair S Cmd` -- update consumed the terminal's own
// event type directly, and there was no way for an app to drive real IO (a
// network call, a subprocess) from inside the loop at all. `Cmd.perform
// (action : Unit -> IO M)` closes that gap without reaching for
// concurrency: `std/concurrent` has no non-blocking fiber-poll primitive on
// either backend (confirmed when weaver's interactive TUI needed exactly
// this), so `perform`'s action runs synchronously, blocking the frame it
// was returned from -- the same trade-off a line-based UI already makes
// over `IO.read_line`.
//
// v3, same reasoning in the other direction: `pollFiber` (async-threading
// 7a.5) landed, and `Cmd.perform_async action on_error` is its
// adoption. The action FORKS (`forkIO`); the result folds back whenever the
// loop's `poll_turns` sees the fiber complete -- a frame boundary the
// action's own turn never blocks (weaver's model turn runs on it, and a
// spinner animates while it does). The loop owns every pending handle:
// fork/poll happen only there, and each handle has exactly one consumer
// (poll), which is what keeps the host's "already consumed / cancelled" eval
// errors structurally unreachable. While a turn is pending the loop
// still reads stdin UNLESS the app's `reads_input` says a modal dialog on
// the fiber owns it (produce_poll_only) -- a second stdin reader would
// race that dialog for every byte and, on a lost poll wake, block the
// whole UI in `read_stdin_exact` (a blocking read). Weaver's dialogs use
// a small file handshake (`overlay.mo`): the dialog asks for stdin, the
// app acks from `reads_input` only once it has stopped drawing, and the
// loop clears + repaints when the dialog releases it.
//
// A `perform` that renders to the real terminal outside this loop's own
// `view`/`render`/`diff` pipeline (an approval overlay is exactly this use
// case) leaves `prev` stale: the next diff would compare the model's
// screen against a `prev` that no longer matches what is actually on the
// terminal, and could leave stray pixels behind. `step_batch`/`step_cmd`
// thread a `forced : Bool` alongside the model and the queued messages, set
// whenever ANY `perform` fired during that batch's fold, and `draw_frame`
// repaints from a blank SCREEN MODEL for it. That is not enough to erase
// whatever the action wrote: blank cells emit no delta. The contract is
// therefore that a perform which writes the terminal clears it (ESC[2J)
// before returning its message; a resize is cleared by `draw_frame` itself,
// because the old geometry cannot be mapped onto the new one.
//
// v1 shape deviations, still true in v2:
//   * `update` is PURE (`S -> M -> Pair S (Cmd M)`), not
//     `TuiT M Raw Raw (S * Cmd)` -- the transformer (tuit.mo) lifts this
//     loop's halves; the pure update is the 90% case the plan's App record
//     is for.
//   * `tick_ms` is a field of `App`: a frame clock has to live somewhere,
//     and negative = block until input, no ticks.
//   * `run_frp` is deferred: the cold FRP core deliberately has no live
//     signals, and `run_app` IS the live composition point.
//   * Panic recovery is the honest v1 version: the terminal is restored on
//     every CONTROLLED exit (quit, EOF). A hard crash still strands the alt
//     screen -- unwinding through the restore path needs the error-effect
//     story (tuit.mo's `ResultT` stack).
//
// `Cmd`'s `beep`/`set_clipboard`/`open_url` from the plan's original sketch
// need natives that do not exist yet; they stay unimplemented rather than
// stubbed.

use lib::types { CellDelta, Event, Screen }
use lib::core { empty_screen, mk_rect }
use lib::render { apply_deltas, diff, render }
use lib::widget { Widget }
use lib::input { Input.produce, Input.produce_poll_only, InputReader, input_reader }
use lib::terminal {
    Terminal.clear_screen, Terminal.cursor_hide, Terminal.cursor_move, Terminal.cursor_show,
    Terminal.enable_mouse, Terminal.disable_mouse,
    Terminal.enable_bracketed_paste, Terminal.disable_bracketed_paste,
    Terminal.enter_alt_screen, Terminal.enter_raw_mode, Terminal.leave_alt_screen,
    Terminal.leave_raw_mode, Terminal.reset_style, Terminal.size
}
use std::concurrent::fiber {Fiber, FiberError, forkIO, pollFiber}
use std::io { IO.flush_stdout, IO.write_stdout }
use std::list { List.length }

/// Commands `update` returns instead of performing. `none` is the
/// ordinary case, `quit` stops the loop (the terminal is restored),
/// `dispatch` injects a message into the NEXT frame's batch, `perform`
/// runs real IO now and folds its result message in as if it had been
/// dispatched.
pub type Cmd (M : Type) {
    /// Nothing to do.
    none,
    /// Stop the app; the terminal is restored.
    quit,
    /// Inject `msg` into the next frame's message batch.
    dispatch (msg : M),
    /// Run `action` now (blocking this frame) and fold its result message
    /// in immediately, the same way a `dispatch`ed message is folded.
    perform (action : Unit -> IO M),
    /// Like `perform`, but WITHOUT forcing a repaint. For a cheap poll
    /// whose result touches only a small part of the frame (a live usage
    /// read): a `perform` would repaint the whole screen every second.
    inspect (action : Unit -> IO M),
    /// Fork `action` as a fiber (never blocks the frame); the loop polls
    /// it every iteration and folds its result message in the moment the
    /// fiber completes. The loop owns the pending handle: fork and poll
    /// happen only there, so the fiber is consumed exactly once. While a
    /// turn this command started is pending, the loop keeps reading
    /// stdin unless the app's `reads_input` yields it to a modal dialog
    /// (see the header). If the fiber has no result -- in practice, the
    /// runtime could not create its thread -- `on_error` turns the reason
    /// into the message folded in instead.
    perform_async (action : Unit -> IO M) (on_error : FiberError -> M)
}

/// An Elm-architecture app: the initial model, how a raw terminal `Event`
/// becomes the app's own message type `M`, the pure step, the view, and
/// the frame clock. `tick_ms` is the poll timeout driving `Event.tick` --
/// 100 is a snappy UI, negative blocks until input (no ticks at all).
///
/// A single-constructor `type`, not a `struct`: parameterized structs do
/// not parse on the current nightly (the plan's own note, and
/// `init/transformers.mo`'s `StateT` header says the same).
pub type App (S : Type) (M : Type) {
    app (init : S)
        (on_event : Event -> M)
        (update : S -> M -> Pair S (Cmd M))
        (view : S -> Widget)
        (tick_ms : I64),
    /// Like `app`, but a tick-only batch draws ONLY when `tick_redraw`
    /// says the state moved (weaver: the spinner while a turn runs). An
    /// idle app then allocates no frames at all -- the immutable screen
    /// copies are the renderer's largest cost. The predicate sees the
    /// state BEFORE the batch folds: a tick whose effect only becomes
    /// visible after folding draws on the following tick.
    ///
    /// `reads_input` decides, once per iteration and only while a fiber
    /// is pending, whether THIS loop may read stdin. Weaver returns false
    /// while a modal dialog on the fiber owns stdin; the app must ack
    /// only after it has stopped drawing (see `produce_for`).
    app_ticked (init : S)
        (on_event : Event -> M)
        (update : S -> M -> Pair S (Cmd M))
        (view : S -> Widget)
        (tick_ms : I64)
        (tick_redraw : S -> Bool)
        (reads_input : S -> IO Bool)
}

/// The app loop. Enters the alternate screen and cbreak, then folds
/// each event batch through `update` and redraws whenever the batch
/// was nonempty (so ticks animate, real keys move, resize reflows).
/// Restores the terminal on quit or EOF -- every exit from `loop_app`
/// lands in the one `restore_terminal` below it.
pub def run_app {S : Type} {M : Type} (a : App S M) : IO Unit := do {
    let size <- Terminal.size;
    let _ <- Terminal.enter_raw_mode;
    Terminal.enter_alt_screen;
    Terminal.cursor_hide;
    Terminal.enable_mouse;
    Terminal.enable_bracketed_paste;
    Terminal.clear_screen;
    Terminal.cursor_move 0 0;
    run_with_size a size
}

/// The loop proper: build the reader from the probed size, fold frames
/// until quit/EOF, then restore. The back buffer starts as a
/// same-sized blank screen: `diff` refuses to diff different-sized
/// screens, so a wrong seed would swallow the first frame.
def run_with_size {S : Type} {M : Type} (a : App S M) (size : Pair I64 I64) : IO Unit :=
    match size {
        Pair.pair rows cols =>
            match a {
                App.app init _ _ vw _ => run_loop a (fn (_ : S) => true) init vw rows cols,
                App.app_ticked init _ _ vw _ redraw _ => run_loop a redraw init vw rows cols,
            }
    }

def run_loop {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (init : S) (vw : S -> Widget) (rows : I64) (cols : I64) : IO Unit := do {
    let reader : InputReader := input_reader rows cols;
    // An initial frame BEFORE the first `Input.produce`: with no ticks
    // (`tick_ms < 0`) the first produce blocks until a key, and the
    // screen stayed blank until then (the recorded UI-repair finding).
    // This draw also flushes run_app's setup writes, which otherwise sat
    // in the stdout buffer behind it.
    let prev <- draw_frame vw init reader (empty_screen rows cols) true false;
    let _ <- loop_app a redraw reader init prev List.empty List.empty;
    restore_terminal
}

/// Whether a batch needs a frame: queued messages and real input always
/// do; a tick-only batch only when the app says the tick moved it.
pub def App.should_draw {S : Type} {M : Type} (redraw : S -> Bool) (model : S) (pending : List M) (evs : List Event) : Bool :=
    if Bool.not (List.length pending < 1) then true
    else if App.has_non_tick evs then true
    else if App.has_tick evs then redraw model
    else false

#[partial]
pub def App.has_non_tick (evs : List Event) : Bool :=
    match evs {
        List.empty => false,
        List.cons e rest => match e {
            Event.tick => App.has_non_tick rest,
            _ => true,
        },
    }

#[partial]
pub def App.has_tick (evs : List Event) : Bool :=
    match evs {
        List.empty => false,
        List.cons e rest => match e {
            Event.tick => true,
            _ => App.has_tick rest,
        },
    }

/// One iteration: poll the pending turn fibers, produce a batch of raw
/// events, lift them to `M`, fold, draw if it was nonempty (or forced),
/// recurse with the dispatched/performed messages as the next batch's
/// prefix and the pending handles still owned here.
/// `#[terminating]`: the loop's progress is the reader's stream, not a
/// structural argument.
#[terminating]
def loop_app {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (reader : InputReader) (model : S) (prev : Screen) (pending : List M) (turns : List (PendingTurn M)) : IO Unit :=
    match a {
        // Explicit `Monad.bind` on the poll (the do-block form's binder
        // is untyped on the self-hosted side, and a
        // polymorphic-`.mo`-def result is exactly where its inference
        // goes wrong -- `poll_turns`'s own comment).
        App.app _ on_ev upd vw tick_ms =>
            loop_body a redraw on_ev upd vw tick_ms (fn (_ : S) => IO.pure true) reader model prev pending turns,
        App.app_ticked _ on_ev upd vw tick_ms _ reads =>
            loop_body a redraw on_ev upd vw tick_ms reads reader model prev pending turns,
    }

#[terminating]
def loop_body {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (on_ev : Event -> M) (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (tick_ms : I64) (reads : S -> IO Bool) (reader : InputReader) (model : S) (prev : Screen) (pending : List M) (turns : List (PendingTurn M)) : IO Unit :=
    Monad.bind (poll_turns turns) (fn (polled : Pair (List M) (List (PendingTurn M))) => do {
        match polled {
            Pair.pair tmsgs turns2 => do {
                // Polling comes BEFORE the produce: with `tick_ms < 0`
                // the produce can block until a key, and the host's poll
                // (which RUNS the deferred action) would then hang behind
                // it.
                let batched : List M := List.append pending tmsgs;
                let out <- produce_for turns2 reader tick_ms model reads;
                after_produce a redraw upd vw on_ev model prev batched turns2 out
            }
        }
    })

/// The cycle's read half. With no pending fiber the loop always reads.
/// While one runs, the app's `reads_input` decides: weaver returns true
/// unless a modal dialog on the fiber owns stdin (it acks from inside
/// that predicate only after its poll marked the overlay open, so its
/// last draw is behind the ack). Declining the read uses
/// `produce_poll_only` -- the frame clock and resizes keep flowing, and
/// the fiber's dialog is the only stdin reader (a second reader would
/// race it and, on a lost wake, block the UI in a blocking read).
def produce_for {S : Type} {M : Type} (turns : List (PendingTurn M)) (reader : InputReader) (timeout_ms : I64) (model : S) (reads : S -> IO Bool) : IO (Pair (List Event) InputReader) := do {
    // The app's read gate is consulted on EVERY iteration, not only
    // while a fiber is pending. A modal dialog opened by a fiber must
    // own stdin even on a loop whose pending-turn bookkeeping is stale
    // (a poll-only cycle keeps the frame clock and resizes flowing
    // without racing the dialog for bytes).
    let may <- reads model;
    if may then Input.produce reader timeout_ms else Input.produce_poll_only reader timeout_ms
}

/// A pending `perform_async`: its fiber and the handler for a fiber
/// error. A one-constructor `type` rather than a `struct` because it is
/// generic over the message type.
type PendingTurn (M : Type) {
    waiting (fiber : Fiber M) (on_error : FiberError -> M)
}

def PendingTurn.fiber {M : Type} (t : PendingTurn M) : Fiber M :=
    match t { PendingTurn.waiting f _ => f }

/// The message a finished turn folds in: its result, or `on_error` of
/// why there is none.
def PendingTurn.message {M : Type} (t : PendingTurn M) (r : Result FiberError M) : M :=
    match r {
        Result.ok m => m,
        Result.err e => match t { PendingTurn.waiting _ on_error => on_error e }
    }

/// Every pending turn fiber, polled once. A fiber that has completed
/// drops from the list and its result message joins the next batch
/// (messages in fork order); one still running stays. Entries never see
/// a cancelled or already-consumed poll: fork, poll and drop live only
/// here and in `continue_step`, and each handle has exactly this one
/// consumer (`pollFiber`) -- that is what keeps the host's eval errors
/// structurally unreachable. `#[terminating]`: recursion on the list
/// tail; a `pollFiber` never waits.
#[terminating]
def poll_turns {M : Type} (turns : List (PendingTurn M)) : IO (Pair (List M) (List (PendingTurn M))) :=
    match turns {
        List.empty => IO.pure (Pair.pair List.empty List.empty),
        List.cons t rest =>
            // Explicit `Monad.bind`, NOT a do-block: this file's binds
            // dispatch `Monad` over the (polymorphic-native) result the
            // self-hosted checker resolves wrongly here -- mock.mo
            // recorded the same failure and the same cure.
            Monad.bind (pollFiber (PendingTurn.fiber t)) (fn (head : Option (Result FiberError M)) =>
                Monad.bind (poll_turns rest) (fn (tail : Pair (List M) (List (PendingTurn M))) =>
                    IO.pure (split_head head t tail)))
    }

/// `poll_turns`'s fold: a completed fiber's message conses in FRONT of
/// the rest's messages (fork order preserved); a running one stays.
#[partial]
def split_head {M : Type} (head : Option (Result FiberError M)) (t : PendingTurn M) (tail : Pair (List M) (List (PendingTurn M))) : Pair (List M) (List (PendingTurn M)) :=
    match tail {
        Pair.pair tmsgs tturns =>
            match head {
                Option.none => Pair.pair tmsgs (List.cons t tturns),
                Option.some r => Pair.pair (List.cons (PendingTurn.message t r) tmsgs) tturns
            }
    }

/// The produce step: a closed reader folds and draws its FINAL batch
/// (a piped script's last keystrokes still count) and then stops -- a
/// controlled exit, `run_with_size` restores after us.
#[terminating]
def after_produce {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (on_ev : Event -> M) (model : S) (prev : Screen) (pending : List M) (turns : List (PendingTurn M)) (out : Pair (List Event) InputReader) : IO Unit :=
    match out {
        Pair.pair evs reader2 =>
            let msgs : List M := List.map on_ev evs in
            let dirty : Bool := App.should_draw redraw model pending evs in
            if reader2.closed
            then final_frame upd vw reader2 model prev pending msgs
            else step_loop a redraw upd vw reader2 model prev turns pending msgs dirty
    }

/// The exit draw: one fold, one frame, no recursion -- the loop is over
/// and any `dispatch`/`perform` commands die with it (there is no next
/// frame). A surviving `perform_async` dies too, unforked: a turn
/// nobody will poll -- and the host never runs a dropped action (fork
/// defers), which makes this exit the CHEAPEST of the two backends.
#[terminating]
def final_frame {S : Type} {M : Type} (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (reader : InputReader) (model : S) (prev : Screen) (pending : List M) (msgs : List M) : IO Unit := do {
    let batch : List M := List.append pending msgs;
    let stepped <- step_batch upd model batch;
    final_draw vw reader prev batch stepped
}

def final_draw {S : Type} {M : Type} (vw : S -> Widget) (reader : InputReader) (prev : Screen) (batch : List M) (stepped : Pair (Pair S (Cmd M)) (Pair (List M) Bool)) : IO Unit :=
    match stepped {
        Pair.pair inner tail => match inner {
            Pair.pair model2 _ => match tail {
                Pair.pair _ forced => do {
                    let frame <- draw_frame vw model2 reader prev (List.length batch > 0) forced;
                    return Unit.unit
                }
            }
        }
    }

/// The batch `step_loop` folds: `pending` (last frame's
/// dispatched/performed messages) in front of the freshly produced ones.
#[terminating]
def step_loop {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (reader : InputReader) (model : S) (prev : Screen) (turns : List (PendingTurn M)) (pending : List M) (msgs : List M) (dirty : Bool) : IO Unit :=
    let batch : List M := List.append pending msgs in
    do {
        let stepped <- step_batch upd model batch;
        after_step a redraw vw reader prev turns batch stepped dirty
    }

/// The fold's continuation: `quit` ends the loop, anything else draws
/// the frame (when the batch was nonempty, or `perform` forced a
/// repaint) and recurses with the queued `dispatch`/`perform` messages.
#[terminating]
def after_step {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (turns : List (PendingTurn M)) (batch : List M) (stepped : Pair (Pair S (Cmd M)) (Pair (List M) Bool)) (dirty : Bool) : IO Unit :=
    match stepped {
        Pair.pair inner tail => continue_step a redraw vw reader prev turns batch inner tail dirty
    }

#[terminating]
def continue_step {S : Type} {M : Type} (a : App S M) (redraw : S -> Bool) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (turns : List (PendingTurn M)) (batch : List M) (inner : Pair S (Cmd M)) (tail : Pair (List M) Bool) (dirty : Bool) : IO Unit :=
    match inner {
        Pair.pair model2 cmd =>
            match cmd {
                Cmd.quit => do { return Unit.unit },
                Cmd.perform_async action on_error =>
                    match tail {
                        Pair.pair pending2 forced => do {
                            // The fork IS this frame's delivery: the
                            // handle joins the loop's pending set, and
                            // the next `loop_app` polls it before it
                            // produces. The handle is consumed exactly
                            // once -- here it is born, in `poll_turns`
                            // it dies.
                            let f <- forkIO action;
                            let frame <- draw_frame vw model2 reader prev dirty forced;
                            loop_app a redraw reader model2 frame pending2 (List.cons (PendingTurn.waiting f on_error) turns)
                        }
                    },
                _ => match tail {
                    Pair.pair pending2 forced => do {
                        let frame <- draw_frame vw model2 reader prev dirty forced;
                        loop_app a redraw reader model2 frame pending2 turns
                    }
                }
            }
    }

/// Fold `update` over the batch: the final model, the surviving command
/// (`quit` short-circuits), the messages the batch's `dispatch`/
/// `perform` commands queued for the next frame, and whether any
/// `perform` fired (which forces the next draw to repaint from blank --
/// see the header comment). `perform` runs real IO, so this (and
/// `step_cmd`) is an `IO` action now, not a pure fold.
def step_batch {S : Type} {M : Type} (upd : S -> M -> Pair S (Cmd M)) (model : S) (msgs : List M) : IO (Pair (Pair S (Cmd M)) (Pair (List M) Bool)) :=
    match msgs {
        List.empty => return (Pair.pair (Pair.pair model Cmd.none) (Pair.pair List.empty false)),
        List.cons m rest =>
            match upd model m {
                Pair.pair model2 cmd => step_cmd upd model2 rest cmd
            }
    }

/// `#[terminating]`: `step_batch` and `step_cmd` are mutually recursive
/// on the tail of the message list.
#[terminating]
def step_cmd {S : Type} {M : Type} (upd : S -> M -> Pair S (Cmd M)) (model : S) (rest : List M) (cmd : Cmd M) : IO (Pair (Pair S (Cmd M)) (Pair (List M) Bool)) :=
    match cmd {
        Cmd.quit => return (Pair.pair (Pair.pair model Cmd.quit) (Pair.pair List.empty false)),
        Cmd.dispatch d => do {
            let stepped <- step_batch upd model rest;
            return (queue_dispatched d stepped)
        },
        Cmd.perform action => do {
            let m2 <- action unit;
            let stepped <- step_batch upd model (List.cons m2 rest);
            return (force_repaint stepped)
        },
        Cmd.inspect action => do {
            let m2 <- action unit;
            step_batch upd model (List.cons m2 rest)
        },
        // Pass-through, not a fork: `step_cmd`'s shape has no room for a
        // fiber handle, and its `rest` has nowhere to go but the
        // unprocessed-message queue. The cmd rides back OUT as this
        // batch's survivor (`continue_step` consumes it there and forks);
        // `rest` re-queues as the next frame's pending, so a SECOND
        // perform_async in the same batch forks, in order, one iteration
        // later.
        Cmd.perform_async action on_error =>
            return (Pair.pair (Pair.pair model (Cmd.perform_async action on_error)) (Pair.pair rest false)),
        Cmd.none => step_batch upd model rest
    }

/// `dispatch`'s queueing: `d` rides in FRONT of whatever the rest of the
/// batch already queued (the same order `step_cmd`'s own recursion
/// produces one message at a time).
def queue_dispatched {S : Type} {M : Type} (d : M) (stepped : Pair (Pair S (Cmd M)) (Pair (List M) Bool)) : Pair (Pair S (Cmd M)) (Pair (List M) Bool) :=
    match stepped {
        Pair.pair inner tail => match tail {
            Pair.pair pend forced => Pair.pair inner (Pair.pair (List.cons d pend) forced)
        }
    }

/// `perform` fired: force the forward flag on, whatever the rest of the
/// batch decided.
def force_repaint {S : Type} {M : Type} (stepped : Pair (Pair S (Cmd M)) (Pair (List M) Bool)) : Pair (Pair S (Cmd M)) (Pair (List M) Bool) :=
    match stepped {
        Pair.pair inner tail => match tail {
            Pair.pair pend _ => Pair.pair inner (Pair.pair pend true)
        }
    }

/// One frame's plan: whether the terminal must be cleared first, and the
/// deltas to write after that. A size change cannot be diffed cell-by-cell
/// (the terminal may have reflowed the old content), so it always clears;
/// a forced repaint of an unchanged size paints from a blank screen model
/// without clearing (the perform that forced it was responsible for its
/// own writes).
pub def frame_plan (prev : Screen) (screen : Screen) (forced : Bool) : Pair Bool (List CellDelta) :=
    let same : Bool := Bool.and (prev.rows == screen.rows) (prev.cols == screen.cols) in
    let clear : Bool := Bool.not same in
    let deltas : List CellDelta :=
        if Bool.or clear forced
        then diff (empty_screen screen.rows screen.cols) screen
        else diff prev screen in
    Pair.pair clear deltas

/// ESC[2J + home: a real erase before repainting at a new geometry.
def clear_before_paint : IO Unit := do {
    Terminal.clear_screen;
    Terminal.cursor_move 0 0
}

/// Render the model into a fresh screen and write the diff against
/// `prev` -- unless the batch was empty AND no `perform` forced a
/// repaint (nothing moved, no write). See `frame_plan` for the clear rule.
def draw_frame {S : Type} (vw : S -> Widget) (model : S) (reader : InputReader) (prev : Screen) (dirty : Bool) (forced : Bool) : IO Screen :=
    if Bool.not dirty && Bool.not forced
    then return prev
    else do {
        let screen : Screen :=
            render (vw model) (mk_rect 0 0 reader.last_cols reader.last_rows)
                (empty_screen reader.last_rows reader.last_cols);
        match frame_plan prev screen forced {
            Pair.pair clear deltas => do {
                let _ <- if clear then clear_before_paint else IO.pure Unit.unit;
                IO.write_stdout (apply_deltas deltas);
                IO.flush_stdout;
                return screen
            }
        }
    }

/// The exit handshake: alternate screen off, cursor back, cooked
/// mode. Every controlled exit lands here; nothing else writes these
/// sequences, so an app cannot half-restore.
def restore_terminal : IO Unit := do {
    // Reset the SGR state FIRST: the app's last frame may have ended on a
    // styled cell (plan mode's status bar is green), and the shell must
    // never inherit it.
    Terminal.reset_style;
    Terminal.disable_bracketed_paste;
    Terminal.disable_mouse;
    Terminal.leave_alt_screen;
    Terminal.cursor_show;
    let _ <- Terminal.leave_raw_mode;
    // The setup/restore writes bypass draw_frame's flush; without this
    // an app that never drew (immediate EOF) would lose its restore.
    IO.flush_stdout;
    return Unit.unit
}
