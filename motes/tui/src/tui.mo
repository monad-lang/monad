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
// 7a.5) landed, and `Cmd.perform_async (action : Unit -> IO M)` is its
// adoption. The action FORKS (`forkIO`); the result folds back whenever the
// loop's `poll_turns` sees the fiber complete -- a frame boundary the
// action's own turn never blocks (weaver's model turn runs on it, and a
// spinner animates while it does). The loop owns every pending handle:
// fork/poll happen only there, and each handle has exactly one consumer
// (poll), which is what keeps the host's "already consumed / cancelled" eval
// errors structurally unreachable. The input consequence is deliberately
// the synchronous loop's: while a turn is pending the loop polls WITHOUT
// reading (produce_poll_only) -- a second stdin reader would both race the
// turn's modal overlay for every byte and, on a lost poll wake, block the
// whole UI in `read_stdin_exact` (a blocking read). Keys typed mid-turn
// buffer in the tty and drain the first normal read after the turn,
// exactly as they did when `perform` blocked the frame.
//
// A `perform` that renders to the real terminal outside this loop's own
// `view`/`render`/`diff` pipeline (an approval overlay is exactly this use
// case) leaves `prev` stale: the next diff would compare the model's
// screen against a `prev` that no longer matches what is actually on the
// terminal, and could leave stray pixels behind. `step_batch`/`step_cmd`
// thread a `forced : Bool` alongside the model and the queued messages, set
// whenever ANY `perform` fired during that batch's fold, and `draw_frame`
// treats `forced` exactly like a resize: repaint from a blank screen
// instead of diffing against `prev`.
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
    Terminal.leave_raw_mode, Terminal.size
}
use std::concurrent::fiber {Fiber, forkIO, pollFiber}
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
    /// Fork `action` as a fiber (never blocks the frame); the loop polls
    /// it every iteration and folds its result message in the moment the
    /// fiber completes. The loop owns the pending handle: fork and poll
    /// happen only there, so the fiber is consumed exactly once. While a
    /// turn this command started is pending, the loop polls stdin
    /// WITHOUT reading (see the header) -- mid-turn keys buffer until
    /// the turn completes, exactly as in the synchronous `perform`.
    perform_async (action : Unit -> IO M)
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
        (tick_ms : I64)
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
                App.app init _ _ vw _ => do {
                    let reader : InputReader := input_reader rows cols;
                    // An initial frame BEFORE the first `Input.produce`:
                    // with no ticks (`tick_ms < 0`) the first produce
                    // blocks until a key, and the screen stayed blank
                    // until then (the recorded UI-repair finding). This
                    // draw also flushes run_app's setup writes, which
                    // otherwise sat in the stdout buffer behind it.
                    let prev <- draw_frame vw init reader (empty_screen rows cols) true false;
                    let _ <- loop_app a reader init prev List.empty List.empty;
                    restore_terminal
                }
            }
    }

/// One iteration: poll the pending turn fibers, produce a batch of raw
/// events, lift them to `M`, fold, draw if it was nonempty (or forced),
/// recurse with the dispatched/performed messages as the next batch's
/// prefix and the pending handles still owned here.
/// `#[terminating]`: the loop's progress is the reader's stream, not a
/// structural argument.
#[terminating]
def loop_app {S : Type} {M : Type} (a : App S M) (reader : InputReader) (model : S) (prev : Screen) (pending : List M) (turns : List (Fiber M)) : IO Unit :=
    match a {
        // Explicit `Monad.bind` on the poll (the do-block form's binder
        // is untyped on the self-hosted side, and a
        // polymorphic-`.mo`-def result is exactly where its inference
        // goes wrong -- `poll_turns`'s own comment).
        App.app _ on_ev upd vw tick_ms =>
            Monad.bind (poll_turns turns) (fn (polled : Pair (List M) (List (Fiber M))) => do {
                match polled {
                    Pair.pair tmsgs turns2 => do {
                        // Polling comes BEFORE the produce: with
                        // `tick_ms < 0` the produce can block until a
                        // key, and the host's poll (which RUNS the
                        // deferred action) would then hang behind it.
                        let batched : List M := List.append pending tmsgs;
                        let out <- produce_for turns2 reader tick_ms;
                        after_produce a upd vw on_ev model prev batched turns2 out
                    }
                }
            })
    }

/// The cycle's read half, decided by the turn state: `produce` normally,
/// `produce_poll_only` while a turn is pending (tui.mo's header carries
/// the whole reason -- a second stdin reader would race the turn's modal
/// overlay and block the UI on a lost wake).
def produce_for {M : Type} (turns : List (Fiber M)) (reader : InputReader) (timeout_ms : I64) : IO (Pair (List Event) InputReader) :=
    match turns {
        List.empty => Input.produce reader timeout_ms,
        List.cons _ _ => Input.produce_poll_only reader timeout_ms
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
def poll_turns {M : Type} (turns : List (Fiber M)) : IO (Pair (List M) (List (Fiber M))) :=
    match turns {
        List.empty => IO.pure (Pair.pair List.empty List.empty),
        List.cons f rest =>
            // Explicit `Monad.bind`, NOT a do-block: this file's binds
            // dispatch `Monad` over the (polymorphic-native) result the
            // self-hosted checker resolves wrongly here -- mock.mo
            // recorded the same failure and the same cure.
            Monad.bind (pollFiber f) (fn (head : Option M) =>
                Monad.bind (poll_turns rest) (fn (tail : Pair (List M) (List (Fiber M))) =>
                    IO.pure (split_head head f tail)))
    }

/// `poll_turns`'s fold: a completed fiber's message conses in FRONT of
/// the rest's messages (fork order preserved); a running one stays.
#[partial]
def split_head {M : Type} (head : Option M) (f : Fiber M) (tail : Pair (List M) (List (Fiber M))) : Pair (List M) (List (Fiber M)) :=
    match tail {
        Pair.pair tmsgs tturns =>
            match head {
                Option.none => Pair.pair tmsgs (List.cons f tturns),
                Option.some m => Pair.pair (List.cons m tmsgs) tturns
            }
    }

/// The produce step: a closed reader folds and draws its FINAL batch
/// (a piped script's last keystrokes still count) and then stops -- a
/// controlled exit, `run_with_size` restores after us.
#[terminating]
def after_produce {S : Type} {M : Type} (a : App S M) (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (on_ev : Event -> M) (model : S) (prev : Screen) (pending : List M) (turns : List (Fiber M)) (out : Pair (List Event) InputReader) : IO Unit :=
    match out {
        Pair.pair evs reader2 =>
            let msgs : List M := List.map on_ev evs in
            if reader2.closed
            then final_frame upd vw reader2 model prev pending msgs
            else step_loop a upd vw reader2 model prev turns pending msgs
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
def step_loop {S : Type} {M : Type} (a : App S M) (upd : S -> M -> Pair S (Cmd M)) (vw : S -> Widget) (reader : InputReader) (model : S) (prev : Screen) (turns : List (Fiber M)) (pending : List M) (msgs : List M) : IO Unit :=
    let batch : List M := List.append pending msgs in
    do {
        let stepped <- step_batch upd model batch;
        after_step a vw reader prev turns batch stepped
    }

/// The fold's continuation: `quit` ends the loop, anything else draws
/// the frame (when the batch was nonempty, or `perform` forced a
/// repaint) and recurses with the queued `dispatch`/`perform` messages.
#[terminating]
def after_step {S : Type} {M : Type} (a : App S M) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (turns : List (Fiber M)) (batch : List M) (stepped : Pair (Pair S (Cmd M)) (Pair (List M) Bool)) : IO Unit :=
    match stepped {
        Pair.pair inner tail => continue_step a vw reader prev turns batch inner tail
    }

#[terminating]
def continue_step {S : Type} {M : Type} (a : App S M) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (turns : List (Fiber M)) (batch : List M) (inner : Pair S (Cmd M)) (tail : Pair (List M) Bool) : IO Unit :=
    match inner {
        Pair.pair model2 cmd =>
            match cmd {
                Cmd.quit => do { return Unit.unit },
                Cmd.perform_async action =>
                    match tail {
                        Pair.pair pending2 forced => do {
                            // The fork IS this frame's delivery: the
                            // handle joins the loop's pending set, and
                            // the next `loop_app` polls it before it
                            // produces. The handle is consumed exactly
                            // once -- here it is born, in `poll_turns`
                            // it dies.
                            let f <- forkIO action;
                            let frame <- draw_frame vw model2 reader prev (List.length batch > 0) forced;
                            loop_app a reader model2 frame pending2 (List.cons f turns)
                        }
                    },
                _ => match tail {
                    Pair.pair pending2 forced => do {
                        let frame <- draw_frame vw model2 reader prev (List.length batch > 0) forced;
                        loop_app a reader model2 frame pending2 turns
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
        // Pass-through, not a fork: `step_cmd`'s shape has no room for a
        // fiber handle, and its `rest` has nowhere to go but the
        // unprocessed-message queue. The cmd rides back OUT as this
        // batch's survivor (`continue_step` consumes it there and forks);
        // `rest` re-queues as the next frame's pending, so a SECOND
        // perform_async in the same batch forks, in order, one iteration
        // later.
        Cmd.perform_async action =>
            return (Pair.pair (Pair.pair model (Cmd.perform_async action)) (Pair.pair rest false)),
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

/// Render the model into a fresh screen and write the diff against
/// `prev` -- unless the batch was empty AND no `perform` forced a
/// repaint (nothing moved, no write). `diff` refuses different-sized
/// screens, so a RESIZE frame (or a forced one) repaints instead: every
/// non-blank cell against a fresh blank screen of the new size (the alt
/// screen is already blank, so blank cells emit nothing and the repaint
/// is as cheap as a diff).
def draw_frame {S : Type} (vw : S -> Widget) (model : S) (reader : InputReader) (prev : Screen) (dirty : Bool) (forced : Bool) : IO Screen :=
    if Bool.not dirty && Bool.not forced
    then return prev
    else do {
        let screen : Screen :=
            render (vw model) (mk_rect 0 0 reader.last_cols reader.last_rows)
                (empty_screen reader.last_rows reader.last_cols);
        let deltas : List CellDelta :=
            if Bool.not forced && prev.rows == screen.rows && prev.cols == screen.cols
            then diff prev screen
            else diff (empty_screen screen.rows screen.cols) screen;
        IO.write_stdout (apply_deltas deltas);
        IO.flush_stdout;
        return screen
    }

/// The exit handshake: alternate screen off, cursor back, cooked
/// mode. Every controlled exit lands here; nothing else writes these
/// sequences, so an app cannot half-restore.
def restore_terminal : IO Unit := do {
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
