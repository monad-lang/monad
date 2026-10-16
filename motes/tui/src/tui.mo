// Terminal UI Library - the application loop (Phase 7)
//
// `run_app` is the Elm-architecture entry point: the app is a record
// of `init`/`update`/`view` plus a frame clock, and the loop wires
// the pull reader (input.mo), the fold semantics (frp.mo pins them)
// and the renderer (render.mo) around it. One loop, one write per
// changed model:
//
//   Input.produce (poll/read/decode + resize + tick)  ->  List Event
//   fold update over the model (dispatch -> next frame)  ->  S * Cmd
//   view -> render -> diff -> apply_deltas  ->  one stdout write
//
// `Cmd` is the only side-channel: `update` returns commands rather
// than performing them, and `dispatch` re-enters the event list one
// frame later -- the same step semantics `EventStream.fold`
// table-tests.
//
// v1 shape deviations from the plan's sketch, recorded here so they
// are decisions, not drift:
//   * `update` is PURE (`S -> Event -> Pair S Cmd`), not
//     `TuiT M Raw Raw (S * Cmd)` -- the transformer (Phase 10) lifts
//     this loop's halves; the pure update is the 90% case the plan
//     says the App record is for.
//   * `tick_ms` is a field of `App`: a frame clock has to live
//     somewhere, and negative = block until input, no ticks.
//   * `run_frp` is deferred: the cold FRP core deliberately has no
//     live signals, and `run_app` IS the live composition point.
//   * Panic recovery is the honest v1 version: the terminal is
//     restored on every CONTROLLED exit (quit, EOF). A hard crash
//     still strands the alt screen -- unwinding through the restore
//     path needs the error-effect story (Phase 10's ResultT stack).
//
// `Cmd`'s `beep`/`set_clipboard`/`open_url` from the plan's sketch
// need natives that do not exist yet; they stay unimplemented rather
// than stubbed.

use lib::types { CellDelta, Event, Screen }
use lib::core { empty_screen, mk_rect }
use lib::render { apply_deltas, diff, render }
use lib::widget { Widget }
use lib::input { Input.produce, InputReader, input_reader }
use lib::terminal {
    Terminal.clear_screen, Terminal.cursor_hide, Terminal.cursor_move, Terminal.cursor_show,
    Terminal.enter_alt_screen, Terminal.enter_raw_mode, Terminal.leave_alt_screen,
    Terminal.leave_raw_mode, Terminal.size
}
use std::io { IO.flush_stdout, IO.write_stdout }
use std::list { List.length }

/// Commands `update` returns instead of performing. `none` is the
/// ordinary case, `quit` stops the loop (the terminal is restored),
/// `dispatch` injects an event into the NEXT frame's batch.
pub type Cmd {
    /// Nothing to do.
    none,
    /// Stop the app; the terminal is restored.
    quit,
    /// Inject `event` into the next frame's event batch.
    dispatch (event : Event)
}

/// An Elm-architecture app: the initial model, the pure step, the
/// view, and the frame clock. `tick_ms` is the poll timeout driving
/// `Event.tick` -- 100 is a snappy UI, negative blocks until input
/// (no ticks at all).
///
/// A single-constructor `type`, not a `struct`: parameterized structs
/// do not parse on the current nightly (the plan's own note, and
/// `init/transformers.mo`'s `StateT` header says the same).
pub type App (S : Type) {
    app (init : S)
        (update : S -> Event -> Pair S Cmd)
        (view : S -> Widget)
        (tick_ms : I64)
}

/// The app loop. Enters the alternate screen and cbreak, then folds
/// each event batch through `update` and redraws whenever the batch
/// was nonempty (so ticks animate, real keys move, resize reflows).
/// Restores the terminal on quit or EOF -- every exit from `loop_app`
/// lands in the one `restore_terminal` below it.
///
/// An `update` whose dispatched events dispatch again loops forever --
/// the fold step is the app's own responsibility, the same deal
/// `EventStream.fold` gives the cold path.
pub def run_app {S : Type} (a : App S) : IO Unit := do {
    let size <- Terminal.size;
    let _ <- Terminal.enter_raw_mode;
    Terminal.enter_alt_screen;
    Terminal.cursor_hide;
    Terminal.clear_screen;
    Terminal.cursor_move 0 0;
    run_with_size a size
}

/// The loop proper: build the reader from the probed size, fold frames
/// until quit/EOF, then restore. The back buffer starts as a
/// same-sized blank screen: `diff` refuses to diff different-sized
/// screens, so a wrong seed would swallow the first frame.
def run_with_size {S : Type} (a : App S) (size : Pair I64 I64) : IO Unit :=
    match size {
        Pair.pair rows cols => do {
            let reader : InputReader := input_reader rows cols;
            let _ <- loop_app a reader a.init (empty_screen rows cols) List.empty;
            restore_terminal
        }
    }

/// One iteration: produce a batch, fold it, draw if it was nonempty,
/// recurse with the dispatched events as the next batch's prefix.
/// `#[terminating]`: the loop's progress is the reader's stream, not
/// a structural argument.
#[terminating]
def loop_app {S : Type} (a : App S) (reader : InputReader) (model : S) (prev : Screen) (pending : List Event) : IO Unit :=
    match a {
        App.app _ upd vw tick_ms => do {
            let out <- Input.produce reader tick_ms;
            after_produce a upd vw model prev pending out
        }
    }

/// The produce step: a closed reader folds and draws its FINAL batch
/// (a piped script's last keystrokes still count) and then stops -- a
/// controlled exit, `run_with_size` restores after us.
#[terminating]
def after_produce {S : Type} (a : App S) (upd : S -> Event -> Pair S Cmd) (vw : S -> Widget) (model : S) (prev : Screen) (pending : List Event) (out : Pair (List Event) InputReader) : IO Unit :=
    match out {
        Pair.pair evs reader2 => do {
            if reader2.closed
            then final_frame upd vw reader2 model prev pending evs
            else step_loop a upd vw reader2 model prev pending evs
        }
    }

/// The exit draw: one fold, one frame, no recursion -- the loop is over
/// and any `dispatch` commands die with it (there is no next frame).
#[terminating]
def final_frame {S : Type} (upd : S -> Event -> Pair S Cmd) (vw : S -> Widget) (reader : InputReader) (model : S) (prev : Screen) (pending : List Event) (evs : List Event) : IO Unit :=
    let batch : List Event := List.append pending evs in
    match step_batch upd model batch {
        Pair.pair inner _ =>
            match inner {
                Pair.pair model2 _ => do {
                    let frame <- draw_frame vw model2 reader prev (List.length batch > 0);
                    return Unit.unit
                }
            }
    }

/// The batch `step_loop` folds: `pending` (last frame's dispatched
/// events) in front of the freshly produced ones.
#[terminating]
def step_loop {S : Type} (a : App S) (upd : S -> Event -> Pair S Cmd) (vw : S -> Widget) (reader : InputReader) (model : S) (prev : Screen) (pending : List Event) (evs : List Event) : IO Unit :=
    let batch : List Event := List.append pending evs in
    after_step a vw reader prev batch (step_batch upd model batch)

/// The fold's continuation: `quit` ends the loop, anything else draws
/// the frame (when the batch was nonempty) and recurses with the
/// queued `dispatch` events.
#[terminating]
def after_step {S : Type} (a : App S) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (batch : List Event) (stepped : Pair (Pair S Cmd) (List Event)) : IO Unit :=
    match stepped {
        Pair.pair inner pending2 => continue_step a vw reader prev batch inner pending2
    }

#[terminating]
def continue_step {S : Type} (a : App S) (vw : S -> Widget) (reader : InputReader) (prev : Screen) (batch : List Event) (inner : Pair S Cmd) (pending2 : List Event) : IO Unit :=
    match inner {
        Pair.pair model2 cmd =>
            match cmd {
                Cmd.quit => do { return Unit.unit },
                _ => do {
                    let frame <- draw_frame vw model2 reader prev (List.length batch > 0);
                    loop_app a reader model2 frame pending2
                }
            }
    }

/// Fold `update` over the batch: the final model, the surviving
/// command (`quit` short-circuits), and the events the batch's
/// `dispatch` commands queued for the next frame.
def step_batch {S : Type} (upd : S -> Event -> Pair S Cmd) (model : S) (evs : List Event) : Pair (Pair S Cmd) (List Event) :=
    match evs {
        empty => Pair.pair (Pair.pair model Cmd.none) List.empty,
        cons e rest =>
            match upd model e {
                Pair.pair model2 cmd => step_cmd upd model2 rest cmd
            }
    }

/// `#[terminating]`: `step_batch` and `step_cmd` are mutually recursive
/// on the tail of the event list.
#[terminating]
def step_cmd {S : Type} (upd : S -> Event -> Pair S Cmd) (model : S) (rest : List Event) (cmd : Cmd) : Pair (Pair S Cmd) (List Event) :=
    match cmd {
        Cmd.quit => Pair.pair (Pair.pair model Cmd.quit) List.empty,
        Cmd.dispatch d =>
            match step_batch upd model rest {
                Pair.pair inner p3 =>
                    match inner {
                        Pair.pair model3 cmd3 =>
                            Pair.pair (Pair.pair model3 cmd3) (List.cons d p3)
                    }
            },
        Cmd.none => step_batch upd model rest
    }

/// Render the model into a fresh screen and write the diff against
/// `prev` -- unless the batch was empty (nothing moved, no write).
/// `diff` refuses different-sized screens, so a RESIZE frame repaints
/// instead: every non-blank cell against a fresh blank screen of the
/// new size (the alt screen is already blank, so blank cells emit
/// nothing and the repaint is as cheap as a diff).
def draw_frame {S : Type} (vw : S -> Widget) (model : S) (reader : InputReader) (prev : Screen) (dirty : Bool) : IO Screen :=
    if Bool.not dirty
    then return prev
    else do {
        let screen : Screen :=
            render (vw model) (mk_rect 0 0 reader.last_cols reader.last_rows)
                (empty_screen reader.last_rows reader.last_cols);
        let deltas : List CellDelta :=
            if prev.rows == screen.rows && prev.cols == screen.cols
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
    Terminal.leave_alt_screen;
    Terminal.cursor_show;
    let _ <- Terminal.leave_raw_mode;
    // The setup/restore writes bypass draw_frame's flush; without this
    // an app that never drew (immediate EOF) would lose its restore.
    IO.flush_stdout;
    return Unit.unit
}
