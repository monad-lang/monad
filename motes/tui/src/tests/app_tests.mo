// Phase 7 table tests: `step_batch` is the loop's whole step semantics.
// It became an `IO` action in v2 (`Cmd.perform` runs real IO inline), so
// every test here binds through it rather than matching a pure value --
// the fold itself (none/quit/dispatch/perform, short-circuit, queue
// order, the forced-repaint flag) still pins without a terminal. The
// IO halves (produce, draw, restore) are exercised end-to-end by
// examples/tui_counter.mo.

use lib::types { Event }
use lib::tui { Cmd, step_batch }
use std::list { List.length }

def cmds_be {M : Type} (a : Cmd M) (b : Cmd M) : Bool :=
    match a {
        Cmd.none => match b { Cmd.none => true, _ => false },
        Cmd.quit => match b { Cmd.quit => true, _ => false },
        Cmd.dispatch _ => match b { Cmd.dispatch _ => true, _ => false },
        Cmd.perform _ => match b { Cmd.perform _ => true, _ => false }
    }

/// The two-level result `step_batch` returns: `((model, cmd), (pending,
/// forced))`. Unpacked once here so every test reads the four parts by
/// name instead of re-deriving the nesting.
struct Stepped {
    model : I64,
    cmd : Cmd Event,
    pending : List Event,
    forced : Bool,
}

def unpack (r : Pair (Pair I64 (Cmd Event)) (Pair (List Event) Bool)) : Stepped :=
    match r {
        Pair.pair inner tail => match inner {
            Pair.pair m cmd => match tail {
                Pair.pair pending forced =>
                    { model := m, cmd := cmd, pending := pending, forced := forced }
            }
        }
    }

// A counting update: every event bumps the model by its position, so
// assertions can distinguish event ORDER inside one batch.
def bump (m : I64) (e : Event) : Pair I64 (Cmd Event) :=
    Pair.pair (m + 1) Cmd.none

// ==================== step_batch ====================

#[test]
def test_step_batch_empty_batch : IO Bool := do {
    let r <- step_batch bump 7 List.empty;
    let s := unpack r;
    return (s.model == 7 && cmds_be s.cmd Cmd.none && List.length s.pending == 0 && Bool.not s.forced)
}

#[test]
def test_step_batch_folds_every_event : IO Bool := do {
    let r <- step_batch bump 0 [Event.tick, Event.tick, Event.tick];
    let s := unpack r;
    return (s.model == 3 && cmds_be s.cmd Cmd.none && List.length s.pending == 0 && Bool.not s.forced)
}

#[test]
def test_step_batch_quit_short_circuits : IO Bool := do {
    // update quits on the SECOND event: the third never runs, the
    // surviving command is quit, and nothing is queued.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 1
            then Pair.pair m Cmd.quit
            else Pair.pair (m + 1) Cmd.none;
    let r <- step_batch upd 0 [Event.tick, Event.tick, Event.tick];
    let s := unpack r;
    return (s.model == 1 && cmds_be s.cmd Cmd.quit && List.length s.pending == 0 && Bool.not s.forced)
}

#[test]
def test_step_batch_dispatch_queues_for_next_frame : IO Bool := do {
    // update dispatches on the first event: the dispatched event rides
    // `pending` (queued for the NEXT frame), the batch itself keeps
    // folding.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.dispatch Event.tick)
            else Pair.pair (m + 1) Cmd.none;
    let r <- step_batch upd 0 [Event.tick, Event.tick];
    let s := unpack r;
    return (s.model == 2 && cmds_be s.cmd Cmd.none && List.length s.pending == 1 && Bool.not s.forced)
}

// ==================== step_batch: perform ====================

#[test]
def test_step_batch_perform_runs_io_and_folds_result : IO Bool := do {
    // update performs on the first event: the action's IO runs inline
    // and ITS result (tick) folds into the SAME batch (model ends at 2,
    // not 1), unlike dispatch which only queues for next frame.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.perform (fn (_ : Unit) => IO.pure Event.tick))
            else Pair.pair (m + 1) Cmd.none;
    let r <- step_batch upd 0 [Event.tick];
    let s := unpack r;
    return (s.model == 2 && cmds_be s.cmd Cmd.none && List.length s.pending == 0)
}

#[test]
def test_step_batch_perform_forces_repaint : IO Bool := do {
    // `perform` only on the first event (never on its own folded-back
    // result) -- an unconditional perform would recurse forever, since
    // its result message re-enters the very same batch.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.perform (fn (_ : Unit) => IO.pure Event.tick))
            else Pair.pair (m + 1) Cmd.none;
    let r <- step_batch upd 0 [Event.tick];
    let s := unpack r;
    return s.forced
}

#[test]
def test_step_batch_no_perform_does_not_force_repaint : IO Bool := do {
    let r <- step_batch bump 0 [Event.tick];
    let s := unpack r;
    return (Bool.not s.forced)
}

#[test]
def test_step_batch_dispatch_after_perform_keeps_forced : IO Bool := do {
    // A perform's folded-back result re-enters the SAME batch, so one
    // perform plus two real events yields three dispatches queued
    // (one per step after the first), and the forced flag survives
    // being combined with later plain dispatches.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.perform (fn (_ : Unit) => IO.pure Event.tick))
            else Pair.pair (m + 1) (Cmd.dispatch Event.tick);
    let r <- step_batch upd 0 [Event.tick, Event.tick];
    let s := unpack r;
    return (s.forced && List.length s.pending == 2)
}
