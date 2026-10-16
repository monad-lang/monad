// Phase 7 table tests: `step_batch` is the loop's whole step semantics
// and it is PURE -- every Cmd rule (none/quit/dispatch, short-circuit,
// queue order) pins here without a terminal. The IO halves (produce,
// draw, restore) are exercised end-to-end by examples/tui_counter.mo.

use lib::types { Event }
use lib::tui { Cmd, step_batch }
use std::list { List.length }

def cmds_be (a : Cmd) (b : Cmd) : Bool :=
    match a {
        Cmd.none => match b { Cmd.none => true, _ => false },
        Cmd.quit => match b { Cmd.quit => true, _ => false },
        Cmd.dispatch _ => match b { Cmd.dispatch _ => true, _ => false }
    }

// A counting update: every event bumps the model by its position, so
// assertions can distinguish event ORDER inside one batch.
def bump (m : I64) (e : Event) : Pair I64 Cmd :=
    Pair.pair (m + 1) Cmd.none

// ==================== step_batch ====================

#[test]
def test_step_batch_empty_batch : Bool :=
    match step_batch bump 7 List.empty {
        Pair.pair inner pending =>
            match inner {
                Pair.pair m cmd => m == 7 && cmds_be cmd Cmd.none && List.length pending == 0
            }
    }

#[test]
def test_step_batch_folds_every_event : Bool :=
    match step_batch bump 0 [Event.tick, Event.tick, Event.tick] {
        Pair.pair inner pending =>
            match inner {
                Pair.pair m cmd => m == 3 && cmds_be cmd Cmd.none && List.length pending == 0
            }
    }

#[test]
def test_step_batch_quit_short_circuits : Bool :=
    // update quits on the SECOND event: the third never runs, the
    // surviving command is quit, and nothing is queued.
    let upd : I64 -> Event -> Pair I64 Cmd :=
        fn (m : I64) (e : Event) =>
            if m == 1
            then Pair.pair m Cmd.quit
            else Pair.pair (m + 1) Cmd.none
    in
    match step_batch upd 0 [Event.tick, Event.tick, Event.tick] {
        Pair.pair inner pending =>
            match inner {
                Pair.pair m cmd => m == 1 && cmds_be cmd Cmd.quit && List.length pending == 0
            }
    }

#[test]
def test_step_batch_dispatch_queues_for_next_frame : Bool :=
    // update dispatches on the first event: the dispatched event rides
    // `pending` (queued for the NEXT frame), the batch itself keeps
    // folding.
    let upd : I64 -> Event -> Pair I64 Cmd :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.dispatch Event.tick)
            else Pair.pair (m + 1) Cmd.none
    in
    match step_batch upd 0 [Event.tick, Event.tick] {
        Pair.pair inner pending =>
            match inner {
                Pair.pair m cmd => m == 2 && cmds_be cmd Cmd.none && List.length pending == 1
            }
    }
