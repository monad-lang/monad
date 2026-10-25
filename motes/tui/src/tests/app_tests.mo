// Phase 7 table tests: `step_batch` is the loop's whole step semantics.
// It became an `IO` action in v2 (`Cmd.perform` runs real IO inline), so
// every test here binds through it rather than matching a pure value --
// the fold itself (none/quit/dispatch/perform, short-circuit, queue
// order, the forced-repaint flag) still pins without a terminal. The
// IO halves (produce, draw, restore) are exercised end-to-end by
// examples/tui_counter.mo.

use lib::types { Event, Key }
use lib::core { mk_screen }
use lib::tui { App, Cmd, PendingTurn, poll_turns, step_batch, frame_plan }
use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, forkIO}
use std::ref {Ref, Ref.get, Ref.new, Ref.set}
use std::list { List.length }

def cmds_be {M : Type} (a : Cmd M) (b : Cmd M) : Bool :=
    match a {
        Cmd.none => match b { Cmd.none => true, _ => false },
        Cmd.quit => match b { Cmd.quit => true, _ => false },
        Cmd.dispatch _ => match b { Cmd.dispatch _ => true, _ => false },
        Cmd.perform _ => match b { Cmd.perform _ => true, _ => false },
        Cmd.inspect _ => match b { Cmd.inspect _ => true, _ => false },
        // NOTE: every future Cmd variant needs an arm here -- this match
        // is exhaustive on purpose, so a new variant cannot slip through
        // the table tests silently.
        Cmd.perform_async _ _ => match b { Cmd.perform_async _ _ => true, _ => false }
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

// poll_turns helpers: actions slow enough that "running" and "completed"
// states are deterministic from the caller's side. A turn's error message
// is -1, which no action here returns.
def turn (f : Fiber I64) : PendingTurn I64 := PendingTurn.waiting f (fn (_ : FiberError) => -1)

def slow_zero_action (_ : Unit) : IO I64 := do {
    sleepIO 300;
    IO.pure 0
}

def slow_one_action (_ : Unit) : IO I64 := do {
    sleepIO 300;
    IO.pure 1
}

def slow_two_action (_ : Unit) : IO I64 := do {
    sleepIO 300;
    IO.pure 2
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

// ==================== step_batch: perform_async ====================

#[test]
def test_step_batch_perform_async_is_a_pass_through : IO Bool := do {
    // update performs-async on the first event: NOTHING runs here and
    // nothing forces a repaint -- the cmd survives as the batch's
    // survivor (`continue_step` forks it), and the UNPROCESSED rest
    // re-queues as the next frame's pending. The model advanced once
    // (the one message was consumed), the other two are pending.
    let upd : I64 -> Event -> Pair I64 (Cmd Event) :=
        fn (m : I64) (e : Event) =>
            if m == 0
            then Pair.pair (m + 1) (Cmd.perform_async (fn (_ : Unit) => IO.pure Event.tick) (fn (_ : FiberError) => Event.tick))
            else Pair.pair (m + 1) Cmd.none;
    let r <- step_batch upd 0 [Event.tick, Event.tick, Event.tick];
    let s := unpack r;
    return (s.model == 1 && cmds_be s.cmd (Cmd.perform_async (fn (_ : Unit) => IO.pure Event.tick) (fn (_ : FiberError) => Event.tick)) && List.length s.pending == 2 && Bool.not s.forced)
}

// ==================== poll_turns ====================
// The turn-fiber polls: `test_poll_turns_completed_fiber_drains` is
// runner-agnostic (poll until a known-complete fiber answers -- the lazy
// host runs the action inside the poll and both backends agree), while
// `test_poll_turns_running_fiber_stays` pins the RUNNING case and so only
// a concurrent implementation can pass it (an await-shaped poll would
// block or answer `some`) -- the combine_test.mo convention.

#[test]
def test_poll_turns_completed_fiber_drains : IO Bool := do {
    let f <- forkIO slow_zero_action;
    sleepIO 700;
    let r <- poll_turns [turn f];
    return (list_shape_be r 1 0)
}

#[test]
def test_poll_turns_running_fiber_stays : IO Bool := do {
    let f <- forkIO slow_zero_action;
    // Poll immediately: the fiber sleeps far longer than this line needs.
    let r <- poll_turns [turn f];
    return (list_shape_be r 0 1)
}

#[test]
def test_poll_turns_drains_in_fork_order : IO Bool := do {
    let f1 <- forkIO slow_one_action;
    let f2 <- forkIO slow_two_action;
    sleepIO 700;
    let r <- poll_turns [turn f1, turn f2];
    return (ordered_pair r)
}

/// A turn whose fiber has no result folds in its `on_error` message
/// instead. Cancelling forces the error on both backends: the compiled
/// fiber is still sleeping, and the host has not run it.
#[test]
def test_poll_turns_error_folds_on_error : IO Bool := do {
    let f <- forkIO slow_zero_action;
    cancel_fiber f;
    sleepIO 700;
    let r <- poll_turns [turn f];
    return (match r {
        Pair.pair msgs rest => match msgs {
            List.cons m _ => I64.beq m (-1) && List.length rest == 0,
            List.empty => false
        }
    })
}

// Unpacked once: `((msgs), (rest))` shapes asserted by counts, so the
// tests read the poll's two halves without unpacking boilerplate.
def list_shape_be (r : Pair (List I64) (List (PendingTurn I64))) (n_msgs : I64) (n_rest : I64) : Bool :=
    match r {
        Pair.pair msgs rest => (List.length msgs == n_msgs && List.length rest == n_rest)
    }

def ordered_pair (r : Pair (List I64) (List (PendingTurn I64))) : Bool :=
    match r {
        Pair.pair msgs rest =>
            match msgs {
                List.empty => false,
                List.cons a tail =>
                    match tail {
                        List.empty => false,
                        // I64.beq explicitly: the projection-vs-`==`
                        // binding looseness recorded from the UI pass
                        // makes an unparenthesized `==`-chain ambiguous.
                        List.cons b _ => (I64.beq a 1 && I64.beq b 2 && List.length rest == 0)
                    }
            }
    }

// ── the idle-tick draw rule (`App.app_ticked`) ────────────────────────

#[test]
def test_idle_tick_does_not_draw_for_a_static_app : Bool :=
    Bool.not (App.should_draw (fn (_ : I64) => false) 0 List.empty [Event.tick])

#[test]
def test_animated_tick_draws : Bool :=
    App.should_draw (fn (_ : I64) => true) 0 List.empty [Event.tick]

#[test]
def test_a_real_event_always_draws : Bool :=
    App.should_draw (fn (_ : I64) => false) 0 List.empty [Event.key (Key.char "a")]

#[test]
def test_a_queued_message_always_draws : Bool :=
    App.should_draw (fn (_ : I64) => false) 0 [1] List.empty

// ── frame_plan: clear on geometry change ──────────────────────────────

#[test]
def test_frame_plan_same_size_diffs_without_clearing : Bool :=
    match frame_plan (mk_screen 1 2) (mk_screen 1 2) false {
        Pair.pair clear deltas => clear == false && List.is_empty deltas,
    }

#[test]
def test_frame_plan_growing_width_clears : Bool :=
    match frame_plan (mk_screen 1 2) (mk_screen 1 3) false {
        Pair.pair clear _ => clear == true,
    }

#[test]
def test_frame_plan_shrinking_height_clears : Bool :=
    match frame_plan (mk_screen 3 2) (mk_screen 2 2) false {
        Pair.pair clear _ => clear == true,
    }

#[test]
def test_frame_plan_forced_same_size_does_not_clear : Bool :=
    match frame_plan (mk_screen 1 2) (mk_screen 1 2) true {
        Pair.pair clear _ => clear == false,
    }

// ── fiber result delivery (regression) ───────────────────────────────
// The compiled backend once answered a COMPLETED fiber with a garbage
// `err cancelled` (or segfaulted in `monad_get_tag` while matching the
// native Result). These pin the primitive the TUI's async turns build on.

#[test]
def test_await_fiber_returns_the_action_result : IO Bool := do {
    let f <- forkIO (fn (_ : Unit) => IO.pure 7i64);
    let r <- await_fiber f;
    match r {
        Result.ok n => IO.pure (n == 7i64),
        Result.err _ => IO.pure false,
    }
}

/// A `Ref` created and used INSIDE a fiber (the usage tracker's original
/// shape) must round-trip through the fiber's result.
#[test]
def test_ref_round_trip_inside_a_fiber : IO Bool := do {
    let f <- forkIO (fn (_ : Unit) => do {
        let r <- Ref.new 1i64;
        let _ <- Ref.set r 2i64;
        Ref.get r
    });
    let res <- await_fiber f;
    match res {
        Result.ok v => IO.pure (v == 2i64),
        Result.err _ => IO.pure false,
    }
}
