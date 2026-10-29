// Structured concurrency tests: all, race, scoped, sleepIO, cancel_all
//
// One test here, `test_sleepIO_fibers_run_concurrently`, asserts on
// ELAPSED TIME, so it fails on any implementation that serializes
// fibers. The Rust host is such an implementation and is lazy on
// purpose; this file runs under the compiled backend's runner, not the
// host's. See that test's own comment for the numbers and the reason.

use lib::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, forkIO}
use lib::concurrent::combine {
  Combine.Duration, FiberScope, Timeout, all, race, scope_fork, scoped, sleepIO, timeout,
}
use lib::io {}
use lib::list {List.length}
open IO {current_time_nano}

// Helper thunks

def io_10_action (_ : Unit) : IO I64 := IO.pure 10

def io_20_action (_ : Unit) : IO I64 := IO.pure 20

def io_30_action (_ : Unit) : IO I64 := IO.pure 30

def io_42_action (_ : Unit) : IO I64 := IO.pure 42

def ok_is (r : Result FiberError I64) (v : I64) : Bool :=
  match r {
    Result.ok x => x == v,
    Result.err _ => false
  }

// `all` collects in reverse await order; only the count is checked.
def ok_count (r : Result FiberError (List I64)) (n : I64) : Bool :=
  match r {
    Result.ok xs => List.length xs == n,
    Result.err _ => false
  }

// race: concrete specialized

def cancel_i64 (fibers : List (Fiber I64)) : IO Unit :=
  match fibers {
    List.empty => IO.pure Unit.unit,
    List.cons f rest => do {
      cancel_fiber f;
      cancel_i64 rest
    }
  }

// Tests

#[test]
def test_all_single : IO Bool {
  let f <- forkIO io_42_action;
  let fibers := List.cons f List.empty;
  let results <- all fibers;
  return (ok_count results 1)
}

#[test]
def test_all_two : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  let results <- all fibers;
  return (ok_count results 2)
}

#[test]
def test_all_three : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let f3 <- forkIO io_30_action;
  let fibers := List.cons f1 (List.cons f2 (List.cons f3 List.empty));
  let results <- all fibers;
  return (ok_count results 3)
}

#[test]
def test_all_empty : IO Bool {
  let fibers := (List.empty : List (Fiber I64));
  let results <- all fibers;
  return (ok_count results 0)
}

def err_is_cancelled (r : Result FiberError A) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e {
      FiberError.cancelled => true,
      FiberError.never_started => false
    }
  }

/// `all` stops at the first fiber with no result and reports why, rather
/// than handing back a list with a made-up element. Both backends: the
/// cancelled fiber is still sleeping (compiled) or never ran (host).
#[test]
def test_all_reports_a_cancelled_fiber : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO slow_10_action;
  cancel_fiber f2;
  let results <- all [f1, f2];
  return (err_is_cancelled results)
}

/// A race whose only contestant was cancelled answers `err cancelled`
/// once that fiber stops, instead of a value it never produced.
#[test]
def test_race_of_a_cancelled_fiber_is_err : IO Bool {
  let f <- forkIO slow_10_action;
  cancel_fiber f;
  let result <- race [f];
  return (err_is_cancelled result)
}

def slow_10_action (_ : Unit) : IO I64 := do {
  sleepIO 400;
  return 10
}

/// The first fiber to FINISH wins, not the first in the list: the head
/// sleeps 400 ms, so the instant one must win, and well before the head
/// would have finished. Compiled only, like the timing test below: the
/// host runs fibers lazily and in order, so its head always wins.
#[test]
def test_race_first_to_finish : IO Bool {
  let start <- current_time_nano;
  let slow <- forkIO slow_10_action;
  let fast <- forkIO io_20_action;
  let result <- race [slow, fast];
  let stop <- current_time_nano;
  let elapsed_ms := I64.div (I64.sub stop start) 1000000;
  return (ok_is result 20 && elapsed_ms < 300)
}

#[test]
def test_race_single : IO Bool {
  let f1 <- forkIO io_30_action;
  let fibers := List.cons f1 List.empty;
  let result <- race fibers;
  return (ok_is result 30)
}

#[test]
def test_cancel_all_smoke : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  cancel_i64 fibers;
  return true
}

// scoped: creates scope, runs action, auto-cancels on exit

def fork_io_42_scoped (s : FiberScope) : IO (Fiber I64) := scope_fork s io_42_action

def scoped_fork_await_42 (s : FiberScope) : IO (Result FiberError I64) := do {
  let f <- fork_io_42_scoped s;
  await_fiber f
}

#[test]
def test_scoped_runs_action : IO Bool {
  let result <- scoped scoped_fork_await_42;
  return (ok_is result 42)
}

// scoped: auto-cancels on exit (callback returns without awaiting)
def scoped_forget (s : FiberScope) : IO I64 := do {
  scope_fork s io_42_action;
  return 0
}

#[test]
def test_scoped_cancels : IO Bool {
  let result <- scoped scoped_forget;
  return (result == 0)
}

// sleepIO: basic smoke test

#[test]
def test_sleepIO_smoke : IO Bool {
  sleepIO 10;
  return true
}

// The one test here that only a genuinely CONCURRENT implementation can
// pass, and the reason `forkIO` must actually start its thread at the
// fork rather than defer the action to the first `await`.
//
// Every other test in this file -- and every test in `fiber_test.mo` --
// passes just as well on a sequential implementation, because each one
// awaits the fiber it just forked: a `forkIO` that returns a deferred
// thunk, and an `await_fiber` that runs it inline, satisfies them all.
// That is exactly what the Rust host does on purpose (see
// `core/src/core_native.rs`'s `fork_io`, "cooperative/lazy, not real
// OS-thread concurrency"), so those tests cannot tell the backends
// apart. This one can: four fibers are forked BEFORE any of them is
// awaited, so the four sleeps overlap only if the four threads exist at
// the same time.
//
//   concurrent  -> the sleeps overlap            -> ~500 ms
//   sequential  -> the sleeps are a sum          -> ~2000 ms
//
// The bound is 1200 ms: 2.4x the concurrent expectation, so a loaded or
// slow machine cannot flake it, and well under the sequential sum, so a
// serialized implementation cannot squeak past it. The 500 ms sleep is
// long enough that thread startup -- a `pthread_create` plus Boehm's
// thread registration, tens of microseconds, with the 128 MB stack
// committed lazily -- cannot move the result either way. `_r1`..`_r4`
// are bound rather than discarded only so the awaits read as an
// ordered sequence of four; their values are all `Unit`.
def sleep_500_action (_ : Unit) : IO Unit := sleepIO 500

#[test]
def test_sleepIO_fibers_run_concurrently : IO Bool {
  let start <- current_time_nano;
  let f1 <- forkIO sleep_500_action;
  let f2 <- forkIO sleep_500_action;
  let f3 <- forkIO sleep_500_action;
  let f4 <- forkIO sleep_500_action;
  let _r1 <- await_fiber f1;
  let _r2 <- await_fiber f2;
  let _r3 <- await_fiber f3;
  let _r4 <- await_fiber f4;
  let finish <- current_time_nano;
  return (I64.lt (I64.sub finish start) 1200000000)
}

/// The waiter is first in the race list, so the lazy host runs it and
/// reports `finished`; the compiled backend races it against the timer and
/// the work finishes first either way.
#[test]
def test_timeout_finished_before_expiry : IO Bool := do {
  let f <- forkIO (fn (_ : Unit) => do { sleepIO 10; return 7i64 });
  let d : Combine.Duration := { millis := 300 };
  let r <- timeout d f;
  return (match r {
    Result.ok t => match t {
      Timeout.finished inner => ok_is inner 7,
      Timeout.expired => false
    },
    Result.err _ => false
  })
}

/// Compiled-only: the host's poll runs the waiter to completion, so it can
/// never observe the timer winning.
#[test]
def test_timeout_expires : IO Bool := do {
  let f <- forkIO (fn (_ : Unit) => do { sleepIO 300; return 7i64 });
  let d : Combine.Duration := { millis := 20 };
  let r <- timeout d f;
  return (match r {
    Result.ok t => match t {
      Timeout.finished _ => false,
      Timeout.expired => true
    },
    Result.err _ => false
  })
}
