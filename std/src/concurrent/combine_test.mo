// Structured concurrency tests: all, race, scoped, sleepIO, cancel_all
//
// One test here, `test_sleepIO_fibers_run_concurrently`, asserts on
// ELAPSED TIME, so it fails on any implementation that serializes
// fibers. The Rust host is such an implementation and is lazy on
// purpose; this file runs under the compiled backend's runner, not the
// host's. See that test's own comment for the numbers and the reason.

use lib::concurrent::fiber {Fiber, await_fiber, cancel_fiber, forkIO}
use lib::concurrent::combine {Scope, scope_fork, scoped, sleepIO}
use lib::io {current_time_nano}
open IO {current_time_nano}

// Helper thunks

def io_10_action (_ : Unit) : IO I64 := IO.pure 10

def io_20_action (_ : Unit) : IO I64 := IO.pure 20

def io_30_action (_ : Unit) : IO I64 := IO.pure 30

def io_42_action (_ : Unit) : IO I64 := IO.pure 42

// all: concrete specialized

def all_i64 (fibers : List (Fiber I64)) : IO (List I64) :=
  match fibers {
    List.empty => IO.pure (List.empty : List I64),
    List.cons f rest => do {
      let head <- await_fiber f;
      let tail <- all_i64 rest;
      return (List.cons head tail)
    }
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

def race_i64 (fibers : List (Fiber I64)) : IO I64 :=
  match fibers {
    List.cons f rest => do {
      cancel_i64 rest;
      await_fiber f
    }
  }

// Tests

#[test]
def test_all_single : IO Bool {
  let f <- forkIO io_42_action;
  let fibers := List.cons f List.empty;
  let results <- all_i64 fibers;
  return true
}

#[test]
def test_all_two : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  let results <- all_i64 fibers;
  return true
}

#[test]
def test_all_three : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let f3 <- forkIO io_30_action;
  let fibers := List.cons f1 (List.cons f2 (List.cons f3 List.empty));
  let results <- all_i64 fibers;
  return true
}

def is_empty (xs : List I64) : Bool :=
  match xs {
    List.empty => true,
    List.cons _ _ => false
  }

#[test]
def test_all_empty : IO Bool {
  let fibers := (List.empty : List (Fiber I64));
  let results <- all_i64 fibers;
  return (is_empty results)
}

#[test]
def test_race_first : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  let result <- race_i64 fibers;
  return (result == 10)
}

#[test]
def test_race_single : IO Bool {
  let f1 <- forkIO io_30_action;
  let fibers := List.cons f1 List.empty;
  let result <- race_i64 fibers;
  return (result == 30)
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

def fork_io_42_scoped (s : Scope) : IO (Fiber I64) := scope_fork s io_42_action

def scoped_fork_await_42 (s : Scope) : IO I64 := do {
  let f <- fork_io_42_scoped s;
  await_fiber f
}

#[test]
def test_scoped_runs_action : IO Bool {
  let result <- scoped scoped_fork_await_42;
  return (result == 42)
}

// scoped: auto-cancels on exit (callback returns without awaiting)
def scoped_forget (s : Scope) : IO I64 := do {
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
