// pollFiber tests: none-while-running, some-exactly-once, the cancelled
// fiber's `err`, and the benign double-consume re-reads.
//
// One corner here is runner-agnostic on purpose: `test_poll_value_is_the_
// result` polls a fiber it KNOWS has stopped, so it pins the VALUE but no
// timing, and the Rust host's lazy poll (which runs the deferred action
// and is always `some`) satisfies it just as well. Everything else asserts
// on what only a CONCURRENT implementation can produce -- a `none` from a
// fiber that has not finished, a cancelled fiber answering `err` rather
// than a silent `none` -- and runs under the compiled backend's runner, like
// `combine_test.mo`'s header. The host's side of the contract (degraded
// semantics, the cancelled answer, the double-consume error) is pinned by
// `rust/core/src/core_native.rs`'s own unit tests, where an eval error is an
// assertion instead of a doomed `#[test]`.
//
// "Wait for the fiber" is a fixed `sleepIO` here rather than a poll loop:
// a bounded-retry helper recurses through two defs and the termination
// checker reasonably refuses to see the bound.

use lib::concurrent::fiber {FiberError, await_fiber, cancel_fiber, forkIO, pollFiber}
use lib::concurrent::combine {sleepIO}

def ok_is (r : Result FiberError I64) (v : I64) : Bool :=
  match r {
    Result.ok x => I64.beq x v,
    Result.err _ => false
  }

def polled_ok_is (o : Option (Result FiberError I64)) (v : I64) : Bool :=
  match o {
    Option.some r => ok_is r v,
    Option.none => false
  }

def err_is_cancelled (r : Result FiberError I64) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e {
      FiberError.cancelled => true,
      FiberError.never_started => false
    }
  }

def ok_value (r : Result FiberError I64) : I64 :=
  match r {
    Result.ok x => x,
    Result.err _ => -1
  }

def poll_300_then_42 (_ : Unit) : IO I64 := do {
  sleepIO 300;
  IO.pure 42
}

def sleep_100_action (_ : Unit) : IO I64 := do {
  sleepIO 100;
  IO.pure 7
}

// The compiled-only corner: the FIRST poll of a still-running fiber must
// be `none` -- that is what makes poll non-blocking rather than a slower
// `await`. Immediate, before the 300 ms body can have completed, then
// after it has stopped: `some`, carrying the value.
#[test]
def test_poll_none_then_some : IO Bool {
  let f <- forkIO poll_300_then_42;
  let first <- pollFiber f;
  let first_ok := match first { Option.none => true, Option.some _ => false };
  sleepIO 700;
  let later <- pollFiber f;
  return (polled_ok_is later 42 && first_ok)
}

// The runner-agnostic corner: the polled value IS the action's result.
// No timing asserted, so the lazy host (always `some` immediately) and
// the compiled backend (poll only answers once the fiber stops) both pass.
#[test]
def test_poll_value_is_the_result : IO Bool {
  let f <- forkIO poll_300_then_42;
  sleepIO 700;
  let o <- pollFiber f;
  return (polled_ok_is o 42)
}

// A cancelled fiber answers `some (err cancelled)` once it has stopped,
// never a silent `none` -- the way `await_fiber` answers IT, so a poll of
// an abandoned fiber terminates instead of dangling.
#[test]
def test_poll_cancelled_fiber_is_err : IO Bool {
  let f <- forkIO sleep_100_action;
  cancel_fiber f;
  sleepIO 300;
  let o <- pollFiber f;
  return (match o {
    Option.some r => err_is_cancelled r,
    Option.none => false
  })
}

// The benign double-consume: on the compiled backend, whoever consumed
// the reap (poll or await) wins the result, and the SECOND consumer
// re-reads the same stored value rather than faulting or hanging.
#[test]
def test_poll_then_await_re_reads : IO Bool {
  let f <- forkIO poll_300_then_42;
  sleepIO 700;
  let o <- pollFiber f;
  let v <- await_fiber f;
  return (polled_ok_is o (ok_value v))
}

#[test]
def test_await_then_poll_re_reads : IO Bool {
  let f <- forkIO poll_300_then_42;
  let v <- await_fiber f;
  let o <- pollFiber f;
  return (polled_ok_is o (ok_value v))
}