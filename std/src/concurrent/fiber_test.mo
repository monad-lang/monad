// Fiber concurrency tests
// Tests for forkIO, await_fiber, cancel_fiber

use lib::concurrent::fiber {
    FiberError, FiberError.message, FiberError.of_code, await_fiber, cancel_fiber, forkIO,
}
use lib::concurrent::combine {sleepIO}

def io_42_action (_ : Unit) : IO I64 := IO.pure 42

def io_7_action (_ : Unit) : IO I64 := IO.pure 7

def io_true_action (_ : Unit) : IO Bool := IO.pure true

def slow_1_action (_ : Unit) : IO I64 := do {
    sleepIO 300;
    return 1
}

def is_cancelled (e : FiberError) : Bool :=
    match e {
        FiberError.cancelled => true,
        FiberError.never_started => false
    }

def err_is_cancelled (r : Result FiberError I64) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => is_cancelled e
    }

def is_never_started (e : FiberError) : Bool :=
    match e {
        FiberError.cancelled => false,
        FiberError.never_started => true
    }

/// The natives' error codes: 1 is `cancelled`, 2 `never_started`, and
/// each error has a message of its own. `never_started` cannot be forced
/// from Monad code; `runtime/tests/thread_stress.c` covers the runtime
/// side of it.
#[test]
def test_fiber_error_codes : Bool :=
    is_cancelled (FiberError.of_code 1)
        && is_never_started (FiberError.of_code 2)
        && Bool.not (String.beq (FiberError.message FiberError.cancelled)
                                (FiberError.message FiberError.never_started))

def ok_is (r : Result FiberError I64) (v : I64) : Bool :=
    match r {
        Result.ok x => x == v,
        Result.err _ => false
    }

#[test]
def test_fork_and_await : IO Bool {
    let fiber <- forkIO io_42_action;
    let result <- await_fiber fiber;
    return (ok_is result 42)
}

#[test]
def test_fork_returns_io_fiber : IO Bool {
    forkIO io_true_action;
    return true
}

#[test]
def test_fork_multiple_and_await : IO Bool {
    let f1 <- forkIO io_42_action;
    let f2 <- forkIO io_7_action;
    let r2 <- await_fiber f2;
    let r1 <- await_fiber f1;
    return (ok_is r1 42 && ok_is r2 7)
}

/// A fiber cancelled before it finishes has no result: await says so
/// instead of handing back a made-up value. Holds on both backends: the
/// compiled fiber is still sleeping when the cancel lands, and the host
/// has not run it at all.
#[test]
def test_await_cancelled_is_err : IO Bool {
    let f <- forkIO slow_1_action;
    cancel_fiber f;
    let r <- await_fiber f;
    return (err_is_cancelled r)
}
