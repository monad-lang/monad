// Fiber concurrency tests
// Tests for forkIO, await_fiber, cancel_fiber

use std.concurrent.fiber {await_fiber, fiber, forkIO}

def io_42_action (_ : Unit) : IO I64 := IO.io 42

def io_7_action (_ : Unit) : IO I64 := IO.io 7

def io_true_action (_ : Unit) : IO Bool := IO.io true

#[test]
def test_fork_and_await : IO Bool {
    let fiber <- forkIO io_42_action;
    let result <- await_fiber fiber;
    return (result == 42)
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
    return (r1 == 42 && r2 == 7)
}
