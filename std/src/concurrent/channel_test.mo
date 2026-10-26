// Channel and select tests.
//
// Every case here runs on both backends: the host has no concurrency, but a
// producer that is awaited before the take, prefilled channels and
// non-blocking probes behave identically there. The blocking put/take
// semantics (a real park and wake-up) are covered in
// runtime/tests/thread_stress.c, where two OS threads can exercise them
// deterministically.

use std::concurrent::channel {
    Channel, Channel.new, Channel.put, Channel.take, Channel.tryTake, select,
}
use std::concurrent::fiber {await_fiber, forkIO}

def new_i64 : IO (Channel I64) := Channel.new

def some_is (o : Option I64) (want : I64) : Bool :=
    match o {
        Option.some v => v == want,
        Option.none => false
    }

def is_none (o : Option I64) : Bool :=
    match o {
        Option.none => true,
        Option.some _ => false
    }

#[test]
def test_channel_roundtrip : IO Bool := do {
    let c <- new_i64;
    Channel.put c 42;
    let v <- Channel.take c;
    return (v == 42)
}

#[test]
def test_try_take_empty : IO Bool := do {
    let c <- new_i64;
    let o <- Channel.tryTake c;
    return (is_none o)
}

#[test]
def test_try_take_after_put : IO Bool := do {
    let c <- new_i64;
    Channel.put c 7;
    let o <- Channel.tryTake c;
    let drained <- Channel.tryTake c;
    return (some_is o 7 && is_none drained)
}

/// Both backends: awaiting the producer runs its put on the host before the
/// take, and the compiled fiber has stored the value by then too.
#[test]
def test_producer_then_take : IO Bool := do {
    let c <- new_i64;
    let f <- forkIO (fn (_ : Unit) => Channel.put c 9);
    let _ <- await_fiber f;
    let v <- Channel.take c;
    return (v == 9)
}

/// `select` probes in list order, so a value already waiting in the second
/// channel is found without touching the empty first one.
#[test]
def test_select_skips_empty : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    Channel.put b 5;
    let v <- select [a, b];
    return (v == 5)
}

#[test]
def test_select_first_ready : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    Channel.put a 3;
    Channel.put b 4;
    let v <- select [a, b];
    return (v == 3)
}
