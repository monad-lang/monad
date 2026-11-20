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
use std::concurrent::combine {sleepIO}
open IO {current_time_nano}

def new_i64 : IO (Channel I64) := Channel.new

def some_is (o : Option I64) (want : I64) : Bool :=
    match o {
        Option.some v => v == want,
        Option.none => false
    }

#[test]
def test_channel_roundtrip : IO Bool := do {
    let c <- new_i64;
    let sc := Shared.of c;
    Channel.put (Shared.get sc) 42;
    let v <- Channel.take (Shared.get sc);
    return (v == 42)
}

#[test]
def test_try_take_empty : IO Bool := do {
    let c <- new_i64;
    let o <- Channel.tryTake c;
    return (Option.is_none o)
}

#[test]
def test_try_take_after_put : IO Bool := do {
    let c <- new_i64;
    let sc := Shared.of c;
    Channel.put (Shared.get sc) 7;
    let o <- Channel.tryTake (Shared.get sc);
    let drained <- Channel.tryTake (Shared.get sc);
    return (some_is o 7 && Option.is_none drained)
}

/// Both backends: awaiting the producer runs its put on the host before the
/// take, and the compiled fiber has stored the value by then too.
#[test]
def test_producer_then_take : IO Bool := do {
    let c <- new_i64;
    let sc := Shared.of c;
    let f <- forkIO (fn (_ : Unit) => Channel.put (Shared.get sc) 9);
    let _ <- await_fiber f;
    let v <- Channel.take (Shared.get sc);
    return (v == 9)
}

/// A value already waiting in the second channel is found without the
/// first one ever being touched.
#[test]
def test_select_skips_empty : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    let sa := Shared.of a;
    let sb := Shared.of b;
    Channel.put (Shared.get sb) 5;
    let v <- select [Shared.get sa, Shared.get sb];
    return (match v { Option.some x => x == 5, Option.none => false })
}

/// With both channels holding a value, the FIRST in list order wins:
/// `select` scans in order, so this is deterministic.
#[test]
def test_select_first_ready : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    let sa := Shared.of a;
    let sb := Shared.of b;
    Channel.put (Shared.get sa) 3;
    Channel.put (Shared.get sb) 4;
    let v <- select [Shared.get sa, Shared.get sb];
    return (match v { Option.some x => x == 3, Option.none => false })
}

/// `select` on an empty list has no value and must not block.
#[test]
def test_select_empty_is_none : IO Bool := do {
    let chs : List (Channel I64) := List.empty;
    let v <- select chs;
    return (match v { Option.some _ => false, Option.none => true })
}

/// THE blocking case: the value arrives from a fiber AFTER the select has
/// already parked. This is the one shape the old polling loop could not
/// distinguish from a fast probe, and the reason `select` now parks on
/// the channels themselves.
///
/// Compiled only: the host cannot park, so its `channel_take_any` does one
/// non-blocking scan and answers `none` at once -- this would see `none`,
/// not the 11 the later put provides.
#[test]
def test_select_waits_for_a_later_put : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    let sa := Shared.of a;
    let sb := Shared.of b;
    let sc := Shared.of b;
    let f <- forkIO (fn (_ : Unit) => do {
        sleepIO 50;
        Channel.put (Shared.get sc) 11
    });
    let v <- select [Shared.get sa, Shared.get sb];
    let _ <- await_fiber f;
    return (match v { Option.some x => x == 11, Option.none => false })
}

/// A select whose value arrives on a channel OTHER than the first, and
/// only after the select has parked. This is the case the cross-channel
/// wake exists for: the waiter sleeps on the FIRST channel's condvar, so
/// a put on the second has to reach that condvar through the registry.
///
/// It is a HANG case, not a slow one: before every watched channel was
/// registered, this blocked in `pthread_cond_wait` forever. The elapsed
/// bound below is what turns "blocked forever" into a failing test rather
/// than a stuck run. Compiled only -- the host answers `none` at once.
#[test]
def test_select_wakes_on_a_non_first_channel : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    let sa := Shared.of a;
    let sb := Shared.of b;
    let sc := Shared.of b;
    let f <- forkIO (fn (_ : Unit) => do {
        sleepIO 30;
        Channel.put (Shared.get sc) 42
    });
    let t0 <- current_time_nano;
    let v <- select [Shared.get sa, Shared.get sb];
    let t1 <- current_time_nano;
    let _ <- await_fiber f;
    let elapsed_ms := I64.div (I64.sub t1 t0) 1000000;
    return (some_is v 42 && elapsed_ms < 2000)
}
