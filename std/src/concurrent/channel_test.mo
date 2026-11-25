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
use std::concurrent::fiber {await_fiber, cancel_fiber, forkIO}
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

// A put/take cycle on one channel, once per tick in `ticks`. Each pass
// fills the channel and drains it, so the channel lock is taken and
// released repeatedly -- the churn `test_select_cancelled_while_parked`
// needs so the cancel's registry walk meets a channel lock that is
// actually held. Recurses over the list (the shape `cancel_all` uses)
// rather than over a counter, so every binder is consumed exactly once.
#[partial]
def churn_channel (sc : Shared (Channel I64)) (ticks : List I64) : IO Unit :=
    match ticks {
        List.empty => IO.pure Unit.unit,
        List.cons v rest => do {
            Channel.put (Shared.get sc) v;
            let _ <- Channel.take (Shared.get sc);
            churn_channel sc rest
        }
    }

/// A `select` waiter CANCELLED while it is parked, with other fibers
/// cycling put/take on the same channel throughout.
///
/// Cancellation reaches a blocked channel waiter only through
/// `channel_wake_cancelled`'s `ChanReg` walk, and this is the only test that
/// cancels a waiter parked in `select` -- the shape nothing covered. It
/// pins the CONTRACT: the cancel is observed, `await_fiber` answers
/// `err cancelled`, and the waiter does not stay parked.
///
/// It is deliberately NOT the deadlock gate, and it cannot be. The AB-BA
/// inversion in that walk (registry then channel lock, against
/// `channel_wait`'s channel-then-registry) needs a waiter to be inside its
/// narrow registration window at the instant a cancel fires. Here one
/// waiter registers once and is cancelled 20 ms later, already deep in
/// `pthread_cond_wait` holding no channel lock, so the canceller never
/// contends. MEASURED, not assumed: with the old inverted walk restored
/// this test still PASSES, which is why the real gate is
/// `thread_stress.c`'s `check_cancel_race` (6 waiters x 150 rounds,
/// staggered cancels, and a watchdog because a deadlock HANGS there).
///
/// The churn fibers keep the channel lock moving so the cancel's walk meets
/// a live holder rather than an idle registry -- useful stress, but see
/// above for what it does and does not prove.
///
/// Compiled only -- the host cannot park, so its `channel_take_any` scans
/// once and answers `none` at once, never reaching the registry or a
/// cancel.
#[test]
def test_select_cancelled_while_parked : IO Bool := do {
    let a <- new_i64;
    let b <- new_i64;
    let sa := Shared.of a;
    let sb := Shared.of b;
    let c1 <- forkIO (fn (_ : Unit) =>
        churn_channel sa [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
    let c2 <- forkIO (fn (_ : Unit) =>
        churn_channel sa [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]);
    let waiter <- forkIO (fn (_ : Unit) => do {
        let v <- select [Shared.get sa, Shared.get sb];
        return (Option.is_none v)
    });
    let swaiter := Shared.of waiter;
    // Let the waiter reach the park before the cancel, or the cancel lands
    // on a thread that has not got there yet.
    sleepIO 20;
    let t0 <- current_time_nano;
    cancel_fiber (Shared.get swaiter);
    let r <- await_fiber (Shared.get swaiter);
    let t1 <- current_time_nano;
    let _ <- await_fiber c1;
    let _ <- await_fiber c2;
    let elapsed_ms := I64.div (I64.sub t1 t0) 1000000;
    let observed_cancel := match r {
        Result.err _ => true,
        Result.ok _ => false
    };
    return (observed_cancel && I64.lt elapsed_ms 2000)
}
