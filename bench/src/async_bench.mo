/// Baseline and regression measurements for the fiber/async runtime
/// (`plans/implementations/monad-fiber-scheduler.md`, P0). One `#[test]`
/// per cost centre, each printing its number so a run is a record rather
/// than a pass/fail: `monad test bench/src/async_bench.mo`.
///
/// What it exists to answer, and why these particular shapes:
///
///   * `bench_fork_await` -- one `pthread_create` + Boehm thread
///     registration + 32 MB VA reservation per `forkIO`
///     (runtime/src/platform_posix.c's `monad_fork_io`). This is the cost
///     a fiber-per-connection server pays per request.
///   * `bench_race_win` -- the win latency of `race`, which used to poll
///     every contestant once a millisecond (a 1 ms FLOOR under every win)
///     and now parks on `wait_any`. Compare against
///     `race_win_floor_us_expected`: the excess over `WINNER_MS` is the
///     notice delay, and it should be far under the old floor.
///   * `bench_select_ready` -- the same quantity through `select`, which
///     used to `tryTake`-probe each channel every millisecond and now
///     parks on `channel_take_any`.
///   * `bench_channel_cancel` -- a fiber cancelled while blocked in
///     `Channel.take`. The runtime used to re-check the cancel flag on a
///     50 ms `pthread_cond_timedwait` tick; `monad_cancel_fiber` now wakes
///     the waiter, so this is microseconds rather than up to 50 ms.
///   * `bench_wait_any_cancel` -- the same quantity for the OTHER blocking
///     wait: a fiber cancelled while parked inside `race`, i.e. inside
///     `fiber_wait_any`. That is P1's own primitive and P2 left it behind
///     -- nothing signalled its condvar, so a cancelled racer was noticed
///     only on a 20 ms tick.
///   * `bench_fiber_va` -- 200 abandoned fibers' virtual size, the
///     "one OS thread per fiber does not scale" number.
///   * `bench_sleep_overlap` -- the control: `sleepIO` really does
///     overlap across fibers (the one property the interim model gets
///     right, and what `combine_test.mo` pins).
///
/// Measurements are reported in MICROSECONDS, not milliseconds. Every
/// cost of interest here is sub-millisecond or a few ms, and a
/// millisecond quotient of a whole-run span rounds to single digits -- so
/// `race_win_us_k8` would read `0` and carry no signal at all.
///
/// Compiled backend only. The Rust host's `forkIO` is lazy (it defers the
/// action to the first await), so every number here would measure the
/// host's sequential degradation rather than the runtime. Run this with
/// the compiled `monad test`.
use std::concurrent::channel {Channel, Channel.new, Channel.put, Channel.take, select}
use std::concurrent::combine {Combine.Duration, Timeout, race, sleepIO, timeout}
use std::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, forkIO}
use std::io {}
use std::path {Path}
open IO {current_time_nano}

// ─── helpers ────────────────────────────────────────────────────────────

/// Print one labelled figure. `Bench.report` is NOT used: it appends a
/// literal "ms" to every label, which would misreport the microsecond
/// and kilobyte values this file is built around. Printing the unit in
/// the label keeps the transcript honest.
def report (label : String) (value : I64) : IO Unit :=
    IO.println (String.concat label (I64.to_string value))

def ns_to_us (span_ns : I64) : I64 :=
    I64.div span_ns 1000

def fast_action (_ : Unit) : IO I64 := IO.pure 2

def sleeper_action (_ : Unit) : IO I64 := do {
    sleepIO 300;
    return 1
}

def WINNER_MS : I64 := 50

/// The race's winner: sleeps `WINNER_MS`, so it is NOT ready when the
/// race's first probe runs. An instantly-ready winner is found on probe
/// zero and the measurement then contains no poll interval at all.
def winner_action (_ : Unit) : IO I64 := do {
    sleepIO WINNER_MS;
    return 2
}

def new_i64_channel : IO (Channel I64) := Channel.new

/// A `Result`'s ok payload, or `d` -- so a loop folds something that
/// proves it actually ran.
def ok_or (r : Result e I64) (d : I64) : I64 :=
    match r { Result.ok v => v, Result.err _ => d }

// ─── fork + await round trip ────────────────────────────────────────────

/// `n` fork+await round trips, each fiber answering immediately, so the
/// per-fiber figure is dominated by thread creation.
#[partial]
def fork_await_loop (i : I64) (n : I64) (acc : I64) : IO I64 :=
    if I64.lt i n
    then do {
        let f <- forkIO fast_action;
        let r <- await_fiber f;
        fork_await_loop (I64.add i 1) n (I64.add acc (ok_or r 0))
    }
    else IO.pure acc

#[test]
def bench_fork_await : IO Bool := do {
    let n : I64 := 200;
    let t0 <- current_time_nano;
    let total <- fork_await_loop 0 n 0;
    let t1 <- current_time_nano;
    let span := I64.sub t1 t0;
    report "fork_await_total_us_n200" (ns_to_us span);
    report "fork_await_per_fiber_us" (I64.div (ns_to_us span) n);
    return (I64.gt total 0)
}

// ─── race win latency (the old 1 ms polling floor) ──────────────────────

#[partial]
def fork_sleepers (k : I64) (acc : List (Fiber I64)) : IO (List (Fiber I64)) :=
    if I64.lt k 1
    then IO.pure acc
    else do {
        let f <- forkIO sleeper_action;
        fork_sleepers (I64.sub k 1) (List.cons f acc)
    }

/// Race one `winner_action` fiber (50 ms) against `n-1` sleepers (300 ms).
/// The winner is ready well after the race starts, so the reported span
/// is `WINNER_MS` plus however late `race` noticed -- which is exactly
/// the quantity P1 removed. The winner is forked LAST so the sleepers are
/// all already armed when the winner's clock starts.
def race_win_us (n : I64) : IO I64 := do {
    let sleepers <- fork_sleepers (I64.sub n 1) List.empty;
    let winner <- forkIO winner_action;
    let contestants := List.cons winner sleepers;
    let t0 <- current_time_nano;
    let r <- race contestants;
    let t1 <- current_time_nano;
    let _v : I64 := ok_or r 0;
    IO.pure (ns_to_us (I64.sub t1 t0))
}

#[test]
def bench_race_win : IO Bool := do {
    let us2 <- race_win_us 2;
    let us8 <- race_win_us 8;
    report "race_win_us_k2" us2;
    report "race_win_us_k8" us8;
    report "race_win_floor_us_old" 1000;
    report "race_winner_ms" WINNER_MS;
    // Two separate claims, and the second is the one P1 bought.
    //
    // (a) The race did NOT wait for the 300 ms sleeper: it returned well
    //     inside that, so the losers were cancelled rather than awaited.
    // (b) The race returned no earlier than its winner: the span covers
    //     the winner's own sleep, so a floor a little under `WINNER_MS`
    //     (not exactly it -- `sleepIO` may return marginally early) is
    //     what makes this a measurement of `race` and not of nothing.
    // The NOTICE delay is `us8` minus the winner's sleep; it used to have
    // a 1 ms floor under it (`race_win_floor_us_old`) and is now within
    // the measurement's own noise of zero, which is the whole point.
    let lower := I64.mul (I64.sub WINNER_MS 10) 1000;
    return (I64.gt us8 lower && I64.lt us8 250000)
}

// ─── select latency (same quantity, different consumer) ─────────────────

/// Put a value in the SECOND of two channels, then `select` over both.
/// The value is already waiting, so `select` must find it without
/// spending a poll interval first.
#[test]
def bench_select_ready : IO Bool := do {
    let a <- new_i64_channel;
    let b <- new_i64_channel;
    let sa := Shared.of a;
    let sb := Shared.of b;
    let _ <- Channel.put (Shared.get sb) 5;
    let t0 <- current_time_nano;
    let v <- select [Shared.get sa, Shared.get sb];
    let t1 <- current_time_nano;
    report "select_ready_us" (ns_to_us (I64.sub t1 t0));
    return (match v { Option.some x => I64.beq x 5, Option.none => false })
}

// ─── channel round trip ─────────────────────────────────────────────────

/// A producer fiber puts, the parent takes: the uncontended handoff,
/// which is the path with no parked waiter on either side.
#[partial]
def channel_round_trips (i : I64) (n : I64) (sc : Shared (Channel I64)) (acc : I64) : IO I64 :=
    if I64.lt i n
    then do {
        let f <- forkIO (fn (_ : Unit) => Channel.put (Shared.get sc) i);
        let _ <- await_fiber f;
        let v <- Channel.take (Shared.get sc);
        channel_round_trips (I64.add i 1) n sc (I64.add acc v)
    }
    else IO.pure acc

#[test]
def bench_channel_round_trip : IO Bool := do {
    let c <- new_i64_channel;
    let n : I64 := 100;
    let t0 <- current_time_nano;
    let total <- channel_round_trips 0 n (Shared.of c) 0;
    let t1 <- current_time_nano;
    let span := I64.sub t1 t0;
    report "channel_round_trip_total_us_n100" (ns_to_us span);
    report "channel_round_trip_per_us" (I64.div (ns_to_us span) n);
    return (I64.gt total 0)
}

// ─── cancellation latency while blocked in a channel ───────────────────

/// A fiber blocked in `Channel.take` on an empty channel is cancelled and
/// then AWAITED. Awaiting -- rather than polling -- is what makes this the
/// true wake latency: the handle answers `err cancelled` only once the
/// runtime has actually woken the waiter, so this is the time from
/// `cancel_fiber` to the blocked `take` returning. It was bounded below
/// by the old 50 ms `pthread_cond_timedwait` tick; `monad_cancel_fiber`
/// now pushes the wake, so it should be microseconds.
///
/// The handle is shared because `cancel_fiber` and `await_fiber` both
/// consume a `Fiber`, which is affine.
///
/// Nothing is ever put into the channel on purpose: the point is an
/// indefinite wait, which is the case the old timed re-check existed for.
#[test]
def bench_channel_cancel : IO Bool := do {
    let c <- new_i64_channel;
    let sc := Shared.of c;
    let f <- forkIO (fn (_ : Unit) => Channel.take (Shared.get sc));
    let sf := Shared.of f;
    // Let the fiber actually reach the blocking wait before cancelling,
    // or the cancel lands on a thread that has not parked yet and the
    // measurement is of thread startup instead.
    sleepIO 20;
    let t0 <- current_time_nano;
    cancel_fiber (Shared.get sf);
    let r <- await_fiber (Shared.get sf);
    let t1 <- current_time_nano;
    report "channel_cancel_observe_us" (ns_to_us (I64.sub t1 t0));
    report "channel_wait_ms_floor_old" 50;
    return (match r {
        Result.ok _ => false,
        Result.err _ => true
    })
}

// ─── cancellation latency while parked in `wait_any` ───────────────────

/// A fiber parked inside `race` -- i.e. inside `fiber_wait_any` -- is
/// cancelled and then awaited. The contestants never finish (they are
/// long sleepers), so the racer can only leave its park through the
/// cancel path: this is the time from `cancel_fiber` to `wait_any`
/// answering, and nothing else can end it.
///
/// This is P2's measurement applied to P1's primitive. When `wait_any`
/// landed it parked on its own `fiber_any_cond` with a 20 ms timed wait
/// purely so it could re-check `monad_fiber_cancelled`, because
/// `monad_cancel_fiber` woke channel waiters only. The fix is the same
/// push-a-wake shape P2 used for channels, so the figure should be
/// microseconds rather than up to 20 ms.
///
/// The handle is shared because `cancel_fiber` and `await_fiber` both
/// consume a `Fiber`, which is affine.
#[test]
def bench_wait_any_cancel : IO Bool := do {
    let s1 <- forkIO sleeper_action;
    let s2 <- forkIO sleeper_action;
    let sc := Shared.of (List.cons s1 (List.cons s2 List.empty));
    let racer <- forkIO (fn (_ : Unit) => do {
        // `race` parks inside `wait_any`; a 300 ms sleeper means it is
        // still parked when the cancel below lands.
        let _ <- race (Shared.get sc);
        return 1
    });
    let sf := Shared.of racer;
    sleepIO 20;
    let t0 <- current_time_nano;
    cancel_fiber (Shared.get sf);
    let r <- await_fiber (Shared.get sf);
    let t1 <- current_time_nano;
    report "wait_any_cancel_observe_us" (ns_to_us (I64.sub t1 t0));
    report "wait_any_tick_ms_old" 20;
    return (match r {
        Result.ok _ => false,
        Result.err _ => true
    })
}

// ─── 200 abandoned fibers: virtual size / RSS ──────────────────────────

#[partial]
def abandon_fibers (k : I64) (acc : List (Fiber I64)) : IO (List (Fiber I64)) :=
    if I64.lt k 1
    then IO.pure acc
    else do {
        let f <- forkIO sleeper_action;
        abandon_fibers (I64.sub k 1) (List.cons f acc)
    }

#[partial]
def cancel_each (fs : List (Fiber I64)) : IO Unit :=
    match fs {
        List.empty => IO.pure unit,
        List.cons f rest => do {
            cancel_fiber f;
            cancel_each rest
        }
    }

/// The first run of decimal digits in `s` as an integer, or 0. Skips the
/// whitespace `/proc/self/status` puts between a field name and its
/// value (`VmSize:\t  123456 kB`), so no per-field slice length is
/// needed.
#[partial]
def digits_in (s : String) (i : I64) (n : I64) (acc : I64) (seen : Bool) : I64 :=
    if I64.lt i n
    then
        let ch : String := String.slice s i 1 in
        if String.contains "0123456789" ch
        then digits_in s (I64.add i 1) n (I64.add (I64.mul acc 10) (digit_value ch)) true
        else if seen then acc
        else digits_in s (I64.add i 1) n acc false
    else acc

def digit_value (ch : String) : I64 :=
    if String.beq ch "0" then 0
    else if String.beq ch "1" then 1
    else if String.beq ch "2" then 2
    else if String.beq ch "3" then 3
    else if String.beq ch "4" then 4
    else if String.beq ch "5" then 5
    else if String.beq ch "6" then 6
    else if String.beq ch "7" then 7
    else if String.beq ch "8" then 8
    else 9

/// The kB figure on the line starting with `needle`, or 0.
#[partial]
def field_kb_in (needle : String) (lines : List String) : I64 :=
    match lines {
        List.empty => 0,
        List.cons line rest =>
            if String.starts_with needle line
            then digits_in line 0 (String.length line) 0 false
            else field_kb_in needle rest
    }

def read_field_kb (needle : String) : IO I64 := do {
    let r <- IO.read_file (Path.path "/proc/self/status");
    match r {
        Result.ok text => IO.pure (field_kb_in needle (String.split text "\n")),
        Result.err _ => IO.pure 0,
    }
}

/// 200 fibers neither awaited nor cancelled, each holding a 32 MB ADDRESS
/// reservation plus its touched pages until its body returns. VmSize is
/// the figure that shows the per-fiber ceiling a thread-per-fiber model
/// hits (200 x 32 MB = 6.4 GB of virtual space, untouched, so RSS is
/// unaffected); VmRSS shows what is actually committed. The fibers are
/// then cancelled so this test does not leak threads into the ones after
/// it.
#[test]
def bench_fiber_va : IO Bool := do {
    let before_va <- read_field_kb "VmSize:";
    let before_rss <- read_field_kb "VmRSS:";
    let fs <- abandon_fibers 200 List.empty;
    sleepIO 50;
    let after_va <- read_field_kb "VmSize:";
    let after_rss <- read_field_kb "VmRSS:";
    report "fiber_va_before_kb" before_va;
    report "fiber_va_after_200_kb" after_va;
    report "fiber_va_growth_kb" (I64.sub after_va before_va);
    report "fiber_va_per_fiber_kb" (I64.div (I64.sub after_va before_va) 200);
    report "fiber_rss_before_kb" before_rss;
    report "fiber_rss_after_200_kb" after_rss;
    report "fiber_rss_growth_kb" (I64.sub after_rss before_rss);
    cancel_each fs;
    // A gate only on what is already guaranteed: the 200 threads exist,
    // and /proc was readable. The VA figure is the measurement, not a
    // defect -- the reservation is deliberate (deep compiled recursion
    // needs it), and reporting it is the point.
    return (I64.gt after_va before_va && I64.gt after_va 0)
}

// ─── sleepIO really overlaps (the control) ─────────────────────────────

#[partial]
def join_all (fs : List (Fiber I64)) : IO Unit :=
    match fs {
        List.empty => IO.pure unit,
        List.cons f rest => do {
            let _ <- await_fiber f;
            join_all rest
        }
    }

#[partial]
def fork_sleepers_any (k : I64) (ms : I64) (acc : List (Fiber I64)) : IO (List (Fiber I64)) :=
    if I64.lt k 1
    then IO.pure acc
    else do {
        let f <- forkIO (fn (_ : Unit) => do { sleepIO ms; return 1 });
        fork_sleepers_any (I64.sub k 1) ms (List.cons f acc)
    }

/// `n` sleepers forked BEFORE any is awaited: ~`ms` if they overlap,
/// `n * ms` if they are a sum. Reports the span and whether it fits the
/// concurrent expectation. `combine_test.mo`'s
/// `test_sleepIO_fibers_run_concurrently` asserts the same fact as a
/// pass/fail gate at 500 ms x 4; this is the general, reported form.
#[test]
def bench_sleep_overlap : IO Bool := do {
    let n : I64 := 4;
    let ms : I64 := 200;
    let t0 <- current_time_nano;
    let fs <- fork_sleepers_any n ms List.empty;
    let t1 <- current_time_nano;
    join_all fs;
    let t2 <- current_time_nano;
    report "sleep_overlap_fork_us" (ns_to_us (I64.sub t1 t0));
    report "sleep_overlap_join_us" (ns_to_us (I64.sub t2 t1));
    // Concurrent: ~`ms`. Sequential: ~`n * ms`. Halfway is the bound.
    // `t2 - t1` is NANOSECONDS, so the bound has to be in the same unit --
    // `ns_to_us` is for the reported figure only, not the comparison.
    let concurrent_ns := I64.mul ms 1000000;
    let sequential_ns := I64.mul (I64.mul ms n) 1000000;
    let bound_ns := I64.div (I64.add concurrent_ns sequential_ns) 2;
    return (I64.lt (I64.sub t2 t1) bound_ns)
}

// ─── timeout: what a bounded wait costs ────────────────────────────────

/// A bounded wait whose body finishes first. `timeout` is built from
/// `race [waiter, timer]`, so ONE call forks the body's fiber, a waiter
/// and a timer -- three threads for a single bounded wait. P1 removed its
/// timer WAKEUPS (the old `race` polled once a millisecond) but not its
/// threads; turning the timer into a reactor deadline is P4's work
/// (`monad-fiber-scheduler.md`).
#[test]
def bench_timeout_finished : IO Bool := do {
    let work_ms : I64 := 10;
    let f <- forkIO (fn (_ : Unit) => do { sleepIO work_ms; return 7 });
    let d : Combine.Duration := { millis := 3000 };
    let t0 <- current_time_nano;
    let r <- timeout d f;
    let t1 <- current_time_nano;
    report "timeout_finished_us" (ns_to_us (I64.sub t1 t0));
    report "timeout_threads_per_call" 3;
    return (match r {
        Result.ok t => match t {
            Timeout.finished inner => I64.beq (ok_or inner 0) 7,
            Timeout.expired => false
        },
        Result.err _ => false
    })
}
