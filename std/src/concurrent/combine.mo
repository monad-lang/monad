// Structured concurrency combinators: all, race, timeout, scoped, sleepIO,
// Duration.
// Builds on forkIO/await_fiber/cancel_fiber from std.concurrent.fiber.

use lib::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, forkIO, pollFiber, wait_any}

// `Combine.Duration`, not `Duration`: `motes/time` declares a `pub Duration`
// (seconds and nanos) and whole-program qualification makes the bare name
// ambiguous, so the literal `{ millis := 300 }` resolved to the wrong one.
// Same reason `FiberScope` below carries a namespace note.
//
// `pub` because it appears in `timeout`'s SIGNATURE, which is already `pub`.
// A private type in a public signature makes the operation uncallable from
// any other mote: the use-completeness gate refuses the caller's reference
// to the type, so `timeout` was reachable in name only. `{ millis := n }`
// still works at a call site (`bench/src/async_bench.mo` does exactly that).
pub struct Combine.Duration {
    millis : I64,
}

// `FiberScope`, not `FiberScope`: lang/types.mo also declares a `FiberScope`, and
// whole-program qualification (plan item 5.1) makes that bare name ambiguous.
type FiberScope {
    scope
}

#[native sleep_io]
priv def sleep_io_raw (ms : I64) : RawIO Unit

pub def sleepIO (ms : I64) : IO Unit := IO.mk (sleep_io_raw ms)

#[native scope_new]
priv def scope_new_raw : RawIO FiberScope

def scope_new : IO FiberScope := IO.mk scope_new_raw

#[native scope_fork]
priv def scope_fork_raw (s : FiberScope) (action : Unit -> IO A) : RawIO (Fiber A)

def scope_fork (s : FiberScope) (action : Unit -> IO A) : IO (Fiber A) :=
    IO.mk (scope_fork_raw s action)

#[native scope_drop]
priv def scope_drop_raw (s : FiberScope) : RawIO Unit

def scope_drop (s : FiberScope) : IO Unit := IO.mk (scope_drop_raw s)

// Await all fibers in order, collecting results; the first error ends it.
def all_aux (fibers : List (Fiber A)) (acc : List A) : IO (Result FiberError (List A)) :=
    match fibers {
        List.empty => IO.pure (Result.ok acc),
        List.cons f rest =>
            Monad.bind (await_fiber f) (fn r =>
                match r {
                    Result.ok head => all_aux rest (List.cons head acc),
                    Result.err e => IO.pure (Result.err e)
                })
    }

/// Every fiber's result, or the first error met awaiting them in order.
/// The fibers after a failed one are not awaited.
pub def all {A : Type} (fibers : List (Fiber A)) : IO (Result FiberError (List A)) :=
    all_aux fibers List.empty

#[partial]
def cancel_all (fibers : List (Fiber A)) : IO Unit :=
    match fibers {
        List.empty => IO.pure Unit.unit,
        List.cons f rest => do {
            cancel_fiber f;
            cancel_all rest
        }
    }

// The answer of whichever contestant `wait_any` named first. Split out
// because a `let x <- ...` inside a `match` arm is a recorded checker
// trap, so each stage gets its own small def.
def race_answer (winner : Fiber A) : IO (Result FiberError A) :=
    Monad.bind (await_fiber winner) (fn r => IO.pure r)

// Cancel every contestant, then hand back the winner's answer.
def race_won (fibers : Shared (List (Fiber A))) (winner : Fiber A) : IO (Result FiberError A) := do {
    let answer <- race_answer winner;
    let _ <- cancel_all (Shared.get fibers);
    return answer
}

// The fiber at `idx` in `fibers`, or the head when the index is out of
// range (which only an empty list could cause, and `race` refuses that).
def fiber_at (fibers : List (Fiber A)) (idx : I64) : Option (Fiber A) :=
    match fibers {
        List.empty => Option.none,
        List.cons f rest =>
            if I64.lt idx 1 then Option.some f else fiber_at rest (I64.sub idx 1)
    }

def race_pick (fibers : Shared (List (Fiber A))) (idx : Option I64) : IO (Result FiberError A) :=
    match idx {
        Option.some i =>
            match fiber_at (Shared.get fibers) i {
                Option.some winner => race_won fibers winner,
                Option.none => IO.pure (Result.err FiberError.never_started)
            },
        // `wait_any` answers `none` only when the waiter itself was
        // cancelled; there is no winner to report.
        Option.none => IO.pure (Result.err FiberError.cancelled)
    }

/// The answer of whichever fiber stops first, error or not; every other
/// one is cancelled. Parks on `wait_any` until a contestant stops, so a
/// win is seen as soon as it happens rather than up to a millisecond
/// late, and a race held open by sleepers costs no timer wakeups.
///
/// On the Rust host `wait_any` answers `none` (it cannot park), so this
/// reports `err cancelled` there; `combine_test.mo`'s lazy-host
/// expectations are written against that.
///
/// A cancelled loser stops at its next IO bind (cancellation is
/// cooperative), so nothing waits for it and no later side effect runs.
/// Racing zero fibers has no value of `A` to hand back; callers pass at
/// least one fiber.
///
/// The continuation is spelled `fn idx => race_pick … idx`, NOT
/// `race_pick (Shared.of fibers)` as a partial application, and that is
/// LOAD-BEARING rather than stylistic: codegen's IO-bind fusion
/// (`io_bind_plan`) only claims a bind whose continuation is a literal
/// lambda. A partial application falls through to `IO.bind`'s reference
/// body, which `match`es its first argument -- and when this fiber is
/// cancelled, `wait_any` answers the cancellation sentinel rather than an
/// `IO` box, so that match dereferences a non-object and the fiber
/// SEGFAULTS instead of unwinding. See
/// `plans/implementations/2026-11-15-unfused-io-bind-dereferences-the-cancel-sentinel.md`.
pub def race (fibers : List (Fiber A)) : IO (Result FiberError A) :=
    Monad.bind (wait_any fibers) (fn idx => race_pick (Shared.of fibers) idx)

/// The outcome of a bounded wait: the fiber finished (with its own result),
/// or the duration expired first.
pub type Timeout A {
    finished (result : Result FiberError A),
    expired
}

/// Wait at most `duration` for `f`, racing a sleeper against a fiber that
/// awaits it. The waiter is listed first so the lazy host -- where a poll
/// runs the deferred action -- degrades to `await_fiber`, its only honest
/// behaviour; the compiled backend races them for real.
///
/// `expired` cancels `f` cooperatively (it stops at its next IO bind) and
/// cancels the waiter, which may itself stay blocked in `await_fiber f`
/// until `f` finishes; nothing waits for either, and `timeout` returns as
/// soon as the timer wins.
///
/// STILL THREE THREADS, deliberately, and P1 did not change that: `race`
/// no longer polls, so a bounded wait costs no timer WAKEUPS any more, but
/// the timer is still a fiber. Retiring it needs NO event loop: `wait_any`
/// already parks on a condvar, so a `pthread_cond_timedwait` deadline on
/// that same park expires the timer inline. What actually stops it is that
/// `wait_any` answers an INDEX, so an expired deadline has no value that
/// cannot be confused with a contestant; the fix is a second timeout-aware
/// primitive (or a distinct sentinel) plus deciding what `race` does with
/// `-1`. Not attempted here because nothing in the tree uses `timeout` for
/// real work -- `motes/moon` uses `SO_RCVTIMEO`, `motes/moose` its own
/// connect deadline -- so it would be speculative churn on a path with no
/// caller (`monad-fiber-scheduler.md`'s P4 scope note).
pub def timeout {A : Type} (duration : Combine.Duration) (f : Fiber A) : IO (Result FiberError (Timeout A)) := do {
    let waiter <- forkIO (fn (_ : Unit) => do {
        let r <- await_fiber f;
        return (Timeout.finished r)
    });
    let timer <- forkIO (fn (_ : Unit) => do {
        sleepIO duration.millis;
        return Timeout.expired
    });
    race [waiter, timer]
}

// Scoped: run f with a scope; all fibers forked via scope_fork
// are cancelled when the scope exits.
def scoped (f : FiberScope -> IO A) : IO A := do {
    let scope <- scope_new;
    let ss := Shared.of scope;
    let result <- f (Shared.get ss);
    scope_drop scope;
    return result
}
