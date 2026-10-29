// Structured concurrency combinators: all, race, timeout, scoped, sleepIO,
// Duration.
// Builds on forkIO/await_fiber/cancel_fiber from std.concurrent.fiber.

use init::shared {Shared, Shared.get}
use lib::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, forkIO, pollFiber}

// `Combine.Duration`, not `Duration`: `motes/time` declares a `pub Duration`
// (seconds and nanos) and whole-program qualification makes the bare name
// ambiguous, so the literal `{ millis := 300 }` resolved to the wrong one.
// Same reason `FiberScope` below carries a namespace note.
struct Combine.Duration {
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

// The answer of the first fiber in `fibers` that has stopped, polling
// each once in list order; `none` while every one is still running.
def poll_first (fibers : List (Fiber A)) : IO (Option (Result FiberError A)) :=
  match fibers {
    List.empty => IO.pure Option.none,
    List.cons f rest =>
      Monad.bind (pollFiber f) (fn done =>
        match done {
          Option.some a => IO.pure (Option.some a),
          Option.none => poll_first rest
        })
  }

// The race loop reads the contestant list every round and cancels it at
// the end, so it threads a `Shared`: `race` hands the list over once.
def race_won (fibers : Shared (List (Fiber A))) (winner : Result FiberError A) : IO (Result FiberError A) :=
  Monad.bind (cancel_all (Shared.get fibers)) (fn _ => IO.pure winner)

#[partial]
def race_step (fibers : Shared (List (Fiber A))) (done : Option (Result FiberError A)) : IO (Result FiberError A) :=
  match done {
    Option.some a => race_won fibers a,
    Option.none => Monad.bind (sleepIO 1) (fn _ => race_loop fibers)
  }

#[partial]
def race_loop (fibers : Shared (List (Fiber A))) : IO (Result FiberError A) :=
  Monad.bind (poll_first (Shared.get fibers)) (race_step fibers)

/// The answer of whichever fiber stops first, error or not; every other
/// one is cancelled. Waits by polling the contestants every millisecond, so a
/// win is seen at most about 1 ms late. On the Rust host polling runs a
/// fiber to completion, so the first fiber in the list always wins there.
/// A cancelled loser stops at its next IO bind (cancellation is
/// cooperative), so nothing waits for it and no later side effect runs.
/// Racing zero fibers never returns: there is no value of `A` to hand
/// back. Callers pass at least one fiber.
#[partial]
pub def race (fibers : List (Fiber A)) : IO (Result FiberError A) :=
  race_loop (Shared.of fibers)

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
  let result <- f scope;
  scope_drop scope;
  return result
}
