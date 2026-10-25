// Structured concurrency combinators: all, race, scoped, sleepIO, Duration.
// Builds on forkIO/await_fiber/cancel_fiber from std.concurrent.fiber.

use init::borrow {Borrow, Borrow.get}
use lib::concurrent::fiber {Fiber, FiberError, await_fiber, cancel_fiber, pollFiber}

struct Duration {
    millis : I64,
}

// `FiberScope`, not `FiberScope`: lang/types.mo also declares a `FiberScope`, and
// whole-program qualification (plan item 5.1) makes that bare name ambiguous.
type FiberScope {
    scope
}

#[native sleep_io]
pub def sleepIO (ms : I64) : IO Unit

#[native scope_new]
def scope_new : IO FiberScope

#[native scope_fork]
def scope_fork (s : FiberScope) (action : Unit -> IO A) : IO (Fiber A)

#[native scope_drop]
def scope_drop (s : FiberScope) : IO Unit

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
// the end, so it threads a `Borrow`: `race` hands the list over once.
def race_won (fibers : Borrow (List (Fiber A))) (winner : Result FiberError A) : IO (Result FiberError A) :=
  Monad.bind (cancel_all (Borrow.get fibers)) (fn _ => IO.pure winner)

#[partial]
def race_step (fibers : Borrow (List (Fiber A))) (done : Option (Result FiberError A)) : IO (Result FiberError A) :=
  match done {
    Option.some a => race_won fibers a,
    Option.none => Monad.bind (sleepIO 1) (fn _ => race_loop fibers)
  }

#[partial]
def race_loop (fibers : Borrow (List (Fiber A))) : IO (Result FiberError A) :=
  Monad.bind (poll_first (Borrow.get fibers)) (race_step fibers)

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
  race_loop (Borrow.of fibers)

// Scoped: run f with a scope; all fibers forked via scope_fork
// are cancelled when the scope exits.
def scoped (f : FiberScope -> IO A) : IO A := do {
  let scope <- scope_new;
  let result <- f scope;
  scope_drop scope;
  return result
}
