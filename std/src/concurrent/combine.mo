// Structured concurrency combinators: all, race, scoped, sleepIO, Duration.
// Builds on forkIO/await_fiber/cancel_fiber from std.concurrent.fiber.

use lib::concurrent::fiber {Fiber, await_fiber, cancel_fiber}

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

// Await all fibers in order, collecting results.
def all_aux (fibers : List (Fiber A)) (acc : List A) : IO (List A) :=
  match fibers {
    List.empty => IO.pure acc,
    List.cons f rest =>
      Monad.bind (await_fiber f) (fn head =>
        all_aux rest (List.cons head acc))
  }

pub def all {A : Type} (fibers : List (Fiber A)) : IO (List A) :=
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

// Race: cancel all but the first fiber, await the first.
//
// `List.empty` is deliberately NOT covered, unlike `all`/`cancel_all`
// above: those have an obviously correct answer for zero fibers (nothing
// to accumulate/cancel), but there is no value of `A` to synthesize for
// the winner of racing zero contestants -- a structural non-totality in
// the API itself, the same shape as `head`/`last` of an empty list, not a
// provable invariant. Callers are expected to pass at least one fiber.
#[allow_incomplete_match "race requires >=1 fiber; no value of A exists for racing zero contestants"]
#[partial]
pub def race (fibers : List (Fiber A)) : IO A :=
  match fibers {
    List.cons f rest => do {
      cancel_all rest;
      await_fiber f
    }
  }

// Scoped: run f with a scope; all fibers forked via scope_fork
// are cancelled when the scope exits.
def scoped (f : FiberScope -> IO A) : IO A := do {
  let scope <- scope_new;
  let result <- f scope;
  scope_drop scope;
  return result
}
