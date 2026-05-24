// Structured concurrency combinators: all, race, scoped, sleepIO, Duration.
// Builds on forkIO/await_fiber/cancel_fiber from std.concurrent.fiber.

use std.concurrent.fiber

struct Duration {
    millis : I64,
}

type Scope {
    scope
}

@[native sleep_io]
def sleepIO (ms : I64) : IO Unit

@[native scope_new]
def scope_new : IO Scope

@[native scope_fork]
def scope_fork (s : Scope) (action : Unit -> IO A) : IO (Fiber A)

@[native scope_drop]
def scope_drop (s : Scope) : IO Unit

// Await all fibers in order, collecting results.
def all_aux (fibers : List (Fiber A)) (acc : List A) : IO (List A) :=
  match fibers {
    List.empty => IO.io acc,
    List.cons f rest =>
      Monad.bind (await_fiber f) (fn head =>
        all_aux rest (List.cons head acc))
  }

def all {A : Type} (fibers : List (Fiber A)) : IO (List A) :=
  all_aux fibers List.empty

@[partial]
def cancel_all (fibers : List (Fiber A)) : IO Unit :=
  match fibers {
    List.empty => IO.io Unit.unit,
    List.cons f rest => do {
      let _ <- cancel_fiber f;
      cancel_all rest
    }
  }

// Race: cancel all but the first fiber, await the first.
@[partial]
def race (fibers : List (Fiber A)) : IO A :=
  match fibers {
    List.cons f rest => do {
      let _ <- cancel_all rest;
      await_fiber f
    }
  }

// Scoped: run f with a scope; all fibers forked via scope_fork
// are cancelled when the scope exits.
def scoped (f : Scope -> IO A) : IO A := do {
  let scope <- scope_new;
  let result <- f scope;
  let _ <- scope_drop scope;
  return result
}
