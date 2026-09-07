# Concurrency

Monad ships fiber-based concurrency primitives in `std.concurrent`. Read the
constraints in this chapter before designing around them: **this is a
cooperative, lazy simulation of concurrency, not parallelism, and it cannot be
compiled at all.**

The compiler backend wires none of the seven concurrency natives, so any program
that reaches one fails to build. `monad check` accepts such a program — only
`compile` refuses. In practice that means `std.concurrent` is reachable today
only under the [bootstrap host](./bootstrap-host.md)'s interpreter.

## What It Actually Does

`forkIO` does not start anything. It captures the action in an opaque handle and
returns immediately. `await_fiber` is what applies the closure — synchronously,
on the calling thread, the first time it is awaited.

So this:

```monad,ignore
let f <- forkIO action;
let result <- await_fiber f;
```

behaves exactly like calling `action unit` at the point of the `await`. There is
no parallel execution, no scheduler, and no preemption. `cancel_fiber` flips a
state flag; there is no thread to interrupt.

This is still a useful abstraction — deferred computation with a cancellation
token, and a shape that a real scheduler could later be dropped into — but it
will not make anything faster.

## Fibers

`std.concurrent.fiber`:

```monad,ignore
type Fiber (A : Type) {
  fiber
}

#[native fork_io]    def forkIO (action : Unit -> IO A) : IO (Fiber A)
#[native await_fiber] def await_fiber (f : Fiber A) : IO A
#[native cancel_fiber] def cancel_fiber (f : Fiber A) : IO Unit
```

Fiber handles are opaque runtime objects — do not pattern match on them.

```monad
use std.concurrent.fiber {await_fiber, forkIO}

def answer (_ : Unit) : IO I64 := IO.pure 42

#[test]
def test_fork_and_await : IO Bool {
    let f <- forkIO answer;
    let result <- await_fiber f;
    return (result == 42)
}
```

## Combinators

`std.concurrent.combine` builds structured-concurrency combinators on top:

| Function | Type | Behaviour |
|----------|------|-----------|
| `all` | `List (Fiber A) -> IO (List A)` | awaits every fiber, collecting results |
| `race` | `List (Fiber A) -> IO A` | cancels all but the first, awaits the first |
| `scoped` | `(Scope -> IO A) -> IO A` | runs an action with a scope, cancelling its fibers on exit |
| `cancel_all` | `List (Fiber A) -> IO Unit` | cancels each fiber |
| `sleepIO` | `I64 -> IO Unit` | sleeps for that many milliseconds |
| `scope_new` / `scope_fork` / `scope_drop` | | the scope primitives `scoped` is built from |

`sleepIO` is the one primitive here that does something genuinely real: it is a
blocking thread sleep.

Because `race` "wins" by taking the head of the list rather than by observing
which finishes first, it is deterministic — a consequence of there being no
actual concurrency to race.

```monad
use std.concurrent.fiber {Fiber, forkIO}
use std.concurrent.combine {all}
use std.list {}

def answer (_ : Unit) : IO I64 := IO.pure 42

#[test]
def test_all : IO Bool {
    let f1 <- forkIO answer;
    let f2 <- forkIO answer;
    let results <- all [f1, f2];
    return (List.length results == 2)
}
```

`Duration` is defined as a struct wrapping milliseconds, but `sleepIO` currently
takes a bare `I64`.

## Not Available in Compiled Binaries

None of the seven concurrency natives (`fork_io`, `await_fiber`, `cancel_fiber`,
`sleep_io`, `scope_new`, `scope_fork`, `scope_drop`) are wired into the compiler
backend. A program that reaches one fails to build:

```text
error: native `fork_io` is not wired into the native backend
```

This is a deliberate fail-fast gate — the alternative, silently emitting a stub,
has caused real miscompiles before. It does mean that everything in this chapter
type-checks and none of it compiles.

## What Does Not Exist

- OS threads or green threads reachable from Monad code
- A scheduler, work stealing, or preemption
- `async`/`await` syntax
- Channels, mutexes, or semaphores exposed to Monad
- Futures, or any notion of a task completing "later"

The Rust side of the repository does contain a real threaded scheduler
(`core/src/runtime/`, with `scheduler.rs`, `channel.rs`, `mutex.rs`,
`semaphore.rs`, `reactor.rs`), but nothing in `std/concurrent/*.mo` reaches it —
the natives all go through the simpler cooperative path. Treat that code as
groundwork for a future runtime, not as something you can use today.

## Summary

- `forkIO` defers; `await_fiber` runs. There is no parallelism.
- `all`, `race`, `scoped`, and `cancel_all` are real combinators over that model
- `sleepIO` genuinely sleeps
- The LLVM backend implements none of it, and says so at compile time
- A real threaded runtime exists in Rust but is not connected

See the [Maturity Matrix](./maturity.md), and
[The Standard Library](./stdlib.md) for what else `std/` provides.
