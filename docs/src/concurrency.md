# Concurrency

Monad ships fiber-based concurrency primitives in `std.concurrent`. Read the
constraints in this chapter before designing around them: **the compiled
backend runs fibers on real OS threads, so `forkIO` is genuinely parallel — and
the [bootstrap host](./bootstrap-host.md) is the one that is lazy.**

That is the reverse of how this chapter used to read, and of how most runtimes
work. Both implementations accept the same programs; they differ in what a
`forkIO` means.

## What It Actually Does

`forkIO` starts a thread. It creates a `pthread` running the action, returns an
opaque handle immediately, and the thread proceeds on its own. `await_fiber`
waits for that thread to finish and yields its result, or a `FiberError` saying
why there is none.

```monad,ignore
let f <- forkIO action;
let result <- await_fiber f;
```

Above, `action` is already running by the time `await_fiber` is called, and a
second `forkIO` before the first `await` starts a second thread that really does
overlap with it.

The model is 1:1 pthreads, deliberately: compiled Monad code recurses deeply
(`main` raises `RLIMIT_STACK` to 128 MB), so a small green-thread stack would
overflow on the first recursive helper. Each fiber therefore reserves the same
128 MB of *address* space, committed only as it is touched, so a fiber that does
not recurse deeply costs nothing in RSS. This does not scale to a hundred
thousand fibers, and it is explicitly the interim design — the plan is to
replace the handle's atomic refcount with the ownership discipline in
[Linear & Affine Types](./linear-types.md).

`cancel_fiber` **records** the cancellation; it does not preempt. `pthread_cancel`
would leave Boehm's allocator lock held and the thread unregistered, so the
cancellation is a flag, and `await_fiber` answers a cancelled fiber with
`Result.err FiberError.cancelled` — the same answer as the host, which can only
cancel a fiber it has never started. The other error, `never_started`, means
the runtime could not create the fiber's thread. A `scope_drop` likewise cancels the fibers forked through that scope
rather than waiting on them.

The host's model, for contrast: `forkIO` captures the action and returns, and
`await_fiber` applies the closure synchronously on the calling thread. Nothing
there can interleave or run in parallel, which is why it is the host's
interpreter — not the compiled binary — that cannot make anything faster.

## Which Backend Am I On?

Almost every test in `std/src/concurrent/` passes under both models, because it
awaits the fiber it just forked — a deferred thunk plus an inline await satisfies
those identically. `combine_test.mo`'s
`test_sleepIO_fibers_run_concurrently` is the one that can tell them apart: it
forks four 500 ms sleeps **before awaiting any of them**, and asserts the whole
thing finishes in under 1200 ms.

```text
compiled  -> the sleeps overlap  -> ~500 ms   -> passes
host      -> the sleeps are a sum -> ~2000 ms -> fails
```

That test is therefore a self-hosted-only expectation, and CI's sweep runs it
self-hosted.

## Fibers

`std.concurrent.fiber`:

```monad,ignore
type Fiber (A : Type) {
  fiber
}

type FiberError { cancelled, never_started }

def forkIO (action : Unit -> IO A) : IO (Fiber A)
def await_fiber (f : Fiber A) : IO (Result FiberError A)
def pollFiber (f : Fiber A) : IO (Option (Result FiberError A))
def cancel_fiber (f : Fiber A) : IO Unit
```

`pollFiber` is the non-blocking `await_fiber`: `none` while the fiber runs,
then `some` of the same answer. On the host it runs the deferred action and is
always `some`.

Fiber handles are opaque runtime objects — do not pattern match on them.

```monad
use std::concurrent::fiber {await_fiber, forkIO}

def answer (_ : Unit) : IO I64 := IO.pure 42

#[test]
def test_fork_and_await : IO Bool {
    let f <- forkIO answer;
    let result <- await_fiber f;
    return (match result {
        Result.ok v => v == 42,
        Result.err _ => false
    })
}
```

## Combinators

`std.concurrent.combine` builds structured-concurrency combinators on top:

| Function | Type | Behaviour |
|----------|------|-----------|
| `all` | `List (Fiber A) -> IO (Result FiberError (List A))` | awaits every fiber in order, collecting results; stops at the first error |
| `race` | `List (Fiber A) -> IO (Result FiberError A)` | the answer of whichever fiber stops first; cancels the rest |
| `scoped` | `(Scope -> IO A) -> IO A` | runs an action with a scope, cancelling its fibers on exit |
| `cancel_all` | `List (Fiber A) -> IO Unit` | cancels each fiber |
| `sleepIO` | `I64 -> IO Unit` | sleeps for that many milliseconds |
| `scope_new` / `scope_fork` / `scope_drop` | | the scope primitives `scoped` is built from |

`sleepIO` is a real blocking sleep (`nanosleep`), so it costs a whole thread
while it runs.

`race` polls its contestants every millisecond, so it sees a win at most about
a millisecond late. On the host, polling runs a fiber to completion, so the
first fiber in the list always wins there.

```monad
use std::concurrent::fiber {Fiber, forkIO}
use std::concurrent::combine {all}
use std::list {List.length}

def answer (_ : Unit) : IO I64 := IO.pure 42

#[test]
def test_all : IO Bool {
    let f1 <- forkIO answer;
    let f2 <- forkIO answer;
    let results <- all [f1, f2];
    return (match results {
        Result.ok xs => List.length xs == 2,
        Result.err _ => false
    })
}
```

`Duration` is defined as a struct wrapping milliseconds, but `sleepIO` currently
takes a bare `I64`.

## What It Costs

Fiber handles are opaque runtime objects tagged in their header, so a `match` on
one fails loudly rather than reading a heap address as a constructor tag. The
refcount in that header is what keeps a `Scope`'s fibers alive, and it is the
*only* thing in the compiled runtime that uses it — the compiler still emits no
retain/release calls for ordinary values, because deterministic freeing is
blocked on [linear types](./linear-types.md).

Fiber threads are detached: a fiber that is cancelled, loses a `race` or is
dropped with its scope gives its stack back as soon as its body returns, without
anyone awaiting it.

## What Does Not Exist

- A way to spawn a raw OS thread from Monad code — the only entry point is
  `forkIO`, which gives you a `Fiber`
- A scheduler, work stealing, or preemption
- `async`/`await` syntax
- Channels, mutexes, or semaphores exposed to Monad
- Futures, or any notion of a task completing "later"
- A guarantee about the *order* threads run in, or which of two racing fibers
  finishes first

The Rust side of the repository does contain a real threaded scheduler
(`core/src/runtime/`, with `scheduler.rs`, `channel.rs`, `mutex.rs`,
`semaphore.rs`, `reactor.rs`), but nothing in `std/concurrent/*.mo` reaches it:
the compiler's own runtime is the C one in `runtime/src/runtime.c`. Treat that
Rust code as groundwork for a future runtime, not as something you can use today.

## Summary

- Compiled `forkIO` starts a real thread; `await_fiber` waits for it. That is
  parallelism.
- The host is the lazy one: it defers to the first `await`, so nothing there
  interleaves
- Cancellation is recorded, never preemptive
- `await_fiber`, `pollFiber`, `all` and `race` return a `Result`: a cancelled
  fiber is an error, never a made-up value
- `all`, `race`, `scoped`, and `cancel_all` are combinators over either model;
  `race` returns whichever fiber stops first
- `sleepIO` genuinely sleeps, and holds a thread while it does
- `std/src/concurrent/combine_test.mo` carries the one test that distinguishes
  the two backends

See the [Maturity Matrix](./maturity.md), and
[The Standard Library](./stdlib.md) for what else `std/` provides.
