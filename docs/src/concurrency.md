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
joins that thread and yields its result.

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
cancellation is a flag that `await_fiber` refuses to hand a result for — the same
observable behaviour as the host, which can only cancel a fiber it has never
started. A `scope_drop` likewise cancels the fibers forked through that scope
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

#[native fork_io]    def forkIO (action : Unit -> IO A) : IO (Fiber A)
#[native await_fiber] def await_fiber (f : Fiber A) : IO A
#[native cancel_fiber] def cancel_fiber (f : Fiber A) : IO Unit
```

Fiber handles are opaque runtime objects — do not pattern match on them.

```monad
use std::concurrent::fiber {await_fiber, forkIO}

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

`sleepIO` is a real blocking sleep (`nanosleep`), so it costs a whole thread
while it runs.

`race` "wins" by taking the head of the list, not by observing which fiber
finishes first. It is therefore deterministic, and it is the right primitive
only when every fiber computes the same thing — `race` is a cancellation
shorthand, not a scheduler. That is a choice in `combine.mo` and not a limit of
the runtime: the threads really do race, this function simply does not look at
who won.

```monad
use std::concurrent::fiber {Fiber, forkIO}
use std::concurrent::combine {all}
use std::list {}

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

## What It Costs

Fiber handles are opaque runtime objects tagged in their header, so a `match` on
one fails loudly rather than reading a heap address as a constructor tag. The
refcount in that header is what keeps a `Scope`'s fibers alive, and it is the
*only* thing in the compiled runtime that uses it — the compiler still emits no
retain/release calls for ordinary values, because deterministic freeing is
blocked on [linear types](./linear-types.md).

A fiber nobody ever awaits or cancels keeps its thread entry until the process
exits: a few hundred bytes each. Reclaiming it would mean joining threads whose
result nobody wants, so `scope_drop` does not.

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

- Compiled `forkIO` starts a real thread; `await_fiber` joins it. That is
  parallelism.
- The host is the lazy one: it defers to the first `await`, so nothing there
  interleaves
- Cancellation is recorded, never preemptive
- `all`, `race`, `scoped`, and `cancel_all` are combinators over either model;
  `race` takes the head rather than observing a winner
- `sleepIO` genuinely sleeps, and holds a thread while it does
- `std/src/concurrent/combine_test.mo` carries the one test that distinguishes
  the two backends

See the [Maturity Matrix](./maturity.md), and
[The Standard Library](./stdlib.md) for what else `std/` provides.
