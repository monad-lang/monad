// Fiber type and forkIO/await_fiber/cancel_fiber concurrency primitives.
// Fiber handles are opaque runtime objects; do not pattern match on them.
//
// `pub` so the `cli` mote can import them (`use std::concurrent::fiber
// {...}`) for the test runner's `--jobs` parallelism; the same-mote users
// in `combine.mo` import via `lib::` and are unaffected either way.

pub type Fiber (A : Type) {
  fiber
}

/// Why a fiber has no result to hand back.
pub type FiberError {
  /// `cancel_fiber` (or a dropped scope, or a lost `race`) reached the
  /// fiber before it finished. Cancellation cannot preempt a running
  /// body, so the body may still have run to the end; its result is
  /// discarded either way.
  cancelled,
  /// The runtime could not create the fiber's thread (a thread-count or
  /// address-space limit), so the action never ran.
  never_started
}

/// The natives' error codes, in this order: 1 is `cancelled`, 2 is
/// `never_started`.
pub def FiberError.of_code (code : I64) : FiberError :=
  if I64.beq code 2 then FiberError.never_started else FiberError.cancelled

pub def FiberError.message (e : FiberError) : String :=
  match e {
    FiberError.cancelled => "fiber was cancelled",
    FiberError.never_started => "fiber never started (no thread could be created)"
  }

def fiber_result (r : Result I64 A) : Result FiberError A :=
  match r {
    Result.ok a => Result.ok a,
    Result.err code => Result.err (FiberError.of_code code)
  }

#[native fork_io]
pub def forkIO (action : Unit -> IO A) : IO (Fiber A)

#[native await_fiber]
priv def await_fiber_raw (f : Fiber A) : RawIO (Result I64 A)

// The wrappers bind with an explicit `IO.pure`, not do-notation:
// instantiated at a caller's type variable (tui's `poll_turns {M}`), a
// do-block's `Monad.pure` finds no instance in the self-hosted checker.

/// Wait for the fiber to stop and take its result, or the reason there is
/// none. Awaiting the same fiber again in compiled code returns the same
/// answer; on the Rust host it is an error, because the host runs the
/// action at the first await.
pub def await_fiber (f : Fiber A) : IO (Result FiberError A) :=
  Monad.bind (IO.mk (await_fiber_raw f)) (fn r => IO.pure (fiber_result r))

#[native cancel_fiber]
pub def cancel_fiber (f : Fiber A) : IO Unit

#[native poll_fiber]
priv def poll_fiber_raw (f : Fiber A) : RawIO (Option (Result I64 A))

/// The non-blocking sibling of `await_fiber`: `none` while the fiber
/// still runs, then `some` of exactly what `await_fiber` would answer.
/// A cancelled fiber answers `some (err cancelled)` once it has stopped,
/// never a silent `none`, so a poll loop on an abandoned fiber ends. On
/// the Rust host the action is deferred and asking IS doing: poll runs it
/// to completion and always returns `some`, so no test may assert
/// interleaving through pollFiber there.
pub def pollFiber (f : Fiber A) : IO (Option (Result FiberError A)) :=
  Monad.bind (IO.mk (poll_fiber_raw f)) (fn o => IO.pure (poll_result o))

def poll_result (o : Option (Result I64 A)) : Option (Result FiberError A) :=
  match o {
    Option.none => Option.none,
    Option.some r => Option.some (fiber_result r)
  }
