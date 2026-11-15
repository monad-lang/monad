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
    /// fiber before it finished. Cancellation is cooperative: the body
    /// stops at its next IO bind (a native or pure computation already in
    /// progress finishes), and its result is discarded either way.
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
priv def fork_io_raw (action : Unit -> IO A) : RawIO (Fiber A)

pub def forkIO (action : Unit -> IO A) : IO (Fiber A) := IO.mk (fork_io_raw action)

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
priv def cancel_fiber_raw (f : Fiber A) : RawIO Unit

pub def cancel_fiber (f : Fiber A) : IO Unit := IO.mk (cancel_fiber_raw f)

#[native fiber_wait_any]
priv def fiber_wait_any_raw (fibers : List (Fiber A)) : RawIO I64

/// Park until ANY fiber in `fibers` has stopped, then that fiber's INDEX
/// in list order; `none` for an empty list or when the waiting fiber is
/// itself cancelled. The index comes back rather than the answer so the
/// winner is taken through the ordinary `await_fiber` reaping path -- one
/// implementation of that protocol, not two.
///
/// This exists so `race` and `select` stop polling. Both used to
/// re-derive "wait for one of N" as "probe all N, sleep 1 ms, repeat",
/// which cost a timer wakeup per millisecond and delayed a win by up to a
/// millisecond. A fiber that has not started yet (`forkIO` could not get
/// a thread) counts as stopped, so it is picked up immediately rather
/// than waited on forever.
///
/// Compiled-only: the Rust host cannot park (its fibers are deferred
/// thunks), so it answers `-1` and its combinators keep the documented
/// lazy degradation.
pub def wait_any {A : Type} (fibers : List (Fiber A)) : IO (Option I64) :=
    Monad.bind (IO.mk (fiber_wait_any_raw fibers)) (fn i => IO.pure (index_or_none i))

/// The native's `-1` sentinel as `none`; every other value is a real index.
def index_or_none (i : I64) : Option I64 :=
    if I64.lt i 0 then Option.none else Option.some i

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
