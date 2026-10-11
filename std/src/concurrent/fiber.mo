// Fiber type and forkIO/await_fiber/cancel_fiber concurrency primitives.
// Fiber handles are opaque runtime objects; do not pattern match on them.
//
// `pub` so the `cli` mote can import them (`use std::concurrent::fiber
// {...}`) for the test runner's `--jobs` parallelism; the same-mote users
// in `combine.mo` import via `lib::` and are unaffected either way.

pub type Fiber (A : Type) {
  fiber
}

#[native fork_io]
pub def forkIO (action : Unit -> IO A) : IO (Fiber A)

#[native await_fiber]
pub def await_fiber (f : Fiber A) : IO A

#[native cancel_fiber]
pub def cancel_fiber (f : Fiber A) : IO Unit
