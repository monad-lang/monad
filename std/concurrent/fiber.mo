// Fiber type and forkIO/await_fiber/cancel_fiber concurrency primitives.
// Fiber handles are opaque runtime objects; do not pattern match on them.

type Fiber (A : Type) {
  fiber
}

@[native fork_io]
def forkIO (action : Unit -> IO A) : IO (Fiber A)

@[native await_fiber]
def await_fiber (f : Fiber A) : IO A

@[native cancel_fiber]
def cancel_fiber (f : Fiber A) : IO Unit
