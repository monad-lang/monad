#![mote { name := "wasm_wasi_async" }]

// `monad-fiber-scheduler.md` P1's two new natives, at the wasm gate.
//
// `wasi_fiber.mo` pins `fork_io`; this pins the pair that replaced the
// poll loops, because a native that is reachable from `std/` and NOT in
// `wasm_os_only_natives` (`codegen/src/natives.mo`) would compile to a
// stub on a profile with no threads instead of failing loudly. Both are
// reachable here through their `pub` wrappers, so the target gate has to
// name whichever it meets first.
//
// Each wrapper's argument is a PARAMETER rather than a value built here,
// so `main` never has to name a `Fiber`/`Channel` twice (those are affine)
// and the only diagnostics this fixture can produce are the target ones
// it exists for.
use std::concurrent::channel {Channel, select}
use std::concurrent::fiber {Fiber, wait_any}

/// `wait_any` parks a fiber until one of a set stops; there is nothing to
/// park on where there are no threads.
def wait_any_reachable (fs : List (Fiber I64)) : IO I64 :=
    IO.bind (wait_any fs) (fn (_ : Option I64) => IO.pure 0)

/// `select` is `channel_take_any`, which parks on the same primitive.
def select_reachable (chs : List (Channel I64)) : IO I64 :=
    IO.bind (select chs) (fn (_ : Option I64) => IO.pure 0)

/// Reaching either wrapper is enough to make its native reachable, so
/// `main` takes the list it hands over instead of building one.
def main (args : List String) : IO I64 := do {
    let _ <- wait_any_reachable (List.empty : List (Fiber I64));
    select_reachable (List.empty : List (Channel I64))
}
