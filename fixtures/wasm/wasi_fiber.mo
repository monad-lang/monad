#![mote { name := "wasm_wasi_fiber" }]

use std::concurrent::fiber {forkIO, await_fiber}

/// Both wasm profiles must reject `fork_io` (there are no OS threads).
def main (args : List String) : IO I64 :=
    IO.bind (forkIO (fn _ => IO.pure 0))
        (fn f => IO.bind (await_fiber f) (fn _ => IO.pure 0))
