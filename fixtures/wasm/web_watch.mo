#![mote { name := "wasm_web_watch" }]

use std::watch {Watch.new}

/// Both wasm profiles must reject `inotify_init` (there is no inotify, and
/// `Watch` is Linux-only) with the target-availability diagnostic rather
/// than link a missing symbol.
def main (args : List String) : IO I64 :=
    IO.bind (Watch.new) (fn _ => IO.pure 0)
