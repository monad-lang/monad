#![mote { name := "wasm_hello" }]

open IO {println}

/// The Phase 2 web-profile fixture: one line of output and exit 0.
def main (args : List String) : IO I64 :=
    IO.bind (println "hello") (fn _ => IO.pure 0)
