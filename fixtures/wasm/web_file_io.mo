#![mote { name := "wasm_web_file_io" }]

/// Native compiles and runs; the web profile must reject `get_env` with the
/// target-availability diagnostic rather than link a missing symbol.
def main (args : List String) : IO I64 :=
    IO.bind (IO.get_env "HOME") (fn _ => IO.pure 0)
