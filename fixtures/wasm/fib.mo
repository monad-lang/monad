#![mote { name := "wasm_fib" }]

open IO {println}

/// The Phase 0 differential fixture: the same source compiles natively and
/// to wasm32-unknown-wasip1, and both must print 832040 and exit 0.
#[decreasing n]
def fib (n : I64) : I64 :=
    if n < 2 then n else fib (n - 1) + fib (n - 2)

def main (args : List String) : IO I64 :=
    IO.bind (println (I64.to_string (fib 30))) (fn _ => IO.pure 0)
