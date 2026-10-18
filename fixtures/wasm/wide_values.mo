#![mote { name := "wasm_wide_values" }]

open IO {println}

/// `add n` captures `n` in a closure env slot; `some n` stores it in a
/// constructor field. Both slots are 8-byte words, so a value above 2^32
/// must survive a round trip through each on wasm32.
def add (a : I64) : I64 -> I64 := fn b => a + b

def maybe_big : Option I64 := some 5000000000

def main (args : List String) : IO I64 :=
    match maybe_big {
        some n => IO.bind (println (I64.to_string (add n 123))) (fn _ => IO.pure 0),
        none => IO.pure 1
    }
