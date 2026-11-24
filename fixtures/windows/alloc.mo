#![mote { name := "alloc", deps := [init] }]

// The claim `windowsShim`'s static `-lgc` exists to make: the collector WORKS
// on this target. 3000 appends of 20 bytes is 60 KiB of live data built out of
// far more garbage, so a heap that is not being collected -- or a recursion
// that did not run to completion -- cannot reach the size the gate asserts.
// A load-time `libgc-1.dll` failure leaves the marker missing instead.
open IO {println}

#[decreasing n]
def grow (n : I64) (s : String) : String :=
    if I64.lt n 1 then s else grow (n - 1) (s ++ "xxxxxxxxxxxxxxxxxxxx")

def main (args : List String) : IO Unit :=
    println (grow 3000 "allocprobe-ok")
