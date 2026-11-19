// Ownership drop glue on the web profile (`scripts/check-ownership.sh`).
//
// The same shapes as `init/src/ownership_tests.mo`: monomorphic, non-Copy
// types with no nullary constructor are Owned under `MONAD_OWNERSHIP=1`,
// so their cells come from `monad_owned_alloc` and drop glue hands them
// back to the web heap (`gc_wasm.c`). `wasm/web/smoke/ownership_smoke.mjs`
// calls `own_run` and checks the runtime's owned alloc/free counters.

type OwnedBox {
    box (x : I64),
}

type OwnedPair {
    pair (a : OwnedBox) (b : I64),
}

def consume_unused (b : OwnedBox) : I64 := 40

def discard_pair (p : OwnedPair) : I64 := 7

#[partial]
def consume_loop (n : I64) (acc : I64) : I64 :=
    if I64.lt n 1
    then acc
    else consume_loop (n - 1) (acc + consume_unused (OwnedBox.box n) + discard_pair (OwnedPair.pair (OwnedBox.box n) n))

/// `n` iterations; each allocates three Owned cells that drop glue frees.
#[export "c"]
def own_run (n : I64) : I64 := consume_loop n 0

def main (args : List String) : IO I64 := IO.pure 0
