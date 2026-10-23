// `#[export "c"]` probe: the smallest program whose exports JS must see.
//
// `probe_add` pins the pure path (a plain i64 export that returns a
// computed value), and `probe_emit` pins the IO path: a def returning `IO`
// performs its effects when EVALUATED (`monad_io_bind` applies its
// continuation eagerly), and the export returns the resulting `IO.mk`
// box, which JS ignores. `scripts/check-wasm-target.sh` builds this for
// `wasm32-unknown-unknown` and asserts both behaviours from Node.
//
// `main` is still required: `platform_web.c` exports `monad_main`, which
// calls `main_monad`. A trivial one is enough for an exports-only module.

use std::io {IO.println}

#[export "c"]
def probe_add (a : I64) : I64 := a + 1

#[export "c"]
def probe_emit : IO Unit := IO.println "probe"

def main (args : List String) : IO I64 := IO.pure 0
