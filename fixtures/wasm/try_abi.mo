// ABI spike for the /try engine (`plans/` — browser REPL at monad-lang.org/try).
//
// Two things the engine depends on are unproven today:
//   1. a `#[export "c"]` def may take a `String` PARAMETER (every existing
//      fixture exports only i64 words), so JS can stage UTF-8 in linear
//      memory and hand its pointer to `try_run`;
//   2. JS can allocate that staging buffer through the C-only `try_alloc`
//      export (`runtime/src/platform_web.c`), which returns a JS Number.
//
// `try_echo` uses `write_stdout` as the observation channel: if the bytes
// arrive unchanged, the export parameter and the (ptr,len) boundary both
// agree. The harness is `wasm/web/try_abi_smoke.mjs`.

use std::io {IO.write_stdout}

#[export "c"]
def try_echo (source : String) : IO Unit := IO.write_stdout source

def main : IO Unit := IO.pure unit
