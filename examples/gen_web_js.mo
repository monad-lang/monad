// Render the browser loader from the ABI spec.
//
//   scripts/gen-web-js.sh [out]        # default wasm/web/web.js
//
// The output is a BUILD ARTIFACT (gitignored), not a checked-in source:
// this program is its only author. `scripts/gen-web-js.sh` builds the
// binary in a temp dir, runs it, and sanity-checks the result; every
// consumer (build-try, check-wasm-target, check-try) calls it first.
//
// Build first, then run the binary: `monad run` prints its compile status
// on stdout, so redirecting it directly would prepend progress lines to
// the generated file. This program is pure except for the write, and it
// never reaches a `web_*` extern, so it builds natively.

#![mote { name := "gen_web_js", deps := [web_wasm] }]

use std::io {IO.write_stdout}
use web_wasm::glue {Glue.loader}
use web_wasm::web_abi {WebAbi.default}

def main : IO Unit := IO.write_stdout (Glue.loader WebAbi.default)
