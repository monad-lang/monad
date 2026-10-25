// Regenerate the browser loader from the ABI spec.
//
//   monad build examples/gen_web_js.mo -o /tmp/gen_web_js --no-cache
//   /tmp/gen_web_js > wasm/web/web.js
//
// Build first, then run the binary: `monad run` prints its compile status
// on stdout, so redirecting it directly would prepend progress lines to
// the generated file.
//
// `wasm/web/web.js` is committed (it is what the page imports) and is
// otherwise treated as build output: `motes/web_wasm`'s drift test compares
// the committed file against `Glue.loader WebAbi.default`, so editing it by
// hand fails the suite. This program is pure except for the write, and it
// never reaches a `web_*` extern, so it builds natively.

#![mote { name := "gen_web_js", deps := [web_wasm] }]

use std::io {IO.write_stdout}
use web_wasm::glue {Glue.loader}
use web_wasm::web_abi {WebAbi.default}

def main : IO Unit := IO.write_stdout (Glue.loader WebAbi.default)
