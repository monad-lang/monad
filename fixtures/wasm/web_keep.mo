// The export-call state slot (`web_wasm.Keep`): `probe_set` stashes a `Ref`
// in the JS host, `probe_get` reads it back in a later export call and logs
// the value. This is the mechanism a SPA's mount/dispatch/tick exports use,
// since the export ABI carries only i64 words.
//
// `wasm/web/export_smoke.mjs <wasm> keep` drives it.

#![mote { name := "web_keep", deps := [web_wasm] }]

use std::ref {Ref, Ref.get, Ref.new}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::console {Console.log}

#[export "c"]
def probe_set : IO Unit := do {
    let r <- Ref.new 41i64;
    let _ <- Keep.save r;
    return unit
}

#[export "c"]
def probe_get : IO Unit := do {
    let r <- Keep.load;
    let v <- Ref.get r;
    let _ <- Console.log (I64.to_string v);
    return unit
}
