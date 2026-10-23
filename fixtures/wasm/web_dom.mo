// The `web_wasm` DOM surface, end to end: mount a text node under the
// root. `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/dom_smoke.mjs` instantiates it against the real
// `wasm/web/web_runtime.js` over a stub DOM, which is what proves the
// externs, the C wrappers and the JS host agree.

#![mote { name := "web_dom", deps := [web_wasm] }]

use web_wasm::dom {Dom.append, Dom.create, Dom.root, Dom.set_attr, Dom.text_node}

def main : IO Unit := do {
    let root <- Dom.root;
    let greeting <- Dom.text_node "hello from wasm";
    let block <- Dom.create "div";
    let _ <- Dom.set_attr block "id" "probe";
    let _ <- Dom.append block greeting;
    let _ <- Dom.append root block;
    return unit
}
