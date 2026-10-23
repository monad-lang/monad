// A program that reaches a `web_*` extern and is built NATIVELY. The extern
// has no implementation outside the web profile, so codegen must refuse with
// a diagnostic naming the extern and the target -- not link an undefined
// symbol. `scripts/check-wasm-target.sh` asserts the message.

#![mote { name := "web_extern_native", deps := [web_wasm] }]

use web_wasm::dom {Dom.create}

def main : IO Unit := do {
    let _ <- Dom.create "div";
    return unit
}
