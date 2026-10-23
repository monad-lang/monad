// An exports-only module: no `def main`, so the runtime's weak `main_monad`
// reference is 0 and `monad_web_entry` returns without calling. This is the
// SPA shape -- JS drives the exports, not the runtime entry.
//
// `scripts/check-wasm-target.sh` builds it and `wasm/web/export_smoke.mjs`
// asserts that `only_add` is exported and that `monad_main` is harmless.

#[export "c"]
def only_add (a : I64) : I64 := a + 5
