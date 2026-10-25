# The web profile: loader, runtime and an Oak SPA

The `wasm32-unknown-unknown` ("web") profile produces a freestanding
`.wasm` that a browser page instantiates with a JS import object.

## Files

| File | What it is |
|---|---|
| `web.js` | **Generated** by `examples/gen_web_js.mo` from `WebAbi` (`motes/web_wasm/src/web_abi.mo`). It builds the import object and exports `start(url, selector)`. Do not edit: `motes/web_wasm`'s drift test compares the committed file with the generator's output. Regenerate by building the generator and running the binary (`monad build examples/gen_web_js.mo -o /tmp/gen_web_js && /tmp/gen_web_js > wasm/web/web.js`) — `monad run` prints compile status on stdout. |
| `web_runtime.js` | The hand-written host behind those imports: DOM node table and reads (`nodeType`/lowercase `tagName`/form `value`/selector `query`), fetch, storage, console/stdin, `F64.to_string` (the freestanding profile's float formatter), the `Keep` state slot and the `requestAnimationFrame` tick loop. |
| `float_format.js` | The `F64.to_string` spelling (shortest round-trip decimal, positional, Rust-compatible), shared by `web_runtime.js`, `main.js` and `smoke.mjs`. |
| `stub_dom.mjs` | The stub DOM every Node harness drives the real runtime over. Its `insertBefore` detaches a moved node (as the real DOM does), which the keyed diff's `move` relies on. |
| `main.js` | The older direct loader for a plain program (`monad_main`); still used by `?autorun=1&render=1` browser proofs. |
| `smoke.mjs` | Node smoke test for `monad_main` (hello/wide-value fixtures). |
| `export_smoke.mjs` | Node test for `#[export "c"]`: exports, eager `IO`, the exports-only module, and the `Keep` slot. |
| `dom_smoke.mjs` | Node test driving `fixtures/wasm/web_dom.mo` through `web.js` + `web_runtime.js` over the stub DOM, including the read-only introspection report. |
| `spa_smoke.mjs` | Node test driving `fixtures/wasm/oak_spa.mo` (mount → two clicks → tick → patch → reset), including the hydration root-mismatch fallback. |
| `nested_spa_smoke.mjs` | Node test driving `fixtures/wasm/oak_spa_nested.mo`: a dynamic list at patch path length 3 (the `Patch.drop_last` regression). |
| `hydrate_smoke.mjs` | Node test that seeds the nested fixture's exact SSR markup and asserts hydration adopts it by identity (0 creates), corrects attributes, trims surplus nodes, and still patches. |
| `keyed_spa_smoke.mjs` | Node test driving `fixtures/wasm/oak_spa_keyed.mo`: reverse/insert/delete keep the same DOM nodes. |

## Running an SPA

A program exposes three `#[export "c"]` thunks and calls `motes/oak_wasm`'s
runtime (`fixtures/wasm/oak_spa.mo` is the worked example):

```monad
#[export "c"]
def oak_mount : IO Unit := Runtime.mount init view

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch decode handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host
```

```bash
monad build --target wasm32-unknown-unknown fixtures/wasm/oak_spa.mo -o app.wasm
```

```html
<script type="module">
  import { start } from './web.js';
  start('./app.wasm', '#app');
</script>
```

`start` sets the mount selector, instantiates the module with the generated
import object, calls `oak_mount()` and starts the tick loop. On every frame
`oak_tick` folds queued messages, re-renders and patches the DOM; DOM
listeners registered from `data-oak-on-<event>` attributes call
`oak_dispatch_event(id)`.

## Checking

`scripts/check-wasm-target.sh` builds and runs every one of these (it needs
`WASI_SDK_PATH`, `node` and `wasmtime`), and runs in CI as the WASM target
proof.
