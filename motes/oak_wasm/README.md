# oak_wasm

The browser runtime for an Oak `Program`: a pure diff over `Html.Node`, a
DOM applier, and the mount/dispatch/tick loop an app exposes to
`wasm/web/web.js` through three `#[export "c"]` thunks.

Every browser call goes through `web_wasm`'s `Dom`/`Keep` wrappers
(`oak_wasm` declares no web externs of its own). The mote is
`targets = ["web"]`, but the pure diff tests run on every target.

## App contract

```monad
#[export "c"]
def oak_mount : IO Unit := Runtime.mount init view

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch decode handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
```

The loader calls `oak_mount` once, `oak_dispatch_event(id)` from each DOM
listener, and `oak_tick` once per animation frame. The runtime's state
lives in the `web_wasm.Keep` slot (the export ABI carries only i64 words).

## Event handlers

An element registers a listener with an ordinary attribute:
`Html.attr "data-oak-on-click" "3"`. The JS host keeps the DOM listener in
step when the value changes and removes it when the attribute goes away,
so a re-render can never stack listeners. The value is the numeric message
id passed to `runtime dispatch decode`.

## Patch

`Patch.diff old new` produces a list of `Patch` values at absolute
`childNodes` paths from the mount container (`[0]` is the view root):

| Patch | Meaning |
|---|---|
| `set_text`, `set_attr`, `remove_attr` | in-place update |
| `replace` | mount a fresh node and swap it in |
| `insert`, `remove`, `move` | structural change (keyed lists) |

Attributes diff by name. Children reconcile one of two ways:

- **Positional** -- when the child count is unchanged, children diff by
  index; a count change, a tag change, or text/raw-text content replaces
  that node.
- **Keyed** -- when *every* child on both sides carries a distinct
  `data-oak-key` (`Html.key`), children are matched by key: a reorder
  MOVES the existing DOM nodes, an insertion mounts one, a deletion
  removes one. Node identity (focus, scroll, listeners, transitions)
  survives a reorder. Duplicate keys, or any unkeyed child, fall back to
  the positional behavior.

Apply order is the invariant the generator relies on: every patch is
applied to the DOM left by the previous one, and each apply performs one
DOM mutation after resolving its indices.

## Hydration

`Runtime.mount` ADOPTS a matching server-rendered tree instead of clearing
it, so the first paint does not flash and node state survives. A live node
is reused when its `nodeType` and lowercase `tagName` match; its
attributes are set from the view, its children adopted recursively, and
surplus children trimmed. If the root does not match, the runtime clears
and mounts.

The contract, and its limits:

- the mount container holds the SSR view root and nothing else, selected
  explicitly (not `body`);
- the markup must be the serializer's exact output -- matching is
  positional over `childNodes`, so added whitespace shifts every index;
- an SSR-only attribute cannot be removed (there is no attribute
  enumeration); `data-oak` annotations are cleaned explicitly;
- a fragment never adopts (it mounts in its `data-oak-fragment` wrapper).

## Tests

```bash
monad test motes/oak_wasm      # pure diff/hydration-predicate tests
```

The DOM half is covered end to end by the Node harnesses in `wasm/web/`,
which drive real web-profile modules over a stub DOM:
`spa_smoke.mjs`, `nested_spa_smoke.mjs`, `keyed_spa_smoke.mjs`,
`hydrate_smoke.mjs`. `scripts/check-wasm-target.sh` builds and runs them
(all of it runs in CI).
