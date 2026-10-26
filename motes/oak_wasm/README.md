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
def oak_mount : IO Unit := Runtime.mount prog

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
```

The loader calls `oak_mount` once, `oak_dispatch_event(id)` from each DOM
listener, and `oak_tick` once per animation frame. The runtime's state
lives in the `web_wasm.Keep` slot (the export ABI carries only i64 words).

## Event handlers

Handlers are pure functions in the typed view; there is no decoder:

```monad
Html.button [Html.on_click Msg.increment] [Html.text "add"]
Html.div [Html.on_dragover Msg.over, Html.drop_effect "copy",
          Html.on_drop (fn (e : WebEvent) => Msg.dropped e.data)] [...]
Html.input [Html.on_input (fn (s : String) => Msg.set_text s)]
```

`Oak.lower` turns each `Oak.Attr.on` into `data-oak-on-<event>="<hex-id><:flags>"`
and collects the handler table. The id is derived from the node's patch
path + event name, so it is stable across renders; the JS host keeps the DOM
listener in step (replace on change, remove when the attribute goes away) and
`Runtime.dispatch` looks the id up, snapshots the live event into a
`web_event::WebEvent`, and runs the pure handler. The `HandlerResult` it returns
decides `preventDefault`/`stopPropagation`, applied while the browser is
still dispatching.

Outgoing effects are declarative: `Html.drag_payload`, `Html.drag_effect`,
`Html.drop_effect`, `Html.copy_text` render `data-oak-*` attributes the host
honours during the event. `Html.on_dragover` and `Html.on_drop` set the
preventDefault flag (a drop target must prevent default).

## Subscriptions

`Program.with_subs init update view subs` adds Elm's `Sub msg` (spelled `Subscription` here):

```monad
def subs (_m : Model) : List (Subscription Msg) :=
    [ Subscription.window_msg "resize" Msg.resized,
      Subscription.document_msg "visibilitychange" Msg.hidden,
      Subscription.animation_frame_msg Msg.frame ]
```

The runtime diffs the list by (target, event) after every batch and
registers/unregisters the difference. `animation_frame` is dispatched by the
loader's `requestAnimationFrame` loop just before `oak_tick`, so a frame
message is folded in the same frame.

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
`hydrate_smoke.mjs`, `oak_event_smoke.mjs` (typed handlers, drag/drop,
clipboard), `event_smoke.mjs` (the raw snapshot), `clipboard_smoke.mjs`
(async clipboard) and `subs_smoke.mjs` (window/document/frame).
`scripts/check-wasm-target.sh` builds and runs them (all of it runs in CI).
