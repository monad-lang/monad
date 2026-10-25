# oak

Type-safe HTML views for Monad: Elm-shaped builders over the shared
`xml_html` markup core, an indexed page-assembly transformer, a
host-agnostic model/update/view layer, and an SSR adapter for `http`.

The pure builder is the primary API. Nothing here performs I/O except
`Render.io`, `PageM` and `Ssr.render_io`.

## Layers

| Layer | File | What it gives you |
|---|---|---|
| Builders | `src/elements.mo` | `Html.div [attrs] [children]`, `Html.text`, curated attributes, `Html.attr`/`Html.bool_attr` for the rest, `Html.document`/`document_with`/`document_utf8`. |
| Page assembly | `src/html_t.mo` | `HtmlT M I J A`, an index-tracking transformer (`Open`/`Sealed`/`Emitted`) that accumulates `<head>`/`<body>` nodes; `PageM` is the production stack (`ResultT String IO`). |
| App model | `src/app.mo` | `Program` (init/update/view), `Command` (`none`/`quit`/`dispatch`/`perform`), `Host` (effect interpreter), `Program.run_batch` (a batch fold that drains deferred dispatches). |
| SSR | `src/ssr.mo` | `Ssr.render_page`/`render_body`/`to_response`/`to_response_node`/`fragment_response`/`render_io`: an Oak page or fragment to an `http.Response`. |
| Markup types | re-exported from `xml_html` | `Html.Node`, `Html.Attr`, `Html.to_string`, `Html.beq`. |

## Example

```monad
#![mote { name := "hello_page", deps := [oak, xml_html] }]

use oak::elements {Html.class_, Html.div, Html.h1, Html.p, Html.text}
use xml_html::html {Html.Node}

def view : Html.Node :=
    Html.div [Html.class_ ["card"]]
        [Html.h1 List.empty [Html.text "Hello"],
         Html.p List.empty [Html.text "from Oak"]]

def main : IO Unit := IO.write_stdout (Html.to_string view)
```

`Html.*` builders come from `oak::elements` (or `use oak` for the whole
re-export hub). Attribute names that are Monad keywords take a trailing
underscore: `class_`, `type_`, `for_`, `open_`, `method_`, `name_`.

## Lists and identity

`Html.key k` stamps a list child with `data-oak-key="k"`. A list whose
children all carry a *distinct* key is reconciled by key by `oak_wasm`'s
diff, so reordering preserves the DOM nodes; see
`../oak_wasm/README.md`.

## Validation

```bash
monad test motes/oak
monad check motes/oak
```

The `Program`/`HtmlT` suites run as `#[test]` defs under `src/tests/` and
are executed by CI's self-hosted web-stack step.

## Limits

- `Html.Node.node_fragment` renders flat as a string, but the browser
  runtime mounts it in one `data-oak-fragment` wrapper element so every
  rendered node maps to exactly one DOM node (the path model depends on
  it). A fragment therefore has no node identity of its own when hydrated.
- Page assembly is for whole documents, not subtrees: `HtmlT` has no
  `element`/`collect` over `List (HtmlT ...)`, because a throwaway page
  would discard head writes.
- No pretty-printing, SVG namespaces, typed URLs or streaming rendering.
