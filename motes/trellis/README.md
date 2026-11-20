# trellis

A call graph visualizer for Monad code. `trellis` reads one or more motes,
resolves every declaration's references, and lets you browse the result in
the browser by **mote**, **module** or **declaration**, with fuzzy search,
grouping boxes and a focus that follows callers or callees.

The first use case is the type checker:

```bash
scripts/build-trellis-ui.sh            # once: the browser UI, into target-monad/trellis-ui
monad run motes/trellis/src/main.mo -- serve lang
# trellis: 53 modules, ... declarations, ... edges; ... of ... references resolved
# trellis: http://127.0.0.1:8040/
```

Search for `unify` and press Enter: the view switches to declarations,
focused on `unify` and its neighbours, grouped by module. Raise the depth,
follow only callers, add `init`/`std`, or select a module and "Show
contents" to see its declarations.

## Commands

| Command | What it does |
|---|---|
| `trellis extract <mote>... [-o FILE]` | write the graph file (`-` for stdout) |
| `trellis serve <mote>... [--port N] [--ui DIR]` | extract once, then serve the UI, the graph and `/source?m=<module>` (a graph module's file, looked up by module path) |

Both take `--tests` (include `*_tests.mo` and `tests/`), `--no-docs` (leave
doc comments out of the graph file; signatures stay), `--docs-base URL` (link every
declaration to its docgen page) and `--verbose` (`extract`: list every
unresolved reference). A mote is a directory with a `mote.toml`
(`lang`, `motes/oak_ui`) or a workspace member's name (`oak_ui`).

## How it works

| Piece | Where |
|---|---|
| Loading: each file with the compiler's strict parser, imports through the compiler's own loader (one shared cache) | `src/load.mo` |
| Nodes, references (`lang::use_completeness::decl_refs`), import-aware resolution | `src/extract.mo` |
| Doc comments and signatures, with docgen's own scan (`DocExtract.extract_source_as`) | `src/docs.mo` |
| The graph model, `trellis 3` wire format, projection, fuzzy search, the Oak app | [`trellis_ui`](../trellis_ui/README.md) |
| The drawing: `Ui.graph` + `Ui.graph_layout` | [`oak_ui`](../oak_ui/README.md) |

A declaration (`def`, `type`, `struct`, `class`, `instance`, `defmacro`) is a
node; a constructor reference is an edge to its type and a class-method
reference an edge to its class. Every edge records its **axis**: `s` when
the name is written in the declaration's signature, `b` in its body.

References are resolved at parse level: a written name is looked up in an
index of every declared name and, when several modules declare it, ranked by
the referring module's own `use` lines, its mote, and the ambient
`init`/`std`. A tie or an unknown name is counted as unresolved, never
guessed.

## Limits

- `x.f` method sugar and instance dispatch need the receiver's type, so
  they stay unresolved (the `S` line of the graph file counts them).
  Typed resolution through the elaborated scope is the follow-up.
- Doc comments are read for every module, external ones included, and
  shown in the UI's detail panel; only the links to published pages
  follow docgen's page scheme (`<mote>/<module>.html#<kind>.<name>`)
  and need a published docs base (`--docs-base`).

## Future: proofs

The schema already carries what a proof inspector needs: each declaration's
attributes (`#[proof]`, `#[theorem]`) and declared result sort (`Prop`), and
each edge's axis. Read on a theorem, signature edges are "the statement
depends on" and body edges "the proof uses". The UI's **proof lens** marks
proof-shaped declarations and dims the rest; `trellis serve proofs` works
because loading does not type-check.

## Validation

```bash
monad test motes/trellis motes/trellis_ui
node wasm/web/smoke/trellis_ui_smoke.mjs <trellis_ui.wasm>   # via scripts/check-wasm-target.sh
```
