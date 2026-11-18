# trellis_ui

The browser half of [trellis](../trellis/README.md): the graph model and its
wire format, the projection from a whole graph to one drawable view, fuzzy
search, and the Oak app that ties them to `oak_ui`'s graph widget.

The library is pure and native-testable; the `trellis_ui` binary is the wasm
app (`scripts/build-trellis-ui.sh`).

| Module | What it gives you |
|---|---|
| `model.mo` | `Trellis.Graph` (modules, declarations, edges, resolution counts) and the `trellis 1` codec: `Trellis.Graph.encode` / `decode` |
| `project.mo` | `Trellis.project graph settings`: visible declarations, keys at a `Trellis.Level`, aggregated edges, focus by depth and direction, grouping, a node cap |
| `fuzzy.mo` | `Fuzzy.search graph query limit external`: tiered, case-insensitive ranking over motes, modules and declarations |
| `app.mo` | the Oak program: search, controls, the graph, a detail panel with uses/used-by |
| `main.mo` | the wasm exports and the host that fetches `graph.tsv` |

## The wire format

Line-oriented and tab-separated, because the browser parses the whole graph
on load: splitting lines is about fifty times faster than `Json.parse` at the
type checker's size. `R` roots, `M` modules, `D` declarations, `E` edges
(by index), `S` counts; see the header of `src/model.mo`.

## Views

- **Level**: motes, modules or declarations. Edges between two nodes are
  aggregated (`weight` = how many references they stand for).
- **Grouping**: boxes by mote, or by module nested in its mote.
- **Focus**: pick a search hit, or select a node and press Focus. Depth
  and direction (callers, callees, both) choose the neighbourhood.
- **Filters**: signature and body references, dependencies (`init`,
  `std`, ...), tests.
- **Lens**: `calls` styles nodes by kind; `proofs` marks propositions and
  `#[proof]` declarations and dims the rest.

A view of more than 250 nodes is refused with a hint rather than drawn.

## Validation

```bash
monad test motes/trellis_ui
```
