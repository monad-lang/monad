# trellis_ui

The browser half of [trellis](../trellis/README.md): the graph model and its
wire format, the projection from a whole graph to one drawable view, fuzzy
search, and the Oak app that ties them to `oak_ui`'s graph widget.

The library is pure and native-testable; the `trellis_ui` binary is the wasm
app (`scripts/build-trellis-ui.sh`).

| Module | What it gives you |
|---|---|
| `model.mo` | `Trellis.Graph` (modules, declarations with their doc comments, edges, resolution counts) and the `trellis 2` codec: `Trellis.Graph.encode` / `decode` |
| `project.mo` | `Trellis.project graph settings`: visible declarations, keys at a `Trellis.Level`, aggregated edges, focus by depth and direction, grouping, sections over the node cap |
| `docs.mo` | `Trellis.render_docs`: a doc comment's markdown to `Html.Node` (raw HTML off, unsafe links dropped) |
| `fuzzy.mo` | `Fuzzy.search graph query limit external`: tiered, case-insensitive ranking over motes, modules and declarations |
| `app.mo` | the Oak program: search, controls, the graph, a section browser, a detail panel with docs and uses/used-by |
| `main.mo` | the wasm exports and the host that fetches `graph.tsv` |

## The wire format

Line-oriented and tab-separated, because the browser parses the whole graph
on load: splitting lines is about fifty times faster than `Json.parse` at the
type checker's size. `R` roots, `M` modules, `D` declarations, `E` edges
(by index), `S` counts; see the header of `src/model.mo`. Doc comments ride
in the `M` and `D` lines as escaped markdown (`Trellis.escape_field`); a
`trellis 1` file still decodes, without docs.

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

**Sections.** A view over the node cap (500 by default; *Max nodes per view*
picks 100 to 1,000) is not drawn whole. Its nodes are split by the
next-coarser key (declarations by module, modules by mote, motes in plain
chunks), a part bigger than the cap is cut in source order, and the main area
lists the sections to open, with a filter. While a section is open, a bar
above the graph steps to the previous or next one, jumps through a select,
or goes back to the list.

**Docs.** Selecting a declaration or a module shows its doc comment,
rendered, in the detail panel.

**Fit.** The drawing is scaled to the canvas, which fills the window height;
the toolbar's *1:1* shows it at actual size (wheel zoom and drag pan work in
both).

## Validation

```bash
monad test motes/trellis_ui
```
