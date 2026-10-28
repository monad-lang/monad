# markdown

A CommonMark 0.31.2 + GFM Markdown parser, an `Html.Node` renderer, and the
AST a consumer can render its own way.

- **Total.** Any byte sequence parses to a `Document`: there is no
  `ParseError`, no `Result`, and no failure branch. Pathological nesting
  degrades to literal text at `Options.max_depth` rather than erroring.
- **Renderer-neutral.** The AST records source-faithful details (bullet
  markers, ordered delimiters, raw HTML) and no positions.
- **One HTML target.** `to_html` produces `motes/xml_html` nodes, so Markdown
  composes with [oak](../oak) and the site/doc generators without a second
  serializer.

## Usage

```monad
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.to_html}
use markdown::options {Markdown.site_options}

def render (src : String) : Html.Node :=
    Markdown.to_html (Markdown.parse_with Markdown.site_options src)
```

`Markdown.parse` uses the defaults: GFM on, frontmatter off. Presets:
`default_options`, `commonmark_options` (strict CommonMark),
`site_options` (GFM plus frontmatter). Frontmatter is delimiter splitting
only -- the literal is preserved and never interpreted.

## Tests

```bash
monad test motes/markdown                      # unit tests + conformance
target-rust/release/monad-rs test motes/markdown
```

The conformance gate renders every CommonMark 0.31.2 example with
`commonmark_options` and compares byte for byte against the spec's expected
HTML. The report prints the first failures and a per-section table.

## Layout

| Module | Role |
|---|---|
| `types.mo` | AST, frontmatter types, hand-rolled equality, block constructors |
| `options.mo` | `Options`/`HtmlOptions` and the presets |
| `scan.mo` | suffix cursor, UTF-8 width and decoding, line splitting |
| `block.mo` | cmark's open-block stack: containers, leaf blocks, tight/loose |
| `block_html.mo` | the seven HTML block kinds |
| `refs.mo` | link reference definitions: extraction, hoisting, lookup |
| `inline.mo` | the inline pass: escapes, code spans, emphasis, links |
| `inline_html.mo` | autolinks and raw inline HTML |
| `link_syntax.mo` | labels, destinations, titles |
| `gfm_table.mo`, `gfm_autolink.mo` | the GFM extensions that need their own scanners |
| `href.mo` | cmark-compatible URL percent-encoding |
| `html.mo` | AST to `Html.Node`, matching cmark's block formatting |
| `entities.mo`, `unicode.mo` | generated tables (`tools/`) |

## Generating the tables

```bash
python3 -I tools/gen_entities.py --entities entities.json --out src/entities.mo
python3 -I tools/gen_unicode.py \
    --unicode-data UnicodeData.txt --case-folding CaseFolding.txt --out src/unicode.mo
```

The inputs are fetched from the URLs recorded in each script (with their
SHA-256 in the generated header); the generated files are committed.

## Limits

- No footnotes, definition lists, math, GFM alerts, or smart punctuation.
- Raw HTML is escaped by default; `HtmlOptions.allow_raw_html` passes it
  through as `Html.Node.node_raw_html`.
- Reference-style links normalise to inline links; image alt text is
  flattened to a `String`.
- `motes/markdown` is not a compiler input: it is loaded through the mote
  system like every other library.
