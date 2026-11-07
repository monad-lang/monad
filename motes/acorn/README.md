# acorn

A static book/site generator built on Oak, mdBook-compatible: chapters come
from `SUMMARY.md` and render to `<out>/<book dir>/<chapter>.html`, with a
sidebar, prev/next pager, on-page TOC, heading self-links, GFM admonitions, a
`monad` syntax highlighter (`motes/fmt`), and a broken-internal-link gate that
fails the build before writing anything.

```bash
monad build motes/acorn -o target/acorn
target/acorn build                  # reads docs/site.toml, writes docs/public
target/acorn build --out /tmp/site  # override the output root
monad test motes/acorn
```

`acorn` is the **generic** builder: it renders the book in acorn's own plain
chrome (`Shell.default`) and has no landing page. A site supplies its own
chrome and extra pages through `Site.build_with`; monad-lang.org's live in
`docs/site/monad_website`, which is the binary `scripts/build-docs.sh` runs.
Plan: `plans/implementations/2026-11-05-acorn-docs-site.md`.
