# acorn

The monad-lang.org site generator, built on Oak. It is replacing Zola (the
landing page) and mdBook (the book under `/docs/`), and will render
docs.rs-style API pages for a mote with runnable examples. Plan:
`plans/implementations/2026-11-05-acorn-docs-site.md`.

```bash
monad build motes/acorn -o target/acorn
target/acorn build                  # reads docs/site.toml, writes docs/public
target/acorn build --out /tmp/site  # override the output root
monad test motes/acorn
```

Phase 0 renders every chapter in `docs/src` to `<out>/docs/<chapter>.html`
(mdBook's URLs) through the Oak page shell in `src/layout.mo`. SUMMARY
navigation, highlighting, the landing page and the cut-over come next.
