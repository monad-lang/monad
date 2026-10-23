# Documentation

The Monad language site, built with [Zola](https://www.getzola.org/) (landing
page) and [mdBook](https://rust-lang.github.io/mdBook/) (documentation), and
published to <https://monad-lang.org> by `.github/workflows/mdbook.yml` on
every push to `main`.

The landing page lives at `monad-lang.org/` and the documentation book at
`monad-lang.org/docs/`.

```bash
docs-build            # devenv script: build both mdBook and Zola to docs/public
docs-serve            # devenv script: build mdBook, then serve Zola with live reload
```

The Zola project is at `docs/site/` — templates in `docs/site/templates/`,
styles in `docs/site/sass/`, static assets in `docs/site/static/`. mdBook
output goes to `docs/site/static/docs/` (configured via `build-dir` in
`docs/book.toml`), so Zola serves it at `/docs/`.

## Keeping the examples correct

`mdbook build` only renders markdown — it does not compile the Monad inside it.
`scripts/check-docs.sh` does: it extracts every ` ```monad ` block, type-checks
it with the real compiler, and runs as a git hook (and therefore in CI).

Because blocks are checked in isolation, each one must stand on its own — its
own `use`/`open` lines and its own type annotations. A reader copying a block
into a file gets exactly what the checker saw.

Tag a block ` ```monad,ignore ` only when it is deliberately not valid today:
syntax the book documents as unimplemented, or a fragment quoted from the
standard library for illustration. Every ignored block should have prose beside
it saying which.

`docs/src` is opt-out like that, but the two files outside it — `AGENTS.md` and
the root `README.md` — are **opt-in**: a bare ` ```monad ` there is skipped, and
` ```monad,check ` asks for the check. Both are prose rather than sample
programs, so the fences worth compiling are the ones making a claim a reader
copies. Each must contribute at least one checked block, which the script
enforces: for an opt-in file a missing tag is an unchecked claim, not a
deliberate omission, and the README's program sat inside a ` ```bash ` heredoc —
invisible to the extractor — until that pin existed.

## Stale after the mote conversion

The mote workspace conversion landed after this book was rewritten, so a few
sections describe the world it replaced. Each is true of neither compiler now,
and none is a code-block failure — `check-docs.sh` stays green, because what
went stale is prose. For the next doc pass:

- `modules.md`, "How Modules Are Found" — the nine-candidate cascade table is
  superseded. Resolution reads the first `use` segment as a mote name and looks
  under `<mote>/src/`, with `lib` naming the importing file's own mote and a
  manifest lookup behind that.
- `modules.md` — "There is also no package system … the self-hosted compiler
  does not read manifests at all" is false. `lang/src/mote.mo` reads `mote.toml`,
  and using a mote the manifest does not declare is an error.
- `modules.md`, "Visibility" — both `priv` and the mote boundary are enforced
  by BOTH compilers now (`monad-rs check` included), at every reference and on
  every load path. The old claim that the Rust host does not gate `priv` is
  false.
- `bootstrap-host.md` — "**The self-hosted compiler has no mote support at
  all**" is false, and the section framing motes as a host-only feature needs
  rewriting around the workspace that ships in the repo.
- Throughout — `use` paths should be respelled with `::`, and examples that
  import from the same mote should use `lib::`.
- File paths in prose all gained a `src/` level, and two chapters name files
  that also changed mote: `lang/main.mo` is now `cli/src/main.mo` and
  `lang/cli.mo` is `cli/src/args.mo` (both in `macros.md`), and
  `lang/codegen/runtime.c` is `runtime/src/runtime.c`. 33 references in all:
  `modules.md` 11, `compiling.md` 7, `macros.md` 5, `stdlib.md` 3,
  `type-classes.md` 2, `reference.md` 2, `io-monad.md` 2, `instances.md` 1.
