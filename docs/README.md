# Documentation

The Monad language site is built by **`docs/site/monad_website`** (the
monad-lang.org site: landing page and chrome) on **acorn** (`motes/acorn`,
the generic static book/site generator), and published to
<https://monad-lang.org> by `.github/workflows/site.yml` on every push to
`main`.

- The landing page is `docs/site/monad_website/src/landing.mo`, rendered to
  `monad-lang.org/`.
- The book's sources are `docs/src/` (`SUMMARY.md` and 22 chapters), rendered
  to `monad-lang.org/docs/` at the same URLs mdBook used, plus `index.html`,
  `print.html` and `404.html`.
- `docs/site/static/` is copied as-is: the landing stylesheet and icons, the
  favicon and logo, `/try` and `/install`. `motes/acorn/assets/acorn.css` is
  the book theme.
- The configuration is `docs/site.toml`.

```bash
docs-build            # devenv script: render the site into docs/public
docs-serve            # devenv script: build it, then serve docs/public on :8000
```

`scripts/build-docs.sh` does the work: it stages `/install` and the `/try`
wasm into `docs/site/static/`, builds acorn and `monad_website` with the
tree's compiler, and runs `monad_website build`. The static tree is copied by
acorn, so those two steps must come first. The build fails before writing
anything if an internal link points at a page or anchor that does not exist.

`docs-serve` serves the output with **`moon static`** (`motes/moon`, built by
the same script with `--with-moon`), the repository's own replacement for
`python3 -m http.server`:

```bash
moon static [DIR] [--port N] [--host H]    # DIR defaults to ., port 8000,
                                           # host 127.0.0.1
```

`acorn build` on its own is the generic builder: it renders the book in
acorn's own plain chrome and writes no landing page, which is what makes
acorn reusable by another site.

## Keeping the examples correct

A site build only renders markdown — it does not compile the Monad inside it.
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
- `modules.md`, "Visibility" — `priv` and the mote boundary are enforced by
  the self-hosted compiler at every reference and on every load path; the
  Rust bootstrap host enforces the same rule in its loader, but it is not
  the language's definition (see `bootstrap-host.md`).
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
