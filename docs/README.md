# Documentation

The Monad language book, built with [mdBook](https://rust-lang.github.io/mdBook/)
and published to <https://monad-lang.org> by `.github/workflows/mdbook.yml` on
every push to `main`.

```bash
mdbook build docs     # render to docs/book (gitignored)
docs-serve            # devenv script: serve with live reload
```

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
