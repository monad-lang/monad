# Command-line reference

`monad <command> --help` prints each command's own surface, and
`monad --help` (or `monad help`) prints the command list below. This page
says the same thing in a readable order; when the two disagree, the binary
is right.

The parser is the `clap` mote's `#[derive Cli]`, so:

- `--help`/`-h` and `--version`/`-V` work at every level.
- A long option may take its value as a separate argument
  (`--output name`) or joined with `=` (`--output=name`). A **flag** that
  does not take a value rejects the `=` form (`--verbose=false` is a
  usage error).
- Flags are position-independent: `monad build -v hello.mo` and
  `monad build hello.mo -v` are the same command.
- An unknown command or flag is a usage error on stderr with **exit code
  2**; an argv that names no command also exits 2, with the usage screen.
- `monad s` is the short spelling of `monad script`.

## Commands

| Command | What it does |
|---|---|
| [`build`](#build) | Compile a `.mo` source file, or a mote, to a native binary |
| [`install`](#install) | Build a release binary and install it under `$MONAD_HOME/bin` |
| [`run`](#run) | Compile and execute a source file |
| [`script`](#script) | Build and run a named `[[script]]` (alias: `s`) |
| [`eval`](#eval) | Evaluate a source file with the built-in interpreter (pure programs) |
| [`repl`](#repl) | Interactive read-eval-print loop on stdin/stdout |
| [`pretty`](#pretty) | Parse and pretty-print a source file |
| [`fmt`](#fmt) | Format source files in place, or verify them with `--check` |
| [`check`](#check) | Parse and typecheck source files, with no execution |
| [`test`](#test) | Compile and run each file's own `#[test]` defs |
| [`clean`](#clean) | Remove build output, keeping the store |
| [`gc`](#gc) | Remove store entries the named files cannot reach |
| [`store`](#store) | List the store, or check its entries |
| [`fetch`](#fetch) | Resolve git dependencies into the cache and write `mote.lock` |
| [`update`](#update) | Re-resolve every git pin, then write `mote.lock` |
| [`doc`](#doc) | Generate an API reference for the named motes from their sources |
| [`kernels`](#kernels) | List each `#[kernel]`: its MLIR signature, C ABI, and whether it compiles as one |
| [`print-targets`](#print-targets) | List the triples `--target` accepts and what this llc can build for |
| [`lsp`](#lsp) | Speak the Language Server Protocol on stdin/stdout |
| [`version`](#version) | Print the git commit this binary was built from |

Several commands share the same *path* conventions, explained once
[below](#paths-and-the-enclosing-mote).

## build

```text
monad build [<path>] [name] [options]
```

Compile a `.mo` source file, or a mote, to a native binary. This verb was
called `monad compile` until 2026-09-29; there is no alias.

| Option | Meaning |
|---|---|
| `-o, --output <NAME>` | output name (the first positional `name`, when given, is the legacy spelling of this) |
| `--bin <NAME>` | pick one `[[bin]]` target when several exist |
| `--target <TRIPLE>` | build for another target (`monad print-targets` lists the spellings) |
| `--target-dir <DIR>` | where the store and output directories live |
| `-v, --verbose` | print each module as it loads and one line per stage |
| `-g, --debug` | emit DWARF debug info |
| `--release` | build without debug info |
| `--no-cache` | compile for real, reading and writing no store entry |
| `--locked` | fail when a dependency's pin no longer matches `mote.lock` |
| `--offline` | accepted and ignored: build never uses the network |

Debug info is **on by default**; `--release` opts out, and an explicit
`--debug` opts back in. A **relative** output name lands inside the
target directory — use an absolute `-o` when you want the binary
somewhere specific (see
[Where the binary lands](./compiling.md#where-the-binary-lands)).

## install

```text
monad install [<path>] [options]
```

Build a **release** binary (no debug info) by the same cached path as
`build`, then install it to `$MONAD_HOME/bin/<name>`. `MONAD_HOME`
defaults to `$HOME/.monad`, so the binary lands beside the compiler in
the layout `monadup` uses. The destination is written as `<dest>.tmp`
and moved into place, so an existing file **or symlink** at the
destination is replaced atomically — `cp` alone would write through a
monadup-managed `bin/monad` symlink.

A mote directory installs its `[[bin]]` target under its own name; a
single `.mo` file has no name of its own and therefore needs
`-o <name>`.

| Option | Meaning |
|---|---|
| `-o, --output <NAME>` | installed name (required for a source file) |
| `--bin <NAME>` | pick one `[[bin]]` target |
| `--target <TRIPLE>` | build for another target |
| `-v, --verbose` | print each module as it loads |
| `--no-cache` | compile for real, reading and writing no store entry |

## run

```text
monad run <path> [--] [args...]
```

Compile and then execute. Everything after `<path>` is the compiled
program's own argv; flag-like arguments (`-x`, `--weird`) must follow
`--`, plain words are forwarded without it. The program's exit code
becomes `monad`'s.

| Option | Meaning |
|---|---|
| `-v, --verbose` | print each module as it loads |
| `-g, --debug` | emit DWARF debug info |
| `--release` | build without debug info |

## script

```text
monad script [<name>] [--] [args...]
```

Build and run a named `[[script]]` declared in the nearest `mote.toml`
(or a workspace root's); `scripts/` is the usual home. `monad s` is the
short spelling.

| Option | Meaning |
|---|---|
| `--list` | list scripts (`mote/script -> path`) instead of running one |
| `-w, --workspace` | also search the workspace's member motes |
| `--watch` | rebuild and rerun whenever a file in the script's tree changes (see [Watching Files](./compiling.md)) |
| `--mote <NAME>` | resolve the closure through that member instead of the script's own manifest |
| `--target-dir <DIR>` | where the store and output directories live |
| `-v, --verbose` | print each module as it loads |
| `-g, --debug` | emit DWARF debug info |
| `--release` | build without debug info |
| `--no-cache` | compile for real, reading and writing no store entry |

## eval

```text
monad eval <path>
```

Evaluate a `.mo` source file with the built-in interpreter. **Pure
programs only** — no file I/O, no processes.

| Option | Meaning |
|---|---|
| `-v, --verbose` | print each module as it loads |

## repl

```text
monad repl
```

Interactive read-eval-print loop over the same interpreter (pure
programs only). Expressions print `value : type`; declarations
(`def`/`type`/`struct`/`class`/`instance`/`use`/`open`) persist in the
session. `:help`, `:quit`, `:reset`, `:type <expr>`; a `def` body may
continue on the next line. Prompts go to stderr, results and
diagnostics to stdout; EOF or `:quit` leaves.

## pretty

```text
monad pretty <path>
```

Parse and pretty-print a `.mo` source file.

## fmt

```text
monad fmt [<path>...] [options]
```

Canonicalize whitespace and indentation. Tokens are never reordered or
rewritten, comments are preserved verbatim, and the author's line
breaks are kept.

| Option | Meaning |
|---|---|
| `--check` | exit 1 if any file would change |
| `--diff` | print a unified diff instead of writing |
| `--stdin` | read a whole module from stdin and write it to stdout (with `--check`/`--diff`, diagnostics go to stderr) |
| `-w, --workspace` | format every mote in the enclosing workspace |
| `-v, --verbose` | print each changed file |

## check

```text
monad check [<path>...] [options]
```

Parse and typecheck `.mo` source files; no execution.

| Option | Meaning |
|---|---|
| `-w, --workspace` | check every mote in the enclosing workspace |
| `-v, --verbose` | print a per-declaration progress trace |
| `--no-cache` | skip the check cache (or `MONAD_NO_CACHE`) |
| `--locked` | fail when a dependency's pin no longer matches `mote.lock` |
| `--target-dir <DIR>` | where the check cache lives |
| `--offline` | accepted and ignored: check never uses the network |

Results are cached under `<target-dir>/check` for multi-file runs,
keyed on the file, its mote's whole declared closure, and the running
compiler; a single-file run always does the work.

The affine usage rule always runs: a binder used twice without a `Copy`
instance is an error. A mote can opt into warnings for migration with
`[affine] mode = "warn"` in its `mote.toml`; there is no off switch (see
[Linear Types](./linear-types.md)).

## test

```text
monad test [<path>...] [options]
```

Compile and run each file's own `#[test]` defs as a native binary. A
file with no `#[test]`s is skipped, not failed. A file that defines its
own `main` is fine: that `main` is renamed out of the way and the
generated test driver becomes the entry point. With no path, the mote
containing the working directory is tested; its `[mote] targets` decides
which `[[bin]]` roots are native-testable.

| Option | Meaning |
|---|---|
| `-w, --workspace` | test every mote in the enclosing workspace |
| `-v, --verbose` | print per-file timing and module-cache statistics |
| `-j, --jobs <N>` | files in flight (default 4; `1` is the serial runner) |
| `--locked` | fail when a dependency's pin no longer matches `mote.lock` |
| `--no-cache` | skip the test cache |
| `--target-dir <DIR>` | where the test cache lives |
| `--offline` | accepted and ignored: test never uses the network |

## clean

```text
monad clean [options]
```

Remove build output, keeping the store: every output directory under
`<target-dir>` (the profile directories).

| Option | Meaning |
|---|---|
| `--all` | remove `<target-dir>` itself, the store included |
| `--target-dir <DIR>` | the target directory to clean |

## gc

```text
monad gc [<path>...] [options]
```

Remove store entries the named files cannot reach. Dry run by default;
`--apply` removes them. Refuses to remove **anything** when it cannot
derive a complete reachable set, because an incomplete one would delete
the store itself.

| Option | Meaning |
|---|---|
| `--apply` | remove the entries (dry run by default) |
| `-w, --workspace` | consider every mote in the enclosing workspace |
| `--target-dir <DIR>` | where the store lives |

## store

```text
monad store <sub> [options]
```

List the store (`ls`), or check its entries (`verify`). Each line is
`<kind> <key> <bytes> <state>`; an artifact is its binary **and** its
IR. `verify` is structural: an entry records neither the file nor the
sources behind it, so it checks that an entry is complete and readable,
not that its key is the right key. It exits non-zero on any incomplete
entry.

| Option | Meaning |
|---|---|
| `--target-dir <DIR>` | where the store lives |

## fetch

```text
monad fetch [<dir>] [options]
```

Resolve git dependencies into `$MONAD_HOME/cache/git` and write
`mote.lock`. The only verb that uses the network. `fetch` keeps the
commit `mote.lock` already names, so a tag that moved upstream does not
change a locked build; `fetch` is the one to run after a manifest edit.

| Option | Meaning |
|---|---|
| `--offline` | use only what is already cached; a missing mirror is an error naming the URL |

## update

```text
monad update [<dir>] [options]
```

Like `fetch`, but re-resolve every tag/branch/HEAD pin. Writes
`mote.lock` from scratch.

| Option | Meaning |
|---|---|
| `--offline` | use only what is already cached; a missing mirror is an error naming the URL |

## doc

```text
monad doc [<mote>...] [options]
```

Generate an API reference from the motes' own sources. Each mote is its own
small site under the output directory: `<mote>/index.html` (the mote's `lib`
doc and its module list) and one page per module at `<mote>/<module>.html`,
plus an `index.html` hub linking every mote and the `docgen.css` stylesheet
every page links. monad-lang.org publishes the same layout under
`/motes/docs/` (`/motes/docs/init/` for `init`). Each `pub`
declaration gets its signature and its `///` doc comment, rendered as
markdown. The pages are written through the site generator's link gate, so a
reference that links to a module with no page fails the build instead of
shipping a 404. A declaration's anchor is its source spelling:
`<kind>.<name>` (`def.List.map`, `struct.Point`).

With no mote named, the enclosing mote (`.`) is documented, the same default
`check` and `test` take.

| Option | Meaning |
|---|---|
| `-o, --output <DIR>` | the output root the `api/` tree is written under (default `target/docs`) |
| `--include-private` | include package-private and `priv` declarations, not just `pub` |

`monad doc` is the compiler's spelling of the same generator the standalone
`docgen` binary runs (`motes/docgen`); the site build uses it too, and
[The Standard Library](./stdlib.md) links to its output.

## kernels

```text
monad kernels <file-or-mote> [-v]
```

One line per `#[kernel]` def: its MLIR signature, its C ABI, and `ok` when
`build` will compile it through MLIR. A kernel that is not ready is listed
with the diagnostics that keep it an ordinary function; that is not an
error, and `build` still compiles it, as its plain body. Nothing is
compiled.

## print-targets

```text
monad print-targets
```

List the triples `--target` accepts, and what this llc can build for.
Each is the spelling the emitter writes; `(llc ...)` adds the argv when
llc needs more than the triple to select the target. A `--target` name
whose architecture this llc does not register is rejected by name.

## lsp

```text
monad lsp
```

Speak the Language Server Protocol on stdin and stdout, until stdin
ends. Started by an editor, which is told nothing else: no arguments, no
flags.

## version

```text
monad version
```

Print the git commit this binary was built from.

## Paths and the enclosing mote

`build`, `check`, `test`, `fmt` and `gc` take the same path forms:

- A **directory** is expanded recursively to its `*.mo` files; hidden
  directories (`.devenv`, `.git`) are skipped by every walk.
- With **no path**, the mote containing the working directory is used;
  with no mote above the working directory the command says so and exits
  1, rather than reporting a pass for having done nothing.
- `-w`/`--workspace` covers every mote in the enclosing workspace (only
  directories that **are** motes: `examples/` has no manifest).

`build`/`check`/`test` verify `mote.lock` before compiling and take
`--locked`, which also fails when a dependency's declared
tag/branch/rev no longer matches the lock. They accept `--offline` too,
and ignore it: they never use the network. `clean`, `gc` and `store`
take the same `--target-dir <dir>` flag as `build`; without it the
config and the default decide where the store and output directories
live.
