# Appendix: The Bootstrap Host

This book documents the **self-hosted** Monad compiler — `lang/`, written in
Monad, which compiles itself. That is the language.

There is a second implementation: `monad-rs`, a compiler and interpreter written
in Rust. It exists to bootstrap the first one, and it is still what runs the
self-hosted compiler's source before you have a binary. It is a **host**, not
the language.

This appendix exists because the two are not yet identical, and because the host
currently provides some things the self-hosted compiler does not have at all —
including every piece of editor tooling. Nothing in here is a language feature.

## Getting it

```bash
cargo build --release        # produces target/release/monad-rs
cargo install --path cli     # or install it
```

The binary is `monad-rs`; the crate is `monad-cli`.

## What the host has that the self-hosted compiler does not

### An interpreter that runs real programs

```bash
monad-rs run file.mo
monad-rs run file.mo -- arg1 arg2     # everything after -- reaches `main`
```

The self-hosted compiler has `run` (compile, then execute) and `eval`, but
`eval`'s interpreter reaches only eight pure natives — no `println`, no files.
The host's interpreter runs the whole language, and skips `llc` and `clang`, so
it is still the faster way to iterate on an effectful program.

### A test runner with machine-readable output and parallelism

```bash
monad-rs test init std
monad-rs test lang --json -j 8 --timeout 30
```

The self-hosted `monad test` now runs the whole corpus (CI's sweep uses it),
but it runs files one at a time and has no `--json`, `-j`, or `--timeout`. It
also cannot run tests whose bodies reach a native the compiled backend does not
wire — the concurrency ones above all — where the host's interpreter can. For
those, and for tooling that wants to parse results, use the host.

### Editor and agent tooling

| Command | What it does |
|---------|--------------|
| `monad-rs lsp` | LSP server over stdio: diagnostics, hover, definition, document and workspace symbols, an organize-imports code action, and code lenses that run tests. No completion, rename, or semantic tokens. |
| `monad-rs mcp` | MCP server exposing `check`, `symbols`, `hover`, `definition`, `organize_imports`, `test` |
| `monad-rs repl` | Interactive REPL |
| `monad-rs organize-imports [--write]` | Rewrites bare `use`/`open` to explicit name lists; the only codemod that exists |
| `monad-rs symbols` / `hover FILE L C` / `definition FILE L C` | One-shot code intelligence, `--json` available |

The repository also ships a Claude Code plugin in `.claude-plugin/` that wires
up the MCP server.

### Packages (motes)

A **mote** is a package: a directory with a `mote.toml` and a `src/`.

```toml
[mote]
name = "example"
version = "0.1.0"
edition = "2026"

[dependencies]
local = { path = "../other-mote" }
```

```bash
monad-rs test examples/test_mote.mo -p motes/example/src
monad-rs check --workspace
```

Local **path** dependencies resolve fully, with transitive walking, workspaces
(`[workspace] members = ["motes/*"]`), a `mote.lock` format, and version-conflict
detection. Registry and git dependencies parse and are then rejected:

```text
dependency from-registry 1.0: registry deps not yet supported
```

There are no `build`/`add`/`publish` commands. **The self-hosted compiler has no
mote support at all** — its module resolution is a fixed cascade, described in
[Modules and Imports](./modules.md#how-modules-are-found).

### Termination checking

The host rejects recursion it cannot see decreasing structurally; the
self-hosted compiler performs no termination analysis. See
[Termination Checking](./termination.md) — this is the divergence most likely to
surprise you, because code that checks clean self-hosted can fail under the
host.

### Module resolution knobs

`--mote-path DIR` (repeatable), `--manifest-path PATH`, `MONAD_STDLIB`, and
`--workspace` all belong to the host. Resolution there is relative to the working
directory.

## Syntax the host accepts and the self-hosted compiler rejects

Each entry below is also marked in the chapter where it appears. Most of what
used to be in this table — char literals, named instances, `_` holes,
multi-binding `let`, brace-parameter declarations, multiplicity prefixes on
parameters — has since been implemented self-hosted; what is left is:

| Construct | Portable alternative |
|-----------|----------------------|
| `#[derive BEq BOrd Debug Lens]` | write the instances by hand. The attribute parses self-hosted, but nothing expands it, so no instances are generated |
| `\u{XXXX}` in a string or char literal | write the character itself |
| A dotted instance name (`instance A.B : Class T`) | use a single bare identifier |
| A `let` with the `;` between bindings left out | write the `;` — the self-hosted parser requires it |
| `_` as a hole in **value** position | only type position works self-hosted; write the value |

## Syntax the self-hosted compiler accepts and the host rejects

Three, in this direction.

Term macros:

```monad,ignore
defmacro double x := x + x
def y : I64 := double! 9
```

The host fails with *"macro `double` did not return a Term value"*. Declaration
macros (`defmacro name T := decls { … }`) work on the host — it is specifically
the term form that diverges. See [Macros and Derive](./macros.md).

A multiplicity prefix on a **destructured** parameter:

```monad,ignore
def sum_coord (!{fst, snd} : Coord) : I64 := fst + snd
```

The host's destructured-parameter parser never reads a prefix, so this is a
parse error there. See [Linear Types](./linear-types.md).

And a codegen behaviour rather than syntax: the self-hosted backend runs a
pre-elaboration pass that desugars annotated struct literals, and aborts loudly
if one ever reaches codegen undesugared. The host resolves struct literals in
its own checker and has no equivalent.

## Why this matters for what you write

If you are writing Monad, target the self-hosted compiler: everything in the
main chapters works there. Use the host for its tooling — editor diagnostics, a
REPL, and running test suites.

If you are working on the compiler itself, you need both, and you should expect
the host to be stricter (termination) and more permissive (the syntax table
above) at the same time — with the two directions now much closer in size than
they were.

Each gap is tracked in the project's plans as
`bootstrapping/self-hosted-parity-gaps.md` and
`bootstrapping/self-hosted-test-runner-multi-test.md`.
