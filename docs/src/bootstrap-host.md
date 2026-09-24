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

The self-hosted `monad test` now runs the whole corpus, including the
concurrency tests — CI's sweep uses it and carries no exclusions — but it runs
files one at a time and has no `--json`, `-j`, or `--timeout`. For parallelism,
machine-readable output, or a per-test timeout, use the host.

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

There are no `build`/`add`/`publish` commands. The self-hosted compiler reads
manifests too — `check` and `test` share one mode dispatch (explicit paths,
`--workspace`, or the mote you are standing in; `compile` takes an explicit
path, and a bare one prints its usage) and all three resolve a module path from
the mote doing the `use`, falling back to the directory conventions for script
modules. See
[How Modules Are Found](./modules.md#how-modules-are-found). What remains
host-only is everything beyond a manifest's declared paths: transitive walking,
the `mote.lock` format, version-conflict detection, and the registry.

### Module resolution knobs

`--mote-path DIR` (repeatable), `--manifest-path PATH` and `MONAD_STDLIB` all
belong to the host, and resolution there is relative to the working directory.
`--workspace`/`-w` is on both, which is what makes
`monad check --workspace` mean the same thing either way.

## Behaviour the two compilers read differently

This section used to be a syntax table, and it is **empty now**. Everything that
was in it has been implemented self-hosted: char literals, named instances, `_`
holes, multi-binding `let`, brace-parameter declarations, multiplicity prefixes
on parameters, `#[derive …]`, `\u{XXXX}` escapes and dotted instance names.

"Empty" means the entries that table held, not every construct either grammar
can spell, and one family sits outside it. A lambda's **parameter** list:
`fn (x) => x`, `fn (x := 5) => x` and `fn ({x, y} : P) => x` all parse under
the host — its parameter annotation is optional, and a destructured group is
accepted — and are a hard parse failure self-hosted, because the dispatch
after `fn` sends every `(` to the typed-parameter path, which requires a `:`.
The reverse holds in the same place: the host requires whitespace after `fn`,
so `fn(x : I64) => x` parses only self-hosted. No file in the corpus writes a
bare `fn (x)`, so this is latent rather than live, and it predates the rewrite
above; it is named here because "no construct left" was read as covering it.

One *behavioural* difference remains — code both compilers accept, which they
then read differently. It is not a syntax gap. A second one, the un-inferable
`_`, closed on this branch and is recorded below rather than deleted.

**A missing `;` between `let` bindings.** Both parse it. Self-hosted, the
binding's value expression is `atom (atom)*`, so it swallows the *next
statement* as an argument whenever that statement's head is an expression atom:

```monad,ignore
def f : I64 := do {
  let a : I64 := 1
  I64.add a 2       // absorbed: the value became `1 I64.add a 2`
}                   // error: unknown variable 'a' in f
```

The binder then never scopes where you meant it to. The host's grammar requires
a *path* head for an application, so it cannot swallow and reads the statement
correctly. The missing `;` is harmless when the next statement begins with a
keyword rather than an expression (`let b : I64 := 2` follows fine), which is
what makes this one easy to write by accident: **write the `;`.** This is the
same grammar difference as the atom-in-function-position entry below, seen from
the other side.

**A `_` whose type cannot be inferred — closed.** `def h : I64 := _` is accepted
by both, and by both it lowers to a value that is not what you wanted
(`I64.beq h 0` fails under each): write the value. The *un-inferable* shape used
to be the divergence — the host rejects a hole no expected type reaches
(`def k : I64 := (fn x => x) _` is *"cannot infer the type of a hole"*) while
self-hosted accepted it silently — and it is not one any more. The reason it
could not be closed by a predicate over the hole is worth keeping: the
self-hosted parser wrote the sort `Type` onto every unannotated lambda
parameter where the reference writes a hole, so a callee's own term shape
(`fn x => x`, as opposed to an application) could not be read at all, and the
argument side was checking against `Type` besides. Both halves were fixed
together, and the port now rejects exactly the two rows of the probe matrix the
host rejects (`(fn x => x) _` and `(fn (x : _) => x) _`) and accepts the other
twelve.

## Syntax the self-hosted compiler accepts and the host rejects

Four, in this direction.

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

An **atom in function position** — an application whose head is a literal
rather than a path:

```monad,ignore
def g : I64 := 1 5
```

Self-hosted this parses (`"s" 5` and `(1) 5` do too; nothing checks the head is
callable). The host rejects it: a bare literal head is a parse error, and a
parenthesised one gets as far as *"expected a function type, found `I64`"*. No
real program wants this, so the portable alternative is simply not to write it
— but it is worth knowing, because it is the grammar fact behind the missing-`;`
mis-scope described above: the same `atom (atom)*` shape is what lets a `let`
value swallow the statement after it.

And a codegen behaviour rather than syntax: the self-hosted backend runs a
pre-elaboration pass that desugars annotated struct literals, and aborts loudly
if one ever reaches codegen undesugared. The host resolves struct literals in
its own checker and has no equivalent.

## Why this matters for what you write

If you are writing Monad, target the self-hosted compiler: everything in the
main chapters works there. Use the host for its tooling — editor diagnostics, a
REPL, and running test suites.

If you are working on the compiler itself, you need both. The host is the
stricter one, and not only about holes. Measured at the end of the test-gap
branch, the self-hosted checker accepts a *concrete* type mismatch in nine of
the ten positions probed — def body, application body, `return`, `if`/`else`
branches, lambda argument, named-def-call argument, constructor argument,
struct-literal field, class-method return — and enforces only the match-arm
result, which it enforces correctly. `unify` itself is sound; the comparison is
simply never invoked at those boundaries, so **a clean self-hosted `check` is
not evidence of type soundness.** (`def f : I64 := "s"` is the shortest way to
see it: accepted self-hosted, one error under the host.) The
self-hosted grammar is separately the more permissive one at the edges, in the
four places listed above. Both directions are larger than the hole case this
paragraph used to name, and the type-checking one is much the largest.

This appendix is the current record. The two plans it used to point at are
historical: `bootstrapping/self-hosted-parity-gaps.md` was a 2026-09-07
inventory of constructs the host accepted and the self-hosted compiler did not,
and eleven of its twelve sections have closed since — the twelfth is the term
macro above, which is a host-side bug;
`bootstrapping/self-hosted-test-runner-multi-test.md` tracked files the
self-hosted test runner skipped, and the sweep now carries no exclusions at
all. The checker gaps that remain are tracked in
`bootstrapping/self-hosted-compiler-review-2.md`.
