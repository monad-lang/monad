# Maturity Matrix

Monad is in alpha. This chapter says, area by area, what actually works today —
so you can tell the parts you can build on from the parts that are still a
sketch.

**This rates the self-hosted compiler**, the `monad` binary written in Monad
that compiles itself. That is the language. Where the Rust
[bootstrap host](./bootstrap-host.md) differs it is called out, because the
difference currently matters.

Every row here was checked against the compilers' own source and tests at the
commit this book ships with, not inferred from intent.

## How to Read This

| Level | Meaning |
|-------|---------|
| **Solid** | Production quality for its scope. Well tested, unlikely to change under you. |
| **Working** | Does its job. Rough edges, but you can build on it. |
| **Partial** | Real, but incomplete. Read the note before depending on it. |
| **Experimental** | Works, but the shape will change. |
| **Stub** | Present in name only. Do not depend on it. |
| **Planned** | Does not exist yet. |
| **Host only** | Works in the bootstrap host; the self-hosted compiler does not. |

## Language

| Area | Level | What that means |
|------|-------|-----------------|
| [Syntax & parser](./reference.md) | **Working** | Stable and well covered. Every `def` needs a type annotation — there is no top-level inference. |
| Type checker | **Working** | Bidirectional, with implicits and holes. Catches most errors; see the instance caveat below. |
| [Type classes & instances](./type-classes.md) | **Partial** | Resolution and superclass constraints work. But instances resolve at **run time**, so a missing instance type-checks and then fails with `unresolved global:`. Empty instance bodies do not parse, so class defaults cannot be inherited wholesale. Resolution keys on the type *head*, so an instance whose head is a variable (`MonadLiftT m m`, `Monad (M I I)`) type-checks and never dispatches. |
| [Inductive types](./inductive-types.md) | **Working** | Parameters, recursion, indexed families, and the strict-positivity rule — a constructor field of a function type *from* the type being declared is rejected. |
| Pattern matching | **Partial** | One constructor level deep. No nested patterns, no literal patterns, no guards, no or-patterns, and **no exhaustiveness checking**. |
| [Structs](./structs-enums.md) | **Partial** | Records, field defaults, `{ s with … }` update, keyword construction, and field destructuring all work. **Generic structs are effectively unconstructible** — use a `type` with a positional constructor. |
| [Dependent types](./dependent-types.md) | **Partial** | Pi and forall types, implicits, `Sort N` universes, `Prop`, and length-indexed `Vec` all work. Propositional `Eq` type-checks but **cannot be eliminated** — `Eq.rec`'s native is unimplemented and matching on `refl` fails at run time. No dependent pattern matching, no tactics, no universe polymorphism. |
| [Macros](./macros.md) | **Working** | `defmacro`, `quote`, and reflection-as-data. Term macros work here and *not* on the host — the one divergence in that direction. |
| [Modules & visibility](./modules.md) | **Working** | `pub`/`priv`/package-private, explicit import filters, unused-import warnings. Resolution is mote-based — a mote's own root first, the directory cascade as the script-mode fallback — and `check`/`test` take `--workspace` or the mote you are standing in (`compile` takes an explicit path). |
| Tuples, raw strings | **Working** | Both real and stable. |
| Optics | **Working** | `Lens` and `Prism` in `init.optics`. |
| Indexed monads | **Experimental** | `IndexedMonad`, `IndexedMonadState` and `IndexedMonadLift` exist and type-check, and `examples/indexed_monads.mo` exercises them. The `Monad (M I I)` bridge instance in the prelude does not dispatch (variable head), so an indexed monad still needs its own `Monad` instance written out. |
| [Termination checking](./termination.md) | **Working** | A structural subterm check, run once per module over that module's own declarations by both compilers, with the same message either way. Recursion over an inductive type is accepted; counting down an `I64` needs `#[terminating]` or `#[partial]`. |
| [Linear & affine types](./linear-types.md) | **Partial** | The syntax parses everywhere it is meant to: struct fields, `def` and lambda parameters, and destructured parameters (`(!{x, y} : P)`, which the *host* still rejects). **Nothing is enforced** — lowering drops the multiplicity, and every binder the checker builds is `Many`. |
| `#[derive BEq BOrd Debug Lens]` | **Working** | Both compilers bridge the attribute to the same `std/derive.mo` macros. The backend must be imported — `#[derive BEq]` dispatches to `derive_beq` by name. |
| Char literals `'M'` | **Working** | Parse, type-check and compile, escapes included, `\u{...}` on both. `Char` itself is a **stub**: no operations, no `BEq`, no `ToString` — you can write, type and pass one, not inspect it. |
| `_` holes in term position | **Partial** | In *type* position (`(x : _)`) it works. In *value* position both compilers accept it and both lower it to a value that is not what you meant (`I64.beq _ 0` fails under each) — write the value. A hole in *infer* position, where no expected type reaches it (`def k : I64 := (fn x => x) _`), is rejected by **both**, with the host's own *"cannot infer the type of a hole"*; that divergence used to open the other way and closed on this branch. |
| Named instances | **Partial** | `instance Name : Class Type { … }` parses on both, bare or dotted (`instance My.Greet : Greet I64`). Nothing selects an instance *by* name in either implementation. |
| Brace-form params with defaults | **Working** | The declaration parses and the default is applied at call sites by both compilers: omit `factor` in `scale { p := 4 }` and the declared `:= 2` stands in. |
| Multi-binding `let x := 1; y := 2 in` | **Working** | The `;` separator parses on both. Write it: self-hosted, an omitted `;` lets the binding's value swallow the next statement as an argument (see [the appendix](./bootstrap-host.md)), so the binder never scopes. Nested `let … in` still works everywhere. |
| UFCS method calls (`x.f args`) | **Planned** | An earlier host type checker desugared these; neither does now. `x.f` is field access only. |
| Backtick infix (`` `f` ``) | **Planned** | The parser recognises the token; the expression parser never reduces it. |
| `for` loops | **Planned** | `for` is reserved with no grammar rule. |
| Reading stdin | **Planned** | `IO` can print and touch files; there is no `getLine`. |

## Implementation

| Area | Level | What that means |
|------|-------|-----------------|
| [Self-hosted compiler](./compiling.md) | **Working** | ~64k lines of Monad in `lang/`. It compiles itself, and the result type-checks the compiler's own source. CI runs this on every push. The bootstrap has reached a fixpoint. |
| LLVM native backend | **Partial** | Arithmetic, strings, file I/O and the seven concurrency natives are wired. A program reaching an unwired native **fails to compile** rather than miscompiling — one of four fail-fast gates. |
| `monad check` | **Working** | The corpus checks clean, and the check phase of CI's sweep carries no exclusion list. `check` takes explicit paths, `--workspace`, or the mote you are standing in. |
| `monad run` | **Working** | Compiles the file and executes the binary in one step. The binary is always named `run_out`, so there is no `-o`. |
| `monad eval` | **Partial** | A self-hosted interpreter, but only **8 pure natives** are wired into it (`i64_add/sub/mul/eq/lt`, `string_concat/eq/to_lowercase`). Anything else, `println` included, fails with `unknown native` — so it cannot run a hello-world. |
| `monad version` | **Working** | Prints the git commit baked in at link time. |
| `monad test` | **Working** | Runs the whole corpus, including the concurrency tests, with no exclusion list: a compiled driver per file, per-test timing, `module::test_name` names, and a failure COUNT the driver reports through a result file (no longer an 8-bit exit code, so a file's test count is no longer capped at 255). Takes explicit paths, `--workspace`, or the mote you are standing in. |
| `monad pretty` | **Working** | Parses and pretty-prints. |
| Memory management | **Partial** | Compiled binaries use the Boehm conservative GC, explicitly a stopgap. The compiler still emits no `monad_retain`/`monad_release` calls for ordinary values, so the refcount is **only** load-bearing for fiber and scope handles (see below); deterministic freeing is blocked on linear types. |
| [Concurrency](./concurrency.md) | **Experimental** | Real concurrency on 1:1 pthreads: `forkIO` starts a thread, `await_fiber` joins it, `scope_*` keeps handles alive through the atomic refcount. Cancellation is recorded rather than preemptive. The **host** is still the lazy/cooperative one, so only compiled code can actually interleave. |
| Error messages | **Partial** | Source spans and useful text for most failures. Parse errors report "did not fully parse (stopped before end of file)" with the remaining text, which locates the line but not the construct. |

## Ecosystem

| Area | Level | What that means |
|------|-------|-----------------|
| [Standard library](./stdlib.md) | **Partial** | ~440 public definitions, 35 classes, 132 instances. Strong: the numeric tower (10 widths, fully instanced), strings, lists, `HashMap`/`BTreeMap`, a native-backed `Array`, a pure-Monad SHA-256. Thin: no `Iterator`, **zero** `Traversable` instances, duplicate `Semigroup`/`Monoid`. |
| Assertions (`std.test`) | **Stub** | `Test.assert` is the identity function on `Bool`. No `assert_eq`, no failure messages. |
| Distribution | **Partial** | A nightly prerelease is published on every push to `main`, and `scripts/monadup` installs and switches between them. One artifact only — Linux x86_64 — and it is built inside the Nix devenv, so it links store paths and does **not** run on a plain machine. |
| Packages | **Working** | Manifests are read: a module path resolves from the mote doing the `use`, and `check`/`test`/`compile` take `--workspace` or the mote you are standing in. Script modules declare theirs inline with `#![mote { … }]`. No search-path flag, and no lockfile or registry — those stay host-only. |
| Editor tooling | **Host only** | The LSP server, MCP server, REPL, and `organize-imports` all live in the host. No syntax highlighting for any editor, and no tree-sitter grammar. |
| CI | **Working** | Build, lint, full test sweep, and a self-hosting bootstrap check on every push. The sweep runs the **self-hosted** runner against a freshly self-compiled binary, so `monad test` itself is covered. |
| Documentation | **Partial** | This book. Every code block is type-checked; prose is not. |
| Formatter | **Planned** | `organize-imports`, in the host, is the only codemod. |
| Package registry | **Planned** | |
| Doc generator | **Planned** | Docstrings are parsed and retained, but nothing renders them. |
| Debugger integration | **Planned** | DWARF is emitted **by default** now (`--release` opts out) and carries a distinct location per term, not one per top-level definition — but nothing consumes it yet. |

## Scale

For context on what "alpha" means here:

| | |
|---|---|
| Monad source (`.mo`) | ~81,500 lines, of which `lang/` is ~64,500 |
| Rust source (bootstrap host) | ~56,400 lines |
| Monad tests (`#[test]`) | 2,033 defined; **1,964** run by CI's sweep |
| Native functions | 137 declared in `init/`+`std/`; 3 unimplemented everywhere; the backend wires a subset |
| Standard library | ~440 public defs, 35 classes, 132 instances (excluding test modules) |

## The Short Version

Monad is a real, self-hosting language: the compiler is written in Monad,
compiles itself, and reaches a fixpoint. The type checker, the class system, the
module system, and a genuine macro system all work.

What it is not yet: **safe by construction** (the self-hosted compiler checks
termination but not linearity — the multiplicity syntax parses everywhere now,
and means nothing), **scalable in concurrency** (fibers are 1:1 pthreads
with 128 MB stacks, real but not the design that ships), or **distributable**
(nightly binaries exist; a lockfile and a registry do not). Its test runner
compiles and runs a driver binary per test file, and covers the whole corpus
with no exclusion list — every file that used to be reported as a gap now runs
self-hosted.

The single largest gap is linear types — and because deterministic memory
management is meant to be built on them, that gap is also why compiled binaries
need a garbage collector.
