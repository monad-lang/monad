# Monad Language Developer Guide

How to modify the Monad language codebase and write correct Monad code.

**All development happens in the current worktree directory.** Do not switch
to other worktrees (e.g. `../monad/`, `../monad-main/`) unless explicitly
instructed — they may target a different branch.

## Project Structure

```
monad/
├── core/              # Rust reference compiler/interpreter ("the Rust host")
│   └── src/
│       ├── parser.rs + parser/   # Lexer/parser
│       ├── core_check_module.rs  # Module type checker (with core_unify.rs)
│       ├── core_eval.rs          # Closure-based CoreTerm evaluator
│       ├── core_native.rs        # Native function dispatch + implementations
│       ├── lower_core_ir.rs      # Term -> CoreIr lowering
│       └── term/ + term.rs       # AST, modules, motes
├── rust-cli/          # `monad-rs`: the Rust host binary (cargo-run surface)
├── cli/               # The self-hosted compiler, written in Monad (`monad build cli`)
├── lang/              # Self-hosted compiler sources: parser, typecheck, module, codegen/
│   └── src/codegen/   # LLVM backend by concern (emit, ir, natives, validate, ...)
├── llvm/              # Self-hosted LLVM IR + linking (llc/clang via exec_cmd)
├── runtime/           # C runtime linked into every compiled binary (runtime.c)
├── build/             # Build orchestrator: input hashing, content store, cache
├── init/              # Pure, portable core mote (prelude, IO type, parser) — no deps
├── std/               # OS-specific side effects (io, process, path, map, test, ...)
├── motes/             # Monad packages (json, lsp, clap, toolkit, shuttle, mcp_client, ...)
├── examples/          # Example programs (not a mote — no manifest)
├── bench/             # Standalone .mo micro-benchmarks, #[test]-driven (not swept by check)
├── slow_tests/        # Real tests too slow for every-commit sweeps (not swept by check)
├── docs/              # mdBook (scripts/check-docs.sh type-checks its fences)
├── scripts/           # CI + dev scripts (build-self-hosted.sh, check-docs.sh, ...)
├── plans/             # Symlink to the external plans repo (design docs)
└── nix/ + flake.nix   # Packaging; CI pushes to monad-lang.cachix.org
```

## Motes

`init/`, `std/`, `lang/`, `cli/`, and everything under `motes/` are **motes**
(Monad's packages). A mote's modules live in its `src/` directory; a `use`
path's first segment names the mote, the rest is the path within its `src/`
(`use lang::codegen::emit {...}` reads `lang/src/codegen/emit.mo`).

- **`init/` vs `std/`**: `init/` holds pure, portable code that must work in
  any environment (wasm included); `std/` holds OS side effects (file I/O,
  processes, env). `init/` must never `use` anything from `std/`. Both are
  ambient: bare `init`/`std` references resolve to their `src/lib.mo`
  re-export hubs, so ordinary files never need `use init`/`use std`.
- **`lib` is the mote's self-reference** (like `crate::`): `use lib::io`
  names this mote's own `src/io.mo`. It is rewritten to the mote-qualified
  path at load time; no mote may be named `lib`.
- **Targets**: `[lib] path` defaults to `src/lib.mo`; with no `[[bin]]` table
  a mote has exactly one target, `src/main.mo`. `monad build <mote>` refuses
  when more than one exists — `--bin <name>` picks one.

### Visibility

```monad,check
pub def exported : I64 := 1     // visible everywhere
def package_private : I64 := 2  // visible inside this mote (the default)
priv def module_only : I64 := 3 // visible only in this file's module
```

`priv` is enforced by the self-hosted compiler (and the LSP); `monad-rs check`
does not gate it. The default is package-private and a cross-mote reference
to an unmarked declaration warns — mark it `pub` or reconsider the import.

## Building and Running

`monad` is the standard binary: `monadup` installs a nightly at
`~/.monad/bin/monad` (`monadup default` installs the latest and makes it
active — run it before self-compile work). `monad build cli` (or
`scripts/build-self-hosted.sh`) builds the self-hosted compiler from
`cli/src/main.mo` as `monad`. `cargo run --release --` (or `monad-rs`) is the
Rust host — use it when iterating on the Rust compiler itself.
`monadup doctor` reports whether the active nightly and the `llc`/`clang`/
`pkg-config`/Boehm-GC build prerequisites are healthy, and `monadup env`
prints the resolved home/platform/toolchain roots.

```bash
monad run examples/hello.mo            # compile and run a file
monad check <path>... [--workspace]    # parse + typecheck (no execution)
monad test <path>... [--jobs N]        # run each file's #[test] defs
monad build <path|mote> [--release]    # compile to a native binary
monad lsp                              # language server on stdio
cargo build -p monad-core              # build the Rust host crate
cargo test -p monad-core <name>        # one Rust test
```

- Use `--release` for self-hosted workloads (anything running
  `cli/src/main.mo` against large files) — the debug build is several times
  slower.
- Prefer the `monad` binary as the host when self-compiling:
  `MONAD_HOST_BIN=monad scripts/build-self-hosted.sh <out>` compiles
  `cli/src/main.mo` at native speed, much faster than the default
  `cargo run --release --` host interpreting it.
- `bootstrap` (devenv) / `scripts/bootstrap-compile.sh` / `devenv tasks run
  monad:bootstrap-compile` self-compiles the compiler; CI runs it after
  every change to `lang/`, `runtime/`, `init/` or `std/` because those are
  compiled INTO the binary (`scripts/build-self-hosted.sh` skips a build only
  when its output is newer than every input).
- The flake's packages are on `monad-lang.cachix.org`; `nix build
  --accept-flake-config .#monad` pulls them with no local build.

## Writing Monad Code

### Declarations

```monad
// Inductive type
type Maybe A { some (a: A), none }

// Struct-like type (single-constructor: prefer struct -- style rule 1)
struct Point { x : I64, y : I64, z : I64 := 0 }   // := default value

// Type class with constraint and default implementation
class [Functor M] Monad (M: Type -> Type) {
    def bind (a: M A) (f: A -> M B) : M B
}
class Show A {
    def show (a: A) : String := "<generic>"
}

instance Functor Maybe {
    def map f m := match m { some a => some (f a), none => none }
}
instance myShow : Show I64 { def show x := "int" }   // named instance

def add (a: I64) (b: I64) : I64 := a + b
def identity {A : Type} (x: A) : A := x               // implicit parameter
```

### Do notation and lets

`do { ... }` (or a `{ ... }` def body) desugars through `Monad.bind`.
Statements: `let x <- m` (bind), `let x := v` (let), `return v`
(`Monad.pure`), or a bare expression. Separate statements with `;`.

- **Outside do-notation** (`:=` bodies) a `let` REQUIRES `in`:
  `let x := 10 in x + 1`.
- **Nested `return` is not supported** — extract it, or wrap the branch in
  its own `do { ... }`.
- A `let x <- ...` inside a do-block inside a `match` arm is a bad shape:
  give each stage its own small `def` instead (this is also how you dodge
  the checker's nested-match limitation below).

### Match, records, literals

```monad
match m { some a => a, none => default }     // sum types: positional is fine
match v { { x, .. } => x }                    // structs: prefer field patterns
{ x := 1, y := 2 }                            // struct literal
[a, b, c]                                     // List literal
r"no \n escapes"  r#"with " inside"#          // raw strings: backslashes literal
```

Numeric literals: `42` (I64), `42u8`/`i32`/`u64`..., `3.14` (F64), `0xFF`.
`'c'` char literals parse but `Char` has no operations — do not use it.

### Gotchas that bite

- **Reserved keywords cannot be field/param names** (`class`, `type`,
  `match`, `if`, `in`, `fn`, ... — see `RESERVED_KEYWORDS` in
  `core/src/parser.rs`). One keyword in a `(name: Type)` position cascades
  into a misleading `unexpected: Eof` at the NEXT declaration. Rename the
  field (`cls`, `kind`).
- **Annotated lambda parameters need parens**: `fn (s : String) => s`, not
  `fn s : String => s` (a parse error).
- **Match on two different type variables**: avoid nested `match` on
  `ParseResult A` inside a match on `ParseResult B` (`A != B`) — the
  checker cannot handle it. Extract per-type helper defs.
- **A struct field added breaks every POSITIONAL match on that struct**, at
  runtime, with no diagnostic naming the site (`expected 9 constructor
  fields, got 10`). Prefer field patterns or `value.field`; when you add a
  field, `grep` for positional matches.
- **Bare struct literals in argument/`return` position** can compile to
  garbage self-hosted; bind to an annotated local first
  (`let r : T := { ... } in ...`), or move the literal into its own def with
  a declared return type. Annotated literals are safe anywhere.
- **`String.slice`/`drop` are byte-oriented** and return `""` when an offset
  lands mid-character; `'` (0x27) is below 0x80 so slicing at its index is
  always safe.

### Imports

```monad,check
// `::` separates use-path segments; the first segment names a MOTE or `lib`.
use std::process {exec_cmd}

// Open a NAMESPACE (keeps `.`): make defs available without their prefix.
open IO {println}

def status : IO Unit := do {
    let rc <- exec_cmd "true" [];
    println (I64.to_string rc)
}
```

- A bare `use greet` is an error: name the mote (`use example::greet`) or
  write `use lib::greet` for this mote's own.
- Brace items are NAME PATHS matched against declarations' own spelling:
  `use std::list {List.intercalate}` (dotted), not `{intercalate}`.
  Constructors are the one bare-name exception. `use std::process
  {exec_cmd}` binds bare `exec_cmd`.
- Avoid qualified `module::name` TERM references at call sites — the
  self-hosted compiler does not resolve them yet; import the name instead.
- `use prelude` is an error (the prelude is ambient, auto-loaded).

## Attributes and Operators

Attributes come before visibility: `#[test] pub def ...`, never
`pub #[test] def ...`.

| Attribute | Meaning |
|---|---|
| `#[native "name"]` | Declares a Rust/C-native function (below) |
| `#[test]` | Run via `monad test` |
| `#[partial]` | Parser-table function (loops as ordinary code) |
| `#[terminating]` | Suppresses the termination check where it is too weak |

Operators (precedence low→high): `|>`/`<|` (5), `>>=` (10), `<*>` (15),
`<|>` (20), `||` (25), `&&` (30), `==`/`!=` (40), `++` (50), `>>`/`<<` (60),
`+`/`-` (65), `*`/`/` (70), `.` (12, right; also path concatenation).
Declare with `infix:13 (>>=) := Monad.bind`. `x.f` desugars to `Type.f x`
(receiver type prepended); an `x.y.z` chain on a local binding is sugar for
field access.

## Modifying the Compiler

| Concern | File |
|---|---|
| Syntax | `core/src/parser.rs` + `core/src/parser/` |
| Term/AST representation | `core/src/term.rs` + `core/src/term/` |
| Type checking | `core/src/core_check_module.rs`, `core_unify.rs` |
| Evaluation | `core/src/core_eval.rs` |
| Natives | `core/src/core_native.rs` (`exec_native` dispatch) |
| Lowering to IR | `core/src/lower_core_ir.rs`, `core_ir.rs` |
| Self-hosted codegen | `lang/src/codegen/` (emit.mo, ir.mo, natives.mo, validate.mo) |
| Module loading / motes | `core/src/term/module.rs`, `lang/src/module.mo`, `lang/src/mote.mo` |

The self-hosted pipeline: parse → scope → elaborate → typecheck → codegen
(LLVM IR → llc → clang, via `llvm/src/link.mo`). Both compilers must agree
on any surface change; a divergence usually shows up only in the
self-compiled binary, so `devenv tasks run monad:bootstrap-compile` is the
gate for anything touching `lang/`, `runtime/`, `init/` or `std/`.

## Testing and Memory Discipline

```bash
cargo test -p monad-core <name>      # one Rust test (cheap iteration)
monad test std/src/process_tests.mo  # one Monad test file
monad test std                       # directory sweep
scripts/check-docs.sh                # type-check md/AGENTS code fences
```

**A whole-corpus check or full `cargo test --release` can exhaust system
memory when name resolution regresses** — it has hard-restarted machines.
The safeguards, in order:

1. Run heavy commands under a kernel-enforced cap (exit 137 = the signal):

   ```bash
   systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
       cargo run --release -- check init std
   ```

   A polling watchdog does NOT work — allocation spikes finish between
   polls. Use the cap.
2. One cargo invocation at a time. Narrow the scope (`check init` is cheap,
   `check init std` is where blow-ups first show; `cargo test -p monad-core
   --lib <name>` beats the full run). Bound parallelism:
   `cargo test -j 2 -- --test-threads=2`.
3. Bisect by narrowing the target, not by widening the cap.

Tests for `std/` modules live in `std/` (`std/src/<module>_tests.mo`), never
in `init/`. A `#[test]` inside a file re-exported by `std/src/lib.mo` (or
`init/`'s) is undiscoverable — that is why test files are separate. Use
`use std::test` / `Test.assert` for assertion-style tests.

## Adding Native Functions

A native needs **four wiring touchpoints** (plus a fifth when the runtime
signature differs). Wiring only the first two compiles and fails at runtime.

1. **Declare it** in a `.mo` file; mark `pub` if another mote imports it:

   ```monad
   #[native "function_name"]
   pub def function_name (args: Types) : ReturnType
   ```

2. **Interpreter**: `core/src/core_native.rs` — an `exec_native` dispatch
   arm. `PURE_NATIVES` is only for effect-free natives.
3. **Compiled backend**: `runtime/src/runtime.c`, beside the existing
   helpers (the function generated code calls).
4. **Codegen**: `lang/src/codegen/natives.mo` — `native_op_table` (only for
   natives whose direct calls should inline), `native_runtime_fn_name` (the
:   `NativeWrapKind` — below), and `runtime_declarations` (the `declare`, or
   the call-target gate fails the compile).
5. **Verify in BOTH backends** — `validate_no_unwired_natives` catches a
   missing `natives.mo` entry at compile time, but NOTHING catches a missing
   `runtime.c` implementation until a compiled binary calls it. Working only
   interpreted is the classic failure.

### The IO wrapping rules

- A native declared `IO A` returns its raw payload; the C side returns the
  payload and `NativeWrapKind.io_passthrough` (emit.mo) wraps it as
  `IO.mk (RawIO.io raw)`. On the Rust host, `io_wrap` does the same.
- A native declared `RawIO A` returns the payload wrapped once as
  `RawIO.io raw` (`raw_io_passthrough` in codegen, `raw_io_wrap` in
  `core_native.rs`). Pair it with a thin `.mo` wrapper that builds the
  user-facing type:

   ```monad
   #[native "proc_read"]
   priv def proc_read (c : Child) (stream : I64) : RawIO (Result String (Option String))

   pub def Proc.read_line (c : Child) : IO (Result String (Option String)) :=
       IO.mk (proc_read c 0)
   ```

   Prefer this split for new native families: the C stays a raw payload
   producer, and the `.mo` wrapper owns naming, defaults and the
   user-facing type.
- **Merge twin natives behind an I64 flag rather than duplicating them** —
  `proc_read`'s stream flag (stdout/stderr) and `proc_wait`'s kill flag
  (reap only / SIGKILL-then-reap) are the standing examples. The dispatch
  arm, the wrap-kind entry and the `.mo` declaration move together.
- Share C helpers instead of copying loops (`monad_build_argv` serves both
  `monad_exec_cmd` and `monad_proc_spawn`).

## Style Conventions

4-space indent, lowercase for functions/variables, uppercase for
types/classes, `//` comments.

1. **Single-constructor types are `struct`s**, not `type X { mk ... }` —
   they gain named-field construction, dot access and update syntax at zero
   cost (identical match syntax).
2. **Use struct literals, dot access, named args** once a type is a
   `struct`: `{ f := v }`, `x.field`, `{ base with field := v }`; in match
   arms prefer `{ field1, field2, .. }` over positional. Positional is fine
   for multi-constructor sums.
3. **No type-prefixed field names** (`cr_ctx`, `mcr_blocks`) — the struct
   already namespaces them.
4. **Avoid nested `if`** — use `match` for multi-way dispatch, `&&`/`||` to
   combine conditions.
5. **Delete dead/duplicated code** in files you are already touching.
6. **Prefer a real map lookup over an `if beq x "a" else if beq x "b"` chain**
   for genuine key→value dispatch. Self-hosted, use the `str_map_*` /
   `modpath_map_*` helpers, not the `Map` class (its instance resolution has
   known bugs). Measure before converting a table that is rebuilt per call.
7. **Call the standard library directly** — no one-line forwarder shims
   (`def empty := List.empty`). Pin inference with a local annotation when
   a position has no expected type.
8. **Prefer literal syntax**: `[a, b]`, `(a, b)`, `{ f := v }` over
   constructor calls that spell out the data structure — except the bare
   struct literal in argument/return position (see Gotchas).

Doc comments (`///`) are parsed and kept for tooling. Write them on public
declarations.

## Workflow

1. **Reproduce first**; minimize the failing case; identify the stage
   (parse error / elaboration free-var error / `TypeError` / eval error /
   missing native / `unreachable!` panic).
2. **TDD**: write the failing test, fix, confirm pass. Parser tests:
   `core/src/parser/test/`; eval tests in `core_eval.rs`; Monad tests in
   the owning mote (`init/src/tests.mo`, `std/<module>_tests.mo`, ...).
3. `cargo fmt && cargo test` before committing.
4. Small, focused commits — one logical change each. Update the relevant
   plan in `plans/` when a feature lands.

When assumptions fail or tests break unexpectedly: explain the root cause
before proceeding; ask for direction rather than silently picking a fix.

### Committing

- Message format: `scope: msg` or `scope/sub: msg`
  (`scripts/check-commit-msg.sh`). Never include a `Claude-Session:` trailer.
- Always commit with hooks enabled — **never `git commit --no-verify`**.
  Hooks: rustfmt, clippy, shellcheck, docs-check, commit-msg.
- Run `cargo fmt` BEFORE committing: if the rustfmt hook modifies files,
  the commit was REJECTED, not made — retry with `git add` + commit, and
  verify with `git log -1`.
- The two whole-corpus sweeps — `cargo test --release` and `monad check init
  std examples lang cli llvm runtime build motes` — run in CI, not hooks
  (`.github/workflows/ci.yml`); do not pay them per commit locally, but run
  them before pushing anything that touches the compiler.
- When an agent: the user saying "don't run tests" includes not committing.

### Finishing a plan

When a plan item or plan is done and its checks pass, finish it through a PR:

1. **Open the PR**: push the branch, then open a PR against `main` whose
   description headlines what changed and why, taken from `<base>...HEAD`
   (`git log <base>..HEAD`, `git diff <base>...HEAD`); list the checks run.
2. **Review it**: read the full `gh pr diff <n>`, then post the review to the
   PR itself — `gh pr review <n> --comment --body-file -`, or
   `gh pr comment <n> --body-file -` if GitHub rejects a self-review — with
   findings anchored to file:line.
3. **Fix by fixup**: one `git commit --fixup=<target-sha>` per finding, hooks
   enabled (fixup subjects are exempt from the `scope:` rule). Never edit a
   `fixup!` subject: autosquash matches it verbatim.
4. **Squash and push**: `GIT_SEQUENCE_EDITOR=true git rebase -i --autosquash
   <base>`, rerun the checks the findings move, then
   `git push --force-with-lease private HEAD:<branch>`. The PR head is the
   squashed result; no fixup commit is left on the branch.
