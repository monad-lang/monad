# Monad Language Developer Guide

This document explains how to modify the Monad language codebase and write correct Monad code.

**IMPORTANT**: All development changes (code, tests, modules) should happen in the
**current worktree directory** (i.e., the working directory where `cargo` commands
are run). Do not switch to other worktrees (e.g., `../monad/`, `../monad-main/`)
unless explicitly instructed. The current worktree contains the branch and
codebase under active development — changes to other worktrees may target
a different branch and cause confusion.

## Project Structure

```
/home/anderscs/src/monad/
├── core/              # Rust compiler/interpreter
│   ├── src/
│   │   ├── parser.rs    # Lexer/parser
│   │   ├── term.rs     # AST and term definitions
│   │   ├── eval.rs     # Evaluator
│   │   │   ├── type.rs    # Type checker
│   │   │   ├── native.rs  # Native function implementations
│   │   │   └── constraint.rs # Constraint solver
│   │   └── main.rs     # CLI entry point (deprecated, use cli/)
│   └── Cargo.toml
├── cli/              # CLI entry point
│   └── src/main.rs
├── wasm/             # WebAssembly bindings
├── init/             # Standard library
│   ├── prelude.mo     # Basic types (Bool, List, Option, etc.)
│   ├── io.mo         # IO operations
│   ├── term.mo        # Term manipulation
│   ├── parser.mo      # Parser combinators
│   ├── string.mo      # String operations
│   ├── init.mo        # Init module with From class
│   └── tests.mo       # Standard library tests
├── std/
│   └── test.mo        # Test utilities (Test.assert)
├── examples/         # Example programs
├── bench/            # Standalone .mo micro-benchmarks (Bench.now/Bench.report,
│                     # #[test]-driven) -- deliberately NOT swept by the
│                     # pre-commit hook's `test init std lang examples`, since
│                     # benchmarks are for occasional manual measurement, not
│                     # every-commit correctness checking
├── slow_tests/       # Real #[test]s, deliberately NOT swept by the pre-commit
│                     # hook (same exclusion mechanism as bench/ -- outside its
│                     # fixed `init std lang examples` directory list). Five
│                     # files, moved here purely for cost (measured directly,
│                     # `cargo run --release -- test init std lang examples
│                     # slow_tests --json`, to be 684s of the corpus's 747.5s
│                     # total, 91.5% -- one single test (test_typecheck_lang_
│                     # main) alone was 544.5s, 72.9% of everything):
│                     #   - typecheck_init_tests.mo/typecheck_std_tests.mo/
│                     #     typecheck_lang_tests.mo all pass `check_deps=false`
│                     #     (target-only) to `elaborate_loaded_modules`
│                     #     (`lang/module.mo`) -- so checking `lang/main.mo`
│                     #     in test_typecheck_lang_main body-type-checks only
│                     #     `lang/main.mo`'s own top-level decls, NOT its
│                     #     dependencies' bodies (dependencies only
│                     #     contribute signatures to scope). `check_deps=true`
│                     #     exists (see `elaborate_loaded_modules`'s own doc
│                     #     comment) but is NOT currently used anywhere,
│                     #     including here or by the real `check`/`compile`/
│                     #     `test` CLI commands -- turning it on for
│                     #     `lang/main.mo`'s own full closure (≈2200 decls,
│                     #     including this self-hosted compiler's own
│                     #     richly-recursive AST types) caused unbounded
│                     #     memory growth (28GB+ RSS and still climbing);
│                     #     root cause under investigation, see
│                     #     `bootstrapping/check-deps-memory-blowup.md`.
│                     #     typecheck_init_tests.mo/typecheck_std_tests.mo
│                     #     are kept as separate per-file tests regardless
│                     #     of whether `check_deps=true` ever becomes safe to
│                     #     default on: a per-file failure here is far more
│                     #     useful for pinpointing WHICH file broke than one
│                     #     aggregate pass/fail.
│                     #   - parser_file_tests.mo/scope_all_tests.mo: not
│                     #     redundant with anything -- they exercise the
│                     #     parser/scope-builder directly, a different code
│                     #     path from type-checking.
│                     # Moved here specifically so a future CI (not yet
│                     # built, see self-hosted-compiler-perf.md's own
│                     # AGENTS.md item 9 follow-up note) can be the safety
│                     # net for this coverage, since local pre-commit no
│                     # longer affords it. Still real, runnable tests
│                     # (`cargo run -- test slow_tests`) -- just for
│                     # manual/CI use, not the fast local commit path.
└── plans/            # Symlink to external repo with design plans
```

## Building and Running

```bash
# Build the compiler
cargo build --package monad-core

# Run a Monad file
cargo run -- run examples/hello.mo

# In devenv shell also monad-rs as an alias for cargo run:
monad-rs run examples/hello.mo

# Run with debug output
cargo run -- run examples/hello.mo -- --debug

# Run #[test] annotated definitions
cargo run -- test init/tests.mo

# Run the bootstrapped cli in lang/main.mo
bootstrap

# Compile to native binary in devenv shell
bootstrap compile examples/hello.mo

# Use the REPL (interactive, requires repl feature)
cargo run -- repl
```

### Use `--release` for self-hosted-compiler workloads

Running `lang/main.mo` (the self-hosted compiler) interprets a real
compiler pipeline on top of the reference compiler's own `core_eval` —
e.g. `cargo run -- run lang/main.mo -- check lang/main.mo` (self-hosted
compiler checking itself) took 223s in a debug build vs 99s
`--release` — a 2.2x speedup here (smaller than the 10-15x speedup
`--release` gives the reference compiler's own `check`/`run` on an
ordinary `.mo` file, since the self-hosted path's cost is dominated by
interpreter dispatch/allocation overhead that `-O` optimizes less
aggressively than typical Rust control flow). Prefer
`cargo build --release` + `target/release/monad-rs run lang/main.mo --
...` (or `cargo run --release -- run lang/main.mo -- ...`) over a plain
debug build for any workload that runs `lang/main.mo` against a large
file or corpus, rather than iterating on the reference compiler itself.

## Writing Monad Code

### File Structure
Monad source files use the `.mo` extension.

### Type Definitions

```monad
// Inductive type (algebraic data type)
type Maybe A {
    some (a: A),
    none
}

// Struct-like type (with field default and multiplicity)
struct Point {
    x : I64,
    y : I64,
    z : I64 := 0,   // default value
    !name : String  // linear field (!) or affine (?)
}

// Type with type parameter
type Either E A {
    left (e: E),
    right (a: A)
}
```

### Sort Universe Hierarchy

Monad has a cumulative Russell-style universe hierarchy. Every valid type lives at some
`Sort n` level. The hierarchy prevents paradoxes like Type : Type.

| Sort level | Surface syntax | Meaning |
|---|---|---|
| `Sort 0` | `Prop` | Universe of propositions (proofs, equality statements) |
| `Sort 1` | `Type` | Universe of small types (data, functions, i.e., `Bool`, `I64`, `List A`) |
| `Sort 2` | `Type 1` | Universe of larger types (`Sort 0`, `Sort 1`, type families) |
| `Sort n` | `Type (n-1)` | nth universe level |

**Formation rule**: `Sort n : Sort (n+1)` — every sort is itself a term of the next higher sort.

**Cumulativity**: A term of type `Sort n` can be used where `Sort m` is expected, for any `m ≥ n`.

#### Propositions vs Booleans

This is a critical distinction in dependent type theory:

| Concept | Type | Values | What it means |
|---|---|---|---|
| `Prop` (Sort 0) | `Sort 1` (Type) | Types like `True`, `Eq A a b` | A **type** of proofs / a proposition |
| `Bool` | `Sort 1` (Type) | `true`, `false` | A **computational** boolean |
| `True` (the proposition) | `Prop` (Sort 0) | `trivial` | The trivially true proposition (unit type in Prop) |
| `Eq A a b` | `Prop` (Sort 0) | `refl a` | Proof that `a = b` |

- **`True` is a TYPE, not a Bool value.** It lives in `Prop` (`Sort 0`). Its constructor is `trivial : True`. Use `True.trivial` to construct a trivial proof.
- **`Bool` is a computational type with values `true` and `false`** (note lowercase). `Bool : Type` (`Sort 1`).
- In test functions, the return type is `Bool` (a computational value that can be asserted), not `True` (a proof that cannot be evaluated at runtime).
- All definitions return types that live in `Sort 1` (Type) or higher unless explicitly annotated with `: Prop`.

```monad
// Bool is a regular inductive type in Sort 1 (Type)
type Bool {
    true,
    false
}

// True is a proposition in Sort 0 (Prop) — it's a TYPE, not a value
type True : Prop {
    trivial
}

// Eq is propositional equality in Sort 0 (Prop)
type Eq (A : Sort 1) (a : A) (b : A) : Prop {
    refl : Eq A a a
}
```

When writing Monad source files:
- Test files use `use std.test` (not `use prelude` — the prelude is auto-loaded as `'prelude`)
- The prelude is imported automatically — no explicit `use prelude` needed
- Module paths for the standard library: `std.test` for testing, `io` for IO, etc.

⚠️ **Reserved keywords cannot be used as field names** in `type` constructor parameters (`(name: Type)`) or `struct` field names (`name: Type`). The parser's `identifier` combinator rejects reserved keywords. Common offenders: `class`, `type`, `match`, `if`, `def`, `let`, `in`, `use`, `open`, `struct`, `instance`, `fn`, `do`, `return`, `for`, `quote`, `with`, `infix`, `else`, `then`. Use a synonym instead (e.g., `cls` for `class`, `kind` for `type`). The reserved keyword list is in `RESERVED_KEYWORDS` at `parser.rs:60-63`.

### Class Definitions (Type Classes)

```monad
// Similar to Haskell type classes
class Functor (F: Type -> Type) {
    def map (f: A -> B) : (F A) -> F B
}

// With constraints
class [Functor M] Monad (M: Type -> Type) {
    def bind (a: M A) (f: A -> M B) : M B
}

// With default implementation
class Show A {
    def show (a: A) : String := "<generic>"
}
```

### Instance Definitions

```monad
instance Functor Maybe {
    def map f m :=
        match m {
            some a => some (f a),
            none => none
        }
}

// With type arguments
instance [Add A] Add (List A) {
    ...
}

// Named instance
instance myShow : Show I64 {
    def show x := "int"
}
```

### Function Definitions

```monad
def add (a: I64) (b: I64) : I64 := a + b

def factorial (n: I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)

// With implicit parameters
def identity {A : Type} (x: A) : A := x

// Do block syntax (alternative to :=)
def greet (name : String) : IO Unit {
    println name
}

// Do block with multiple statements
def multi_step : IO Unit {
    println "Step 1";
    let value := 42;
    println "Done"
}
```

### Do Notation

Do notation provides syntactic sugar for monadic operations. It can be used with the `do { ... }` syntax or directly in function definitions using `{ ... }`.

```monad
// Standard do notation
def example : IO Unit := do {
    let x <- get_value;
    let y := x + 1;
    return y
}

// Do block in function definition (equivalent)
def example : IO Unit {
    let x <- get_value;
    let y := x + 1;
    return y
}
```

Do blocks support three kinds of statements:

| Statement | Syntax | Desugars To |
|-----------|--------|-------------|
| Bind | `let x <- monadic_expr` | `Monad.bind monadic_expr (fn x => ...)` |
| Let | `let x := value` | `let x := value in ...` |
| Return | `return value` | `Monad.pure value` |
| Expression | `expr` | `Monad.bind expr (fn _ => ...)` |

Multiple expressions must be separated by semicolons:

```monad
def multi : IO Unit {
    println "first";
    println "second"
}
```

Do notation does not (yet) support nested return statements.

<!-- TODO: Give accurate parser errors for this scenario. -->
<!-- TODO: Support more convenient do notation with nested return. -->

```monad
// WRONG return needs to be top level. Will cause cascading parse error.
def nested : IO Unit {
    println "first";
    if b then return a
    else return c
}

// CORRECT use a second do-block
def nested : IO Unit {
    println "first";
    if b then do {
        return a
    }
    else do {
        return c
    }
}

// CORRECT extract return
def nested : IO Unit {
    println "first";
    return if b then a
    else c
}
```

### Comments

```monad
// Line comment
/* Block comment */
```

### Docstrings

```monad
/// Documentation for the following declaration
def greet (name : String) : IO Unit {
    println name
}

/// Module-level documentation (at top of file)
```

Docstrings (`///`) are parsed and stored on declarations. They are retained through module loading for tooling and inspection.

### Lambda Expressions

```monad
fn x => x + 1
\ x => x + 1
ꟛ x => x + 1
```

### Backtick Operators

```monad
x `f` y   // Equivalent to f x y
```

Identifiers in backticks are treated as infix operators (like Haskell).

### Type Annotations

```monad
(expr : Type)
```

Any term can be annotated with its type using `(term : Type)` syntax.

### Let Expressions

`let` expressions come in two forms depending on context:

**Outside do-notation** (in `:=` def bodies): the `in` keyword is REQUIRED.

```monad
let x := 10 in
x + 1

// With type annotation
let x : I64 := 10 in
x + 1

// Chained lets: each let needs its own `in`, nesting rightward
let x := 10 in
let y := x + 5 in
x + y
```

**Inside do-blocks** (`{ ... }` def bodies): statements use `;` separation, NO `in`.

```monad
def example : I64 {
  let x : I64 := 10;
  let y : I64 := x + 5;
  x + y
}
```

**Common mistake**: using `:=` body syntax with multi-statement `let ... ; let ... ; expr` without `in`.
This is invalid. Either use `{ }` do-block syntax or nest with `in`.

```monad
// WRONG — no `in`, no `{ }`:
def example : I64 :=
  let x : I64 := 10;
  x + 1

// CORRECT — do-block:
def example : I64 {
  let x : I64 := 10;
  x + 1
}

// CORRECT — let ... in:
def example : I64 :=
  let x : I64 := 10 in
  x + 1
```

### Numeric Literals

```monad
42        // I64 (default)
42i8      // I8
42i16     // I16
42i32     // I32
42i64     // I64
42u8      // U8
42u16     // U16
42u32     // U32
42u64     // U64
3.14      // F64 (default)
3.14f32   // F32
3.14f64   // F64
0xFF      // I64, hex notation
0xFFu32   // U32, hex notation
```

### Match Expressions

```monad
match value {
    some a => a,
    none => default
}
```

### Record / Struct Literals

```monad
{ x := 1, y := 2 }
```

### Operator Declarations

```monad
infix:13 (>>=) := Monad.bind
infix:20 (++) := List.append
```

### Module Imports

```monad
// Load a module, listing exactly the names needed
use io {IO}

// Open namespace. Make defs available without given prefix.
open IO {println}
```

`{*}` imports/opens everything explicitly; a bare `use`/`open` (no braces) still parses but is deprecated in favor of an explicit filter.

### Native Functions

Call Rust functions from Monad using the `#[native "..."]` attribute:

```monad
#[native "add"]
def add (a: I64) (b: I64) : I64
```

## Attributes

Declarations can be annotated with `#[...]` attributes:

```monad
#[native "function_name"]   // Declare a Rust-native function
#[test]                     // Mark as a test (run via `cargo run -- test <file>`)
```

Attributes come before visibility: `#[test] pub def ...`, not `pub #[test] def ...`.

## Operators

All operators and their precedences:

| Operator | Precedence | Assoc | Description |
|----------|-----------|-------|-------------|
| `.` | 12 | Right | Dot macro (path concatenation / method call) |
| `\|>` | 5 | Left | Forward pipe (`x \|> f`) |
| `<\|` | 5 | Right | Backward pipe (`f <\| x`) |
| `>>=` | 10 | Right | Monad bind |
| `<*>` | 15 | Left | Applicative apply |
| `<\ | >` | 20 | Left | Alt/choice |
| `\|\|` | 25 | Right | Boolean OR |
| `&&` | 30 | Right | Boolean AND |
| `==`, `!=`, `=` | 40 | Left | Equality / assignment |
| `++` | 50 | Right | Append |
| `>>`, `<<` | 60 | Left | Shift / fork |
| `+`, `-` | 65 | Left | Add / subtract |
| `*`, `/` | 70 | Left | Multiply / divide |

## Method Call Syntax

```monad
x.fun        // Desugared to A.fun x (where A is the type of x)
x.fun args   // Desugared to A.fun args x
```

Method calls are desugared in the type checker at `type.rs:701-740`. The receiver type is extracted and prepended to the method name.

## Dot Macro

The `.` operator (`x.y.z`) is treated as a compile-time macro that concatenates module paths into a single `Var` reference (at `eval.rs:167-200`). This is how module paths like `List.append` work.

## Constraint Solver

Recursive instance constraints (e.g., `instance [Show A] Show (List A) { ... }`) are handled by the constraint solver at `core/src/eval/constraint.rs`. It uses a visiting set to detect and resolve cyclic constraint dependencies during instance resolution.

## Key Language Features

1. **Dependent Types**: Types can depend on values (using `{x : Type}` forall syntax)

2. **Type Classes**: Like Haskell, with automatic instance resolution

3. **Linear Types**: Compile-time enforcement via `!` (linear) and `?` (affine) multiplicity annotations on parameters

## Modifying the Compiler

### Parser (`core/src/parser.rs`)
- Add new syntax in the parser combinators
- Reserved keywords are defined in `RESERVED_KEYWORDS`

### List Literal Desugaring
List literals `[a, b, c]` are desugared in `desugar_list_literal` (parser.rs:620) to nested `FromListLiteral` calls:
```
[a, b, c]  =>  (FromListLiteral.cons a) ((FromListLiteral.cons b) ((FromListLiteral.cons c) FromListLiteral.empty))
```
The AST structure is `app(app(cons, elem), acc)` — **NOT** `app(cons, app(elem, acc))`.
For a single element: `[x]` => `app(app(cons, var("x")), empty)`

### Evaluator (`core/src/core_eval.rs` + `core_native.rs`)
The legacy tree-walking evaluator (`core/src/eval.rs`'s old `eval`/`eval_test`) has been removed — the closure-based `CoreTerm` evaluator is now the crate's only evaluator, reached via `check_all_modules_capturing_core` (`core_check_module.rs`) → `lower_core_ir::lower_program` → `core_eval::force_global`.
- Beta reduction/closure application happens in `core_eval.rs`'s `force_global`/`apply`
- Native functions are executed in `core_native.rs`'s `exec_native`
- To trace evaluation, add tracing in `core_eval.rs` rather than a stray `println!` — `run --debug` already prints the checked type (`Eval type ...`) before evaluating

### Type Checker (`core/src/core_check_module.rs` + `core_unify.rs`)
- Module-level type checking and de Bruijn/`MetaId`-based unification
- `core/src/eval/type.rs` still holds shared pre-lowering infra used by the checker above: `elaborate_decls` (implicit `Forall` insertion), `check_strict_positivity`, the `TypeError` type and its diagnostics rendering — despite the `eval/` path, this file is not part of the (removed) legacy evaluator

## Testing

```bash
# Run Rust tests
cargo test

# Run a specific test
cargo test core_check_module::
cargo test core_eval::
```

### Running Monad Tests

```bash
# Run tests from a single file
cargo run -- test init/tests.mo

# Run tests from an entire directory (recursively finds all .mo files with #[test])
cargo run -- test init/

# Run all test suites
cargo run -- test init/ && cargo run -- test examples/
```

The test runner supports both files and directories. When given a directory, it recursively scans for `.mo` files and runs any definitions annotated with `#[test]`, reporting pass/fail.

### No Personal-Machine Details or Hardcoded Paths

Never hardcode a contributor's local machine details into code — absolute
paths under a personal home directory, machine-specific usernames, or
anything else that only exists on one person's checkout. This includes test
fixtures: resolve repo files relative to `CARGO_MANIFEST_DIR` (see
`core_check_module.rs`'s `repo_search_paths`), never via an absolute path.
A real instance of this broke CI while passing locally, since the hardcoded
path only existed on its author's machine.

### Pre-commit

The pre-commit config (`.pre-commit-config.yaml`) is managed by Nix via `git-hooks.nix`. Do NOT edit it directly. Instead, modify the Nix configuration that generates it. The `monad-tests` hook currently runs `cargo run --release -- test init std lang examples` (see `devenv.nix`) — recursing into every `.mo` file under those four directories, `lang/tests/` included. If this hook fails, run the same command directly (or narrow to one directory, e.g. `cargo run -- test lang/`) to see all test failures.

## Development Workflow

Always use Test-Driven Development (TDD):
1. Write a **failing test** first
2. Implement the fix/feature
3. Run tests to confirm pass
4. Run `cargo fmt && cargo test` to ensure formatting and all tests pass
5. Make a **small, focused commit** with a descriptive message

Always make small, incremental changes. Each commit should be a single logical change.
After each commit, confirm the test suite still passes.

When a feature or bug fix is implemented, update the relevant plan in `plans/` to reflect the completed work. Mark completed tasks, add notes on the approach taken, and capture any design decisions or tradeoffs discovered during implementation.

When implementing a non-trivial new language feature or stdlib addition, add a corresponding example to `examples/` demonstrating its use. The example must pass `cargo run -- test examples/` — do not add broken examples. If an existing example already covers the feature, add a test case to the existing example file instead of creating a new one.

## Common Patterns

### Creating New Types

Add to `init/prelude.mo`:
```monad
type MyType {
    constructor (field: Type)
}
```

### Adding Native Functions

1. Add Rust implementation in `core/src/eval/native.rs`
2. Declare in a `.mo` file:
```monad
#[native "function_name"]
def function_name (args: Types) : ReturnType
```

## Standard Library

### `init/prelude.mo`
- Basic types: `Bool`, `I64`, `I8`, `I16`, `I32`, `I64`, `U8`, `U16`, `U32`, `U64`, `F32`, `F64`, `String`, `Void`, `Any`, `Nat`, `List`, `Option`
- Type classes: `Add`, `Sub`, `Mul`, `Div`, `BEq`, `BOrd`, `Functor`, `Applicative`, `Monad`, `Show`, `Append`, `FromListLiteral`, `DefaultValue`
- Operators: `+`, `-`, `*`, `/`, `==`, `!=`, `&&`, `||`, `++`, `|>`, `<|`, `>>=`, `<*>`, `<|>`
- Functions: `Bool.not`, `Bool.and`, `Bool.or`, `Option.get_or_default`, `List.is_empty`, `List.append`, `List.first`, `List.last`, `List.tail`, `List.flatten`, `fun_apply`, `apply_fun`

### `init/string.mo`
- `String.concat`, `String.length`, `String.get`, `String.is_empty`

### `init/init.mo`
- `From` class for type conversion

### `std/test.mo`
- `Test.assert` for assertion-based testing

### Module Dependency Boundaries

**`init/` must never depend on `std/`.** The `init/` directory contains core language definitions (prelude, io, types) that are foundational. The `std/` directory contains higher-level modules that depend on `init/`.

- `std/` modules may `use` `init/` modules (e.g., `use io`)
- `init/` modules must **NOT** `use` `std/` modules
- **Tests for `std/` modules go in `std/`**, not in `init/` — `init/tests.mo` must not import from `std/`

When adding a new `std/` module with tests, place the test file within `std/`:
```bash
cargo run -- test std/   # runs all std/ tests including new ones
```

## Style Conventions

- Use 2 spaces for indentation
- Lowercase identifiers for functions/variables
- Uppercase for types/type classes
- Prefer descriptive names
- Comment with `//` (never `--`)

### Rust Code Style

- Always use `use` statements at the top of the file instead of fully qualified paths
- Group `use` statements logically (standard library, external crates, local modules)
- Example: prefer `use crate::term::{Identifier, Term, param};` over `crate::term::Identifier`

## Workflow

When assumptions fail, tests break unexpectedly, or you hit hard errors:
1. **Explain the root cause** to the user before proceeding
2. **Ask for input** on how to resolve — don't silently pick a fix
3. Present options with tradeoffs when there are multiple approaches
4. Only proceed once the user confirms direction

## Troubleshooting & Known Issues

### Class Method Resolution in `def_refs`

**Problem**: Class methods (e.g., `BEq.beq`) were being added to `def_refs` with their type signature as the term. This caused `find_ref` to find them before instance resolution could happen in `find_any_ref`, resulting in "expected function found for {A : Type} -> ..." errors at evaluation time.

**Root cause**: Two places were adding class methods to `def_refs`:
1. `load_decl` (line ~558) — when loading `Decl::Type` for classes
2. `get_def_refs` (line ~1123) — via `get_class_method_defs`

**Fix**: Class constructors should NOT be added to `def_refs`. Only the class name itself should be in `def_refs`. Class methods should only be in `class_defs`, so that `find_any_ref` falls through to instance resolution.

**Key invariant**: `def_refs` should contain concrete terms (implementations), NOT type signatures. Class methods are abstract — their concrete terms come from instances.

### Instance Resolution Flow

When resolving a name like `BEq.beq` or `==`:
1. `resolve_name` → `find_any_name_ref` → `find_any_ref`
2. `find_any_ref` first tries `find_ref` (def_refs) — if found, returns immediately
3. If not in def_refs, tries `find_class_def` (class_defs) — if found, derives instance key and calls `find_instance`
4. `find_instance` matches the instance key against registered instances

**If a class method is in def_refs, step 2 returns the type signature term and instance resolution never happens.**

### BEq Type Signature Bug

The `BEq` class in `init/prelude.mo` originally had:
```monad
class BEq A {
    def beq : A -> B -> Bool  // WRONG: B is unbound
}
```
Should be:
```monad
class BEq A {
    def beq : A -> A -> Bool  // CORRECT
}
```

### Reserved Keywords in Field Names Cause Cascading Parse Errors

**Problem**: Using a reserved keyword (e.g., `class`) as a constructor field name in `type` or `struct` declarations causes a misleading parse error. The error appears at the *next* declaration with "unexpected: Eof", because the parser rejects the keyword inside `(name: Type)` syntax, fails to find the closing `}`, and consumes all remaining input looking for it.

**Root cause**: `cons_param` (`parser.rs:329`) and `struct_field_parser` (`parser.rs:1346`) both use `identifier`, which rejects reserved keywords. When a field like `(class: ModulePath)` is encountered, the keyword fails to parse, the branch backtracks, and `type_expression` consumes the `:` as a type annotation instead, leaving the `}` unsatisfied.

**Fix**: Rename the field (e.g., `class` → `cls`). See the warning under [Type Definitions](#type-definitions) for the full list of reserved keywords.

### Lambda Parameter Type Annotations Require Parens

**Problem**: Writing `fn s : String => s` (an annotated lambda parameter with no parens around `s : String`) produces a parse error — this is not, and never was, valid syntax. Note this is *not* about lambda expressions in argument position; it fails the same way as a standalone `def` body too.

**Root cause**: `lam_param` (`core/src/parser.rs:394`) parses a bare identifier as an unannotated param (`param(i, Hole)`), or an *entirely parenthesized* `(name : Type)`/`(name : Type := default)` for an annotated one — mirroring `def`'s own parameter syntax. There is no bare `name : Type` form.

**Fix**: Wrap the annotated parameter in parens:

```monad
// BROKEN — no parens around the annotated param:
fn s : String => s

// CORRECT:
fn (s : String) => s
```

Lambda expressions (both annotated-with-parens and unannotated) parse and
type-check fine as **direct arguments in function application**, including
to generic/polymorphic functions — confirmed with `map_parse`/`bind_parse`:

```monad
map_parse (fn (s : String) => s) (tag "x") "xy"   // works
map_parse (fn s => s) (tag "x") "xy"               // works
bind_parse (tag "x") (fn (s : String) => tag "y") "xy"  // works
```

### Struct Field Access via Dot Syntax

Writing `loc.offset` (or a chain, `line.span.offset`) on a *locally bound* value works and is sugar for a bare `{ }` match: `loc.offset` desugars to `match loc { {offset} => offset }`, resolved against `loc`'s type at type-check time — so it works for any single-constructor type (not just `struct`-declared ones), not a fixed "method call" scheme. This only applies when the left of the first `.` is a local binding (a `def`/lambda parameter, a `let`); a bare `Module.name`-shaped path (no local binding by that name in scope) still resolves as an ordinary qualified reference, exactly as before:
```monad
struct Location { offset : I64, line : I64, column : I64 }

def get_offset (loc : Location) : I64 := loc.offset   // works

// Equivalent, if you'd rather write it out:
def get_offset (loc : Location) : I64 :=
    match loc {
        { offset, .. } => offset
    }
```
Dot access on an arbitrary non-identifier expression (e.g. `(mk_point 1 2).x`) isn't supported yet — only a chain of bare identifiers starting from a local binding.

### Debug `println!` in Type Checker Masks Real Errors

**Problem**: `core/src/eval/type.rs` contains debug `println!()` statements in `match_resolve_type_inner` (line ~1596: `"{left} != {right} arg=... ret=... vars=..."`) and `check_free_vars` (line ~1479: `"{detected} != {current_type}"`). These produce noisy output during normal type checking and can mask the actual error when diagnosing parse/type failures.

**Fix**: Remove these `println!` calls before production use. They are leftover debugging aids and are not guarded by any log level.

## Parser Combinator Library (init/parser.mo)

### Status: In Progress

Working: `tag`, `eof`, `alt`/`<|>`, `many0`, `many1`, `char_in_string`, `is_digit`, `is_alpha`, `is_alphanumeric`, `is_space`, `is_ident_char`, `satisfy`, `char`, `digit`, `alpha`, `space`, `take_while`, `opt`, `preceded`, `terminated`, `delimited`, `recognize` — 23/23 tests pass.

The self-hosted parser at `lang/parser.mo` provides a self-contained copy of the foundation types (`ParseResult`, `ParseError`) and combinators (`tag`, `alt`, `many0`, `many1`, `take_while`), char predicates, keyword check, identifier parser, whitespace skimmer, and number parser — 7/7 tests pass.

Key patterns when writing self-hosted Monad code:
1. **Avoid long `||` chains** (>10 operations) — the operator precedence climber slows down exponentially. Use nested `if/else` chains or split into helper functions (see `is_alpha_lower`/`is_alpha_lower2` pattern in `lang/parser.mo`).
2. **Avoid deep `else if` chains** (>15 levels) — the parser depth causes extreme slowdown. Split into multiple helper functions (max ~14 `if/else` per function).
3. **Avoid `use` for `init/parser`** — module loading produces "duplicate key" warnings that break `String.starts_with` and other native functions in test contexts. Make the parser file self-contained instead.
4. **Use `open TypeName`** — constructor names (like `success`/`fail`) are not available without opening the type.
5. **Type checker limitation with `ParseResult`** — matches on `ParseResult A` must avoid nested matches on `ParseResult B` where `B != A` (different type variables). Use separate functions to extract values at each level.

### Known Type Checker Issues

1. **`open` doesn't propagate**: `open ParseResult` within `parser.mo` doesn't affect external modules. Inner opens are not applied to module exports. Functions using `open`-ed constructors must be defined inside the same module. Workaround: bind results to a typed parameter before matching (see `many0`/`many1` implementation pattern in `init/parser.mo`).
2. **Forall inference on polymorphic combinators**: The type checker correctly instantiates implicit forall parameters on functions like `map_parse` and `bind_parse`, whether called with a concrete named function (`map_parse id_str (tag "x") "xy"`) or an inline lambda, annotated or not (`map_parse (fn s => s) (tag "x") "xy"`) — confirmed directly. If a combinator call fails with "Variable mismatch, expected ... found {B : Type} -> {A : Type} -> ...", the cause is elsewhere (e.g. a genuine type mismatch); it is not a lambda-argument limitation.
3. **`Map.insert`/`Map.lookup` (typeclass method dispatch) can fail at
   runtime with `eval error: scope: scope: Map.lookup not found` inside
   deeply-recursive self-hosted-compiler code paths** — specifically
   observed when a self-hosted function using `Map`/`BOrd` class methods
   (`std/map.mo`'s `instance [BOrd K] Map BTreeMap`) gets called
   repeatedly through `lang.module`'s dynamic module-loading/dependency-
   walk (`load_module_with_dependencies`, exercised by
   `slow_tests/typecheck_lang_tests.mo`'s `test_typecheck_lang_main`, the
   only test that exercises that runtime path). Not reproduced when the
   same `BTreeMap` usage is type-checked directly (e.g. `lang/json.mo`
   alone) — the failure is specific to this recursive/dynamic-scope
   context, not to `BTreeMap`/`BOrd` in general. A workaround exists
   (bypass the `Map`/`BOrd` class methods and call
   `BTreeMap.insert_loop`/`BTreeMap.lookup_loop` directly with the
   ordering passed as **plain function values**, e.g. built from
   `String.lt`/`String.gt` rather than `BOrd.lt`/`BOrd.gt`) — but see the
   next item before reaching for it.
4. **`BTreeMap` is markedly SLOWER than a plain `List` + linear scan for
   the small collection sizes typical in this self-hosted compiler's own
   code, once everything runs through the tree-walking evaluator.**
   Measured directly: replacing `lang/module.mo`'s `List ModulePath` +
   `list_contains` cycle-detection sets with `BTreeMap ModulePath Unit`
   (using the plain-function-value workaround from the item above, to
   dodge the dispatch bug) took `test_typecheck_lang_main` from 2.1s to
   29s; additionally converting `elaborate.mo`'s `union_ids`/`id_member`
   the same way pushed it to 53s — a ~25x regression overall, not an
   improvement, despite the asymptotic complexity genuinely being better
   on paper (O(n log n) vs O(n²)). The self-hosted interpreter's per-call
   overhead for tree-node allocation/rebalancing dominates at the
   collection sizes actually seen here (module counts, free-variable
   lists — tens, not thousands), so the crossover point where `BTreeMap`
   would actually win is never reached in practice. **Do not replace
   `List`+linear-scan with `BTreeMap` in self-hosted (`lang/*.mo`) code
   without measuring end-to-end wall-clock time first** (e.g.
   `time cargo run -- test slow_tests/typecheck_lang_tests.mo`) — Big-O
   analysis alone is not a reliable guide to real performance here.
5. **`self-hosted-compiler-perf.md` phase-timing infra**: `lang/module.mo`'s
   `check_file_cached` now wraps its three phases (scope/dep resolution,
   strict parse, typecheck) with `Bench.now`/`Bench.report` calls gated
   on `verbose` — `run lang/main.mo -- check <files> --verbose` prints
   `scope=`/`parse=`/`check=` timings per file, silent otherwise. This
   is distinct from the Rust-level `--benchmark` flag (which only times
   the outer per-file load, not phases *inside* the self-hosted checker
   while it runs) — use this tool to answer "which phase dominates"
   before touching self-hosted-checker performance, the same way item 4
   above already demonstrates for data-structure choices.
6. **Measured, not worth it: flattening `HashMap`'s 16-way bucket
   dispatch** (`std/map.mo`'s `HashMap.get_bucket`/`set_bucket`,
   originally a single 16-deep `if U64.beq N idx` chain). Splitting it
   into two <=8-deep tiers (mirroring `lang/parser.mo`'s
   `is_alpha_lower`/`is_alpha_lower2` pattern, itself a real, proven win
   for *parser* code) was tried and measured directly with a dedicated
   isolated micro-benchmark (`bench/hashmap_bucket_dispatch.mo` — pure
   `get_bucket`/`set_bucket` call volume, decoupled from `HashMap`'s own
   hashing/allocation cost), reproduced across two independent runs at
   two sizes (n=50000/200000): unflattened `set_bucket` 485-489ms/
   1950-1956ms vs. flattened 638ms/2568ms; unflattened `get_bucket`
   461-468ms/1837-1840ms vs. flattened 512ms/2045ms — a consistent
   **~10-30% regression**, not an improvement. Root cause (inferred, not
   separately measured): splitting into `get_bucket_lo`/`hi`
   (`set_bucket_lo`/`hi`) trades fewer `U64.beq` comparisons per call for
   one extra function-call boundary plus an extra `U64.lt` dispatch check
   on *every* call, and this interpreter's per-call overhead outweighs
   the comparisons saved at this chain depth (16 is apparently still
   short enough that the `>15 levels` rule's *depth*-driven slowdown
   hasn't kicked in yet; splitting adds a *call*, which is the more
   expensive operation here). Reverted — `std/map.mo`'s `get_bucket`/
   `set_bucket` remain the original single 16-way chain. Kept
   `bench/hashmap_bucket_dispatch.mo` as standing infrastructure so this
   isn't re-investigated blind. A second data point (after item 4's
   BTreeMap regression) that a proven win in one part of this
   interpreter (parser recursion depth) doesn't automatically transfer to
   another (hot-path dispatch call count) — measure per case.
7. **Native `string_lt`/`string_gt`/`string_hash` fast paths**
   (`core/src/core_native.rs` + `init/string.mo`): `String.beq` already
   had a native path (`string_eq`, plain `&str == &str`); `String.lt`/
   `String.gt`/`String.hash` didn't — they were self-hosted `.mo` code
   that converted both operands through `String.to_list` (materializing
   a full `List U8` linked list) before comparing/folding, even though
   `Identifier`/`ModulePath`'s `BOrd`/`Hashable` instances
   (`lang/types.mo`) delegate to them on every scope-`HashMap` op. When a
   self-hosted function's cost is dominated by an allocation-heavy
   conversion rather than genuine self-hosted logic, check whether a
   native already exists for a sibling operation (here, `string_eq`)
   before assuming the self-hosted version is the only option. The
   self-hosted implementations were kept (renamed
   `..._selfhosted`/`bytes_lt_selfhosted`/etc., not deleted) as the
   intended long-term implementation to switch back to once more of the
   compiler is self-hosted and the interpreter itself is faster (see
   item 8) — this native fast path is explicitly temporary and
   pragmatic, not a retreat from self-hosting.
8. **Tail-call optimization in `core/src/core_eval.rs`**: `eval`'s `App`
   case called `apply`, whose `Closure` branch called
   `eval(&body, &extended, ...)` — a real recursive Rust call despite
   being syntactically a tail call; `Match`'s dispatch had the identical
   shape. Every self-recursive closure application (an ordinary
   accumulator-style `.mo` loop) grew the native Rust stack by a frame
   per iteration — confirmed by `bench/scope_lookup.mo` stack-
   overflowing at n≈1000 even under 64MB worker-thread stacks.
   `eval` is now a `loop` over owned `(cur_ir: IrRef, cur_env: EnvRef)`
   state — `App` applying to a `Closure`, and `Match` dispatching to an
   arm, `continue` the loop (reassign state, `Arc::clone`, O(1)) instead
   of recursing. Every *other* recursive `eval` call (an `App`'s
   `fun`/`arg`, a `Match`'s scrutinee, `Con`/`Ntv`'s argument list) stays
   real Rust recursion on purpose — bounded by *static* source-term
   nesting depth, not *dynamic* call count. This means genuinely
   non-tail-recursive `.mo` code (e.g. `len xs = match xs { cons _ t =>
   1 + len t, ... }`) still consumes O(N) Rust stack depth, same as any
   language with TCO — the 64MB worker-thread stack (`core/src/lib.rs`)
   stays in place as a backstop for that case, it did not become
   unnecessary. Standing proof this works:
   `core_eval::tests::test_tail_recursive_countdown_survives_a_million_iterations_on_default_stack`,
   a self-recursive `Global` closure driven to n=1,000,000 under a
   *default*-sized test-thread stack. Bonus, not the primary goal:
   `test_typecheck_lang_main` (the compiler typechecking its own ~50-file
   corpus) dropped from 600.5s to 409.6s (~32% faster) from fewer
   allocations (no per-call `apply`/`dispatch` Rust frame).
9. **Two independent, real fixes for `merge_scope_data`/`PreludeInitBase`
   found and landed in parallel (on separate branches, later reconciled
   by rebase) — both kept, since they address genuinely different parts
   of the same cost.** Item 8's phase timing found the SCOPE phase
   dominating per-file check time by up to ~90x over the CHECK phase
   (e.g. `init/id.mo`: scope~4.3s vs. check~0.05s) — NOT the CHECK phase
   where `union_ids`/`free_vars` (`lang/elaborate.mo`, `lang/types.mo`)
   live, confirming `union_ids` is not worth optimizing.
   - **Fix A** (`lang/module.mo`'s `load_module_with_dependencies_and_
     prelude_cached`): `extract_all_dependencies_go`'s `visited`
     accumulator was seeded with `base_covered` (the shared
     `PreludeInitBase`'s already-loaded module set) so the walk would
     skip re-visiting it — but that function returns `visited` verbatim
     once its to-visit queue empties, so every call returned the
     *entire* `base_covered` set back as "extra deps to load", and the
     caller reloaded (re-parsed, re-scope-built) all of prelude+init
     from scratch for every single file — precisely the O(N*D)
     redundancy `PreludeInitBase` was built to eliminate. Fixed by
     seeding `visiting` instead of `visited`: in this walk's
     non-backtracking shape (a dependency's own subtree is processed via
     the same sequential recursive call that continues on to its
     siblings, never popped) the two parameters are already functionally
     equivalent "seen" sets for skip purposes, so this changes nothing
     about what gets skipped, only what gets correctly returned as
     empty/small instead of the whole base.
   - **Fix B** (`lang/module.mo`'s `merge_scope_data`, `std/map.mo`):
     even with Fix A landed, `merge_scope_data base_sd merged_extra`
     still merges the two `ScopeData`s' `def_refs` `HashMap`s every
     file — the original implementation did this via `HashMap.to_list
     dr1` (a full walk+concat of every bucket) followed by one
     `Map.insert`-equivalent call per entry to fold it into the other
     side, effectively rebuilding a `HashMap` from scratch bucket-by-
     bucket-and-back on every call regardless of how large `dr1` was.
     Replaced with `HashMap.merge_buckets`: merges two `HashMap`s
     directly bucket-by-bucket via 16 `List.append` calls, needing NO
     re-hashing at all — safe specifically because both sides already
     hashed their keys with the same function, so a key in bucket `i` on
     one side is always in bucket `i` on the other. Needs no
     `[Hashable K, BOrd K]` constraint either (unlike the `to_list`+
     refold approach it replaces), so it also sidesteps the
     `[Constraint]`-annotated-function class-method-dispatch limitation
     `std/map.mo` already documents elsewhere — and needs no empty-`sd2`
     short-circuit either (a fixed 16 bucket-pair appends is already
     cheap enough regardless of size).
   - `bench/hashmap_bucket_dispatch.mo` (item 6) was tried FIRST as a
     general "flatten `HashMap`'s dispatch" fix and found not to help;
     these two much more targeted fixes (WHERE the redundant work
     happened, and HOW one specific merge was implemented) are what
     actually delivered the win — a reminder that a hot function's own
     internals aren't the only place a real win can hide; how often and
     against what it's actually called can matter just as much.
   - Combined effect, both fixes together, measured after reconciling
     them via rebase: `test_typecheck_lang_main` dropped from 545.05s
     (the item-8/TCO baseline) to **97.07s — an 82% reduction, ~5.6x
     faster** — essentially identical to Fix B's own standalone number
     (97.38s, measured before this rebase), not additionally improved by
     Fix A on this specific end-to-end metric. That's expected, not a
     sign Fix A is redundant: Fix B's bucket-merge is a fixed 16-append
     cost regardless of `merged_extra`'s size, so shrinking
     `merged_extra` (Fix A's effect) doesn't move `merge_scope_data`'s
     own cost further once it's already cheap — but Fix A still matters
     on its own terms, for the cost `merge_scope_data` never touches at
     all: `load_dependency_scopes` actually parsing/scope-building
     `extra_deps`' files. `test_typecheck_lang_main`'s own dependency
     shape (mostly prelude+init-covered, little genuine `lang/`-internal
     `extra_deps` per file) just doesn't happen to exercise that
     saving much; files with real non-base dependencies still benefit
     from Fix A the way its own commit measured directly (`std/show.mo`
     scope phase 4224ms → 712ms; `lang/module.mo` 418.8s → 367.3s).
     Full corpus `check init std examples`: 51 files, 181 errors,
     unchanged from before either fix (confirmed via a direct isolated
     stash comparison on this exact combined commit), completing in
     well under a minute where the pre-item-8 baseline could not finish
     within a 590s timeout at all. Remaining known gap, explicitly out
     of scope for both fixes: `PreludeInitBase` only covers prelude+
     init, not a file's dependencies on *other, non-base* corpus files
     during a multi-file run (real, non-base `use` dependencies within
     `lang/`/`std/` still pay a real, uncached reload cost) — a
     separate, larger architectural change (a whole-corpus, not just
     prelude+init, module-scope cache) and a natural next target for a
     future performance pass.
10. **Whole-corpus module-scope cache** (`ModuleScopeCache`,
    `lang/module.mo`) closes item 9's own remaining gap: a growing,
    whole-`run_check`-invocation cache of already-loaded non-base
    dependencies' `ScopeData`, threaded through `run_check_loop`/
    `check_file_cached`/`load_module_with_dependencies_and_prelude_
    cached` the same way `PreludeInitBase` is, except mutable rather
    than fixed. Fixes the exact redundancy item 9 measured but didn't
    address: `lang/types.mo` was independently loaded 54 separate
    times in one multi-file run (54 files `use lang.types`), now served
    from cache after the first. Keyed on `ModulePath` (grep-verified
    safe for the current corpus — only two bare, non-dotted `use`s
    exist anywhere, each resolved from exactly one `base_dir`, no
    observed collision; flagged as a structural, not observed, risk in
    the code, with resolved-path keying noted as a cheap fast-follow if
    it's ever needed). Correct because this codebase's dependency
    loading is flat, not recursive: each dependency's `ScopeData` is
    built from only its own decls, independent of who asked, so a
    cached value is bit-identical to a fresh load; cycle detection
    (`extract_all_dependencies_go`'s `visiting`/`visited`) is completely
    untouched — the cache only changes HOW an already-decided-necessary
    dependency's value gets produced, never WHICH dependencies a caller
    needs. Verified: 1274/1274 self-hosted tests passed (baseline
    unchanged), real speedup on repeated-dependency scenarios (a 4-file
    sample's scope-phase times dropped 13-47% per file as later files
    hit the cache for shared deps). Deliberately NOT measured against
    `slow_tests/typecheck_lang_tests.mo`'s `test_typecheck_lang_main` —
    that test is a single flat dependency-closure walk from one call
    site (`load_module_with_dependencies`, not the `..._and_prelude_
    cached` path this cache lives on), so it cannot exhibit cross-file
    redundancy by construction; its own regression (see item 11) is a
    separate story.
11. **`test_typecheck_lang_main` regression (97.07s → 257.61s since
    item 9): investigated as two candidate causes, one fixed (small,
    real win), one measured and found to be diffuse organic growth,
    not a single fixable hotspot.**
    - **Candidate 1, fixed**: `build_scope_from_decls` (`lang/
      scope.mo`) does a second full pass over every module's decls
      (`alias_decls_in_scope`, added by the open/use bare-name-aliasing
      commit) even when that module has no `use`/`open` declarations
      at all to alias — pure wasted work for the ~12% of the corpus
      that's true of (grep-counted). Measured directly (temporary
      `Bench.now`/`Bench.report` instrumentation, since reverted):
      `alias_decls_in_scope` is ~29% of `build_scope_from_decls`'s own
      cost on a representative sample — real, but `build_scope_from_
      decls`'s own cost is itself a minority of a file's total "scope"
      phase (most of which is I/O/parsing). Fixed with a cheap
      `decls_have_aliasable_decls` pre-check (O(decls), O(1) per decl —
      a bare tag match, no `ScopeData` work) that skips the whole
      second pass when it would do nothing. Small, safe, and
      correctness-preserving by construction (nothing to alias means
      the skipped pass would have been a no-op regardless) — not
      claimed to explain the bulk of the 97s→257s regression on its
      own, given it only fires for ~12% of module loads.
    - **Candidate 2, measured and NOT the cause — the CHECK phase's own
      per-declaration cost has grown, but not through the mechanism
      first suspected.** `lang/typecheck/infer.mo`'s `find_inductive_
      for_cases_by_constructor` (a linear scan over every inductive in
      the fully-merged scope, ~218+ `type` declarations corpus-wide)
      looked like a strong candidate by code-reading alone — the CHECK
      phase is now often 2-4x LARGER than the SCOPE phase for real
      files (`lang/pretty.mo`: scope≈15-29s, check≈57-83s across
      several runs), the opposite of this section's own item 9
      assumption (based on a tiny `init/id.mo` file where scope
      dominated ~90x over check). Instrumented directly (temporary
      counters on both the fast path and this fallback, since
      reverted) and ran against `lang/pretty.mo` (60 `match`
      expressions, the worst measured `check=` offender): **zero**
      calls to either path were logged — this function isn't even
      being reached by the self-hosted checker's current coverage for
      this file. The hypothesis is disproven, not just unconfirmed.
      Followed up with per-declaration timing instead (temporary,
      since reverted): costs are roughly UNIFORM (~600-900ms) across
      most of `pretty.mo`'s 103 declarations, not concentrated in a
      handful of outliers — consistent with organic, distributed
      complexity growth in `type_check`'s own per-declaration work
      (skolemization now extended to more decl kinds, match-case
      validation, struct-literal/struct-update checking, Pi-chain
      handling all landed since item 9's 97.07s measurement) rather
      than one identifiable, fixable hot path. **Do not chase a single
      fix here without new evidence** — this needs either a much
      deeper per-node profiling pass inside `type_check` itself (a
      separate, larger investigation) or acceptance that this is the
      accumulated cost of genuine feature growth. Recorded here so it
      isn't re-investigated blind from the same starting hypothesis.
12. **`SharedStr` (Arc-backed zero-copy string slicing) + parser/type-
    checker follow-ups — the parser's own cost model, never previously
    examined, turned out to hold the largest lever in this whole history.**
    Full writeup: `plans/implementations/shared-str-and-typecheck-
    optimization.md`. Three independent tracks, one root-cause Rust
    change plus two self-hosted-only tracks extending items 9-11's
    already-proven patterns:
    - **Track 1 (root cause, Rust)**: `IrLit::Str` (`core/src/core_ir.rs`)
      was a plain owned `String` — `string_slice`/`string_drop`
      (`core/src/core_native.rs`) both did `s.get(range).unwrap_or("")
      .to_string()`, a full byte copy on every call. The self-hosted
      parser (`lang/parser.mo`, `lang/parser/combinators.mo`) threads
      "the rest of the source file" through nearly every grammar
      function this way, consuming it a few bytes at a time — so parsing
      a file of length N cost `O(N)+O(N-1)+...+O(1) = O(N²)`, independent
      of grammar complexity. Fixed by a new `SharedStr` type
      (`core/src/shared_str.rs`): `Arc<str>` backing + a `(start, end)`
      byte-range view, so `slice`/`drop` become O(1) (bump a refcount,
      adjust two `usize`s) instead of copying. `Arc`, not `Rc` — the
      evaluator runs on real OS threads (`run_tests_parallel`,
      `force_global_with_timeout`'s per-call thread spawn,
      `std/concurrent`'s real-thread runtime; `Value` is asserted
      `Send + Sync` at compile time), the same tradeoff `Env`
      (`core_value.rs`) already made and documented. `read_file` is the
      key construction site: the whole file's content becomes ONE
      backing allocation, and every subsequent `slice`/`drop` during
      parsing shares it. Small, mechanical blast radius despite touching
      the runtime's value representation: 5 files, ~35 call sites total
      (`core_ir.rs`, `core_native.rs`, `lower_core_ir.rs`,
      `eval/meta_reflect.rs`, `lib.rs`) — most natives (`string_eq`,
      `string_hash`, `string_length`, ...) needed zero changes since they
      only ever read via a derived `&str`.
    - **Track 2 (self-hosted parser, `.mo`-only)**: `take_while`/
      `take_while_loop` (`lang/parser/combinators.mo`) used to build its
      matched-text accumulator via per-character `String.concat acc ch`
      — an independent, compounding O(L²) cost (for a token of length L)
      on top of Track 1's fix. Rewritten to track the original input
      alongside the shrinking remainder and take exactly ONE
      `String.slice` when the predicate first fails, instead of L
      accumulator concats — benefits every `take_while`-based scan
      (identifiers, numbers, whitespace/comment-skipping) at once, not
      just call sites that discard the matched text. Also: `is_digit`
      (`lang/parser/char_preds.mo`) rewritten from a fresh-list-plus-
      closure-plus-`List.any` scan to a plain `if/else` chain matching
      every sibling predicate in the file (the already-established,
      already-proven-faster pattern); `op_lookup_prec`/`op_lookup_rassoc`
      (`lang/parser/core.mo`) merged into one `op_lookup_entry` scan so
      `expr_climb_op_prec`/`expr_climb_op_rhs_ws` (`lang/parser.mo`) walk
      `op_table` once per operator token instead of twice.
    - **Track 3 (self-hosted type checker/scope/module, `.mo`-only,
      independent of 1/2)**: `ScopeData.inductives` (`lang/types.mo`)
      converted from `List Inductive` to `HashMap ModulePath Inductive`
      — the identical, already-proven move item 4/`def_refs` made
      (commit `532df61`). `scope_data_find_inductive`
      (`lang/scope.mo`) was a linear scan over every inductive in the
      merged scope (~218+ corpus-wide) reached on the PREFERRED,
      non-fallback path added by the match-case-validation (`0dbc3f2`)
      and struct-literal (`0303aee`) commits — both landed after item 9's
      97.07s baseline, and exactly the kind of "diffuse organic growth"
      item 11's own instrumentation was consistent with but didn't
      isolate (item 11 counted calls into the OLD fallback function,
      which this new preferred path bypasses entirely). `.classes`, the
      sibling field, stayed a `List` — confirmed no by-name lookup
      anywhere in the corpus, so no read-side benefit from converting
      it. Track B's `decls_have_aliasable_decls` no-op-skip guard
      (already landed, see item 11) was applied inside
      `build_scope_from_decls` but NOT at two sibling call sites in
      `lang/module.mo` (`load_module_with_dependencies`,
      `load_module_with_dependencies_and_prelude_cached`) that
      unconditionally re-ran the identical "outer aliasing" pass — the
      FIRST of these is exactly `test_typecheck_lang_main`'s own call
      path (item 10 explicitly noted it couldn't measure that test
      against the whole-corpus module-scope cache for this reason).
      Extended the same guard to both. Also added a `ys`-empty
      short-circuit to `list_append`/`merge_instances` (`lang/module.mo`,
      mirrored in `lang/scope.mo`) — `merge_scope_data`'s two real call
      sites always pass the large shared-base side first and the
      small/often-empty side second, the opposite of the ONLY existing
      fast path (`xs = List.empty`), so `class_defs`/`instances`/
      `classes`/`infixes`/`conflicts` were fully walked and reallocated
      on every file checked for zero benefit — same bug shape item 9's
      Fix B fixed for `def_refs`, just never extended past that one
      field.
    - **Measured** (release build, `--verbose` phase timing +
      `test_typecheck_lang_main` as the standing end-to-end benchmark,
      same methodology as items 8-11): parse-phase time roughly HALVED
      across every file size tried, Track 1+2 combined
      (`init/id.mo`: 78ms→35ms; `lang/pretty.mo`: 6681ms→2827ms;
      `lang/json.mo`: 4000ms→1901ms — a consistent ~55% reduction
      regardless of file size, confirmed via a real git-stash before/
      after rebuild, not just a single post-fix run). All three tracks
      combined: `test_typecheck_lang_main` (the item 8-11 regression
      benchmark) dropped from **262.30s to 105.31s — a 60% reduction,
      ~2.5x faster** — back down near item 9's original 97.07s baseline
      despite all the feature growth items 10/11 identified as the
      regression's cause. Verified: `cargo test` 625/625 (616 baseline +
      9 new `SharedStr` unit tests); full corpus
      `cargo run --release -- test init std lang examples slow_tests`
      1274/1274, identical to baseline; `cargo run --release -- check
      init std lang examples` unchanged at 2 pre-existing errors/7
      pre-existing warnings (confirmed via the same check against an
      unmodified baseline — none of these are new).
    - **Follow-up (Track 4): `string_body_loop`'s O(L²) accumulator,
      confirmed and fixed — gap partially closed, not fully.** The gap
      flagged above (parse-phase superlinearity: `init/id.mo` 28
      lines→35ms vs. `lang/pretty.mo` 885 lines→2827ms, ~80x time for
      ~32x lines) was traced to `lang/parser/string.mo`'s
      `string_body_loop` (string-literal body scanning), which built its
      accumulator via one `String.concat acc ch` per character — the
      exact pre-Track-2 `take_while` shape, deliberately left alone at
      the time because `\`-escapes genuinely change content
      byte-for-byte and can't collapse to a single final slice the way
      `take_while`'s non-escaping scan could. Fixed by tracking where the
      current *unescaped run* started (`run_start`) alongside the
      shrinking `input`, paying for one `String.slice` + `String.concat`
      per run boundary (a `\` or the closing `"`) instead of per
      character — a typical un-escaped string literal is now ONE slice,
      zero concats; a string with E escapes is O(E) concats instead of
      O(L). Measured: parse-phase time dropped further on top of Track
      1+2 (`lang/pretty.mo` 2827ms→2045ms, `lang/json.mo`
      1901ms→1706ms), and the scaling ratio improved (`id.mo` 28
      lines→33ms vs. `json.mo` 1213 lines→1706ms is now ~52x time for
      ~43x lines, close to linear — vs. `pretty.mo`'s remaining ~62x
      time for ~32x lines, still mildly superlinear, likely other
      per-character accumulation this pass didn't chase further). This
      did **not** move `test_typecheck_lang_main`'s end-to-end number
      (105.71s, within noise of the 105.31s Track 1-3 baseline) —
      confirms item 11's own conclusion still holds: for this benchmark
      the `check` phase dominates total cost by ~50-100x over `parse`
      (e.g. `lang/pretty.mo`: scope=21866ms, parse=2045ms,
      check=97276ms), so a parse-only fix, however real, is invisible at
      the end-to-end level. Verified: full corpus
      `cargo run --release -- test init std lang examples slow_tests`
      1274/1274 unchanged; `cargo run --release -- check init std lang
      examples` unchanged at 2 pre-existing errors/7 pre-existing
      warnings.
    - **Track 3d (from the original plan doc), measured and skipped**:
      `check_file_cached`'s duplicate file read (strict parse re-reads
      what `build_scope_with_deps_and_prelude_cached` already read once
      for the lenient parse, plus a handful of `file_exists` stats) is,
      per this pass's own `--verbose` numbers, on the order of a few
      syscalls against a `check`/`scope` cost measured in **tens of
      seconds per file** — orders of magnitude too small to register.
      Recorded as a deliberate no-op rather than re-investigated blind
      later; the actual lever, if this history continues, is item 11's
      already-identified one: a per-node profiling pass inside
      `type_check` itself.
13. **The "per-node profiling pass" item 11/12 called for, actually done —
    and it found something nobody was looking for.** No `perf`/
    `flamegraph`/`samply` exist in this sandbox (confirmed); `valgrind`
    does, and needs no special privileges (binary translation, not
    `perf_events`). Two independent investigations, one Rust-level (via
    `valgrind --tool=callgrind`) and one self-hosted-level (via targeted
    ablation), against `test_typecheck_lang_main` (the standing item
    8-12 benchmark, ~86-106s depending on machine load run-to-run — the
    variance itself turned out to matter, see below).
    - **Getting the target right matters**: `monad-rs check <file>` (bare
      CLI) goes through `core/src/lib.rs`'s `check_files` →
      `term::module::load_module_from_text_typed` — a *separate*, legacy
      Rust-native tree-walking checker kept for parity, **not** the
      self-hosted `lang/*.mo` checker. `monad-rs test <path>` is the
      correct profiling target — it runs a self-hosted `#[test]` def
      through the real `CoreIr` evaluator.
    - **Rust-level, via callgrind (headline finding)**: profiled a small
      scratch `#[test]` (`typecheck_file "std/map.mo"`, mirroring
      `typecheck_lang_tests.mo`'s own helper) two ways — once fully
      instrumented from process start, once with `--instr-atstart=no`
      plus a live `callgrind_control -i on <pid>` toggle fired exactly
      when self-hosted test execution begins (after Rust-native bootstrap
      compilation of the ~32 loaded modules completes), to cleanly
      separate "checking+lowering the self-hosted compiler's own source"
      from "the self-hosted checker actually running." The isolated,
      bootstrap-free profile is **83-99% `malloc_consolidate`/
      `_int_free_chunk`/`free`/`unlink_chunk`/`BTreeMap::drop`** — i.e.
      the whole counted window is dominated by tearing down ONE large
      heap structure, not by `core_eval`/`exec_native`/actual checking
      logic (which combined don't even clear the 99%-cumulative
      threshold). Root cause: `LoadedModules` (`core/src/term/module.rs`)
      is `#[derive(Clone)]` over `modules: Map<ModulePath, Module>`
      where `Module` itself holds SIX more `Map`(`=BTreeMap`) fields
      (`defs`, `inductives`, `macro_defs`, `decl_gens`, `infix`, plus an
      `instances: Vec`) — i.e. every loaded module's ENTIRE checked AST.
      `evaluate_one_test_file`/`check_files` (`core/src/lib.rs`) each
      **deep-clone this whole registry once per checked/tested FILE**
      (`base_loaded.clone()`/`master_loaded.clone()`), and drop it again
      at file-scope exit. This is a *deliberate* correctness fix, not an
      oversight — the doc comment at `evaluate_one_test_file` explains it
      prevents cross-test-file bare-name collisions (confirmed against a
      real corpus case: `init`'s `foldable_tests.mo`/
      `foldable_tests_fold.mo` both declare `test_foldr_sum`) — but its
      performance cost was never measured until now, and a plain
      `#[derive(Clone)]` over nested `BTreeMap`s of full AST trees is the
      most expensive way to buy that guarantee. A cheaper fix preserving
      the same isolation (each file's own additions stay local, the
      shared base is never mutated in place) would replace `Map`/
      `BTreeMap` here with something structurally-shared (e.g. `im::
      OrdMap`, or wrap each field in `Arc` for copy-on-write), making the
      per-file clone O(1) instead of O(total loaded-corpus AST size) —
      **not implemented this pass** (investigation only), but the
      highest-confidence, best-understood lead this whole history has
      produced. Cost scales with `files tested × total corpus size`, the
      same "gets worse as the corpus grows, never fixed" shape as several
      other items here — for a single huge file (`test_typecheck_lang_main`
      itself, one file with one `#[test]`) it's a bounded one-time tax
      (small relative to that benchmark's ~86-106s total); for the FULL
      multi-hundred-file test/check suite it is paid once per file and
      was not separately quantified at that scale this pass.
    - **Rust-level, ruled out**: the two hypotheses this investigation
      started from — `Value::clone()` on `Con`/`PartialNtv` being an
      uncontrolled deep recursive copy (`Con`/`PartialNtv` hold
      `args: Vec<Value>`, not `Arc<[Value]>`, so every self-hosted
      `List`/`HashMap`/record clone is structural, not O(1)), and
      `Env::get` (`core/src/core_value.rs`) being an O(lexical-depth)
      pointer-chain walk — are both real but **negligible** here:
      `Env::drop_slow` (the closest attributable symbol) totals 0.19% of
      instructions combined across both variants in the full
      (non-isolated) profile; no `<Value as Clone>::clone` symbol clears
      even the smallest visible line (~0.01%) in either profile. Ruled
      out as significant factors for this benchmark, dwarfed by the
      `LoadedModules` clone/drop cost by 3-4 orders of magnitude.
    - **Self-hosted-level, via ablation — all ruled out**: `CoreIr` nodes
      carry no spans/names, and `force_global` only fires once per
      memoized global (not once per call), so callgrind can't attribute
      cost to a *self-hosted* function name — a pure-functional language
      also has no cheap way to add call counters without threading state
      through every signature. Used ablation instead (temporarily stub
      the candidate to a trivial O(1) wrong-but-non-crashing
      implementation, measure the wall-time delta on
      `test_typecheck_lang_main`, revert): stubbed
      `find_class_def_in_list`, `find_instances_by_class`,
      `scope_data_find_inductive_by_constructor` (`lang/scope.mo`),
      `unify`'s `Similar.similar` structural-walk fallback
      (`lang/typecheck/unify.mo`), and `struct_lit_find_field`
      (`lang/typecheck/infer.mo`) all at once — every one of these was a
      linear-scan sibling of an already-`HashMap`-converted field
      (`class_defs`/`instances` never got the `def_refs`/`inductives`
      treatment) or an unmemoized nested scan, exactly the bug shapes
      items 4/9/12 already fixed elsewhere. Result: **85.93s vs. an
      86.72s clean baseline — no measurable effect**, well inside this
      benchmark's own ~20s run-to-run machine-load noise band (observed
      86.72s and 105.71s for the *same* unmodified binary across
      different points in this session). All five ruled out as
      contributors to this benchmark's cost. `scope_find_local`/
      `nth_type`'s O(nesting-depth) walk (candidate 6) was NOT ablated —
      unlike the other five, it fires on every free/bound variable
      reference including ordinary global references, and stubbing it
      would break most of the corpus rather than just degrade gracefully
      — left unmeasured rather than guessed at; by analogy to the other
      five siblings all measuring null, and item 6's own prior finding
      that flattening loses to per-call overhead at this interpreter's
      typical scope depths, it's judged low-priority but is explicitly
      **not confirmed either way**.
    - **Bottom line**: the item 11/12 hypothesis that `type_check`'s own
      per-node logic hides a diffuse-but-real cost was not confirmed by
      this pass — everything self-hosted-level that could safely be
      measured came back null. The real, confirmed, actionable lead this
      investigation produced is Rust-level and outside `lang/*.mo`
      entirely: `LoadedModules`'s clone-per-file cost.
    - **Follow-up: fixed.** `Module`'s six AST-bearing fields (`defs`,
      `inductives`, `macro_defs`, `decl_gens`, `infix`, `instances`) and
      `LoadedModules`'s own `modules: Map<ModulePath, Module>` were
      `Arc`-wrapped (`core/src/term/module.rs`) — the same tool already
      used repeatedly on this branch (`SharedStr`'s `Arc<str>`, `Env`'s
      `Arc<Env>` chain), no new dependency. All six fields are private to
      `module.rs`, so the blast radius was fully contained: one
      constructor (`fn module(...)`) wraps each freshly-built map/vec in
      `Arc::new(..)`; the one live outer-map mutator (`add_module`) and
      the REPL-only `add_decl`/`get_module_mut` paths switched to
      `Arc::make_mut` (copy-on-write, free in practice since those values
      are always uniquely-owned at the point of mutation); every
      read-only accessor (`.defs()`, `.get_def()`, `LoadedModules::
      modules()`, ...) needed **no changes** — `&Arc<Map<K,V>>` derefs to
      `&Map<K,V>` at existing call sites. `Module::clone()` went from
      O(that module's own checked-AST size) to O(1) (a handful of `Arc`
      bumps); `LoadedModules::clone()`'s outer `BTreeMap` clone is now
      O(number of loaded modules) values that are themselves O(1) to
      clone, rather than O(total loaded-corpus AST size). Two more
      whole-registry clone sites inside the recursive module loader
      (`module.rs`, threading `loaded` by value through
      `load_decl_uses_modules`) and REPL/test-support clones (`lib.rs`,
      `core_check_module.rs`) all became cheap for free, no call-site
      changes needed. **Measured**: `cargo run --release -- test init
      std lang examples slow_tests` (the full corpus, ~100+ files, each
      paying the per-file clone this fix targets) dropped from
      **215.55s to 173.51s — a ~19.5% wall-time reduction** (`git stash`
      before/after, both 1274/1274 passing, unchanged). As predicted,
      `test_typecheck_lang_main` alone (one file, one clone) barely
      moved (86.72s→87.68s, within noise) — confirms the fix targets the
      per-FILE-tested cost specifically, not per-node checking cost.
      `cargo test` (all crates) and `cargo run --release -- check init
      std lang examples` both unchanged (625/625 core tests, 1 ignored;
      2 pre-existing errors/7 warnings). **Not fully explained**: the
      ~19.5% win, while real and worth keeping, is smaller than the
      83-99%-of-one-profile-window headline number might suggest —
      plausible explanation, not independently confirmed: some of that
      isolated-window `malloc`/`BTreeMap`-drop cost may belong to
      `core_check_module.rs`'s own per-file capture-key registries (the
      `BTreeMap<Atom, ModulePath>` machinery also visible in the
      original profile), built fresh once per file by `build_core_program`
      regardless of `LoadedModules`'s own clone cost — a DIFFERENT
      structure this fix didn't touch. Flagged as a possible next target,
      not chased further this pass.
14. **Follow-up to item 13's flagged remainder: found and fixed —
    `global_atom_paths` (`core_check_module.rs`), a `BTreeMap<Atom,
    ModulePath>` holding every known global across the whole corpus
    loaded so far, was fully cloned once per checked top-level `def`
    (`check_one_def_new`, twice — once for the per-def working copy,
    again when storing into `CoreProgram`'s `CheckedCoreDef.atom_paths`)
    and once per instance method (`check_one_instance_new` calls
    `check_one_def_new` once per method). With ~3,800+ defs across the
    corpus and a map that grows toward corpus size as checking proceeds,
    this is an O(defs × corpus-size) cost — the same "gets worse as the
    corpus grows" shape as item 13's `LoadedModules` bug, just at
    per-*def* rather than per-*file* granularity. Unlike `LoadedModules`
    (cloned-then-never-mutated, where `Arc`+copy-on-write sufficed),
    `global_atom_paths` is cloned-then-immediately-extended with new
    entries every time, so `Arc::make_mut` would trigger a full copy on
    the first insert anyway — no free win available from the same tool.
    **Fix**: added the `im` crate and introduced `AtomPathMap =
    im::OrdMap<Atom, ModulePath>` (`core/src/lib.rs`), scoped to exactly
    this one type family (NOT the general-purpose `Map<K, V>` alias,
    which covers many unrelated tables with no equivalent hot-path
    pressure — `StructFields.inductive_paths`, textually the same type
    but a separate, once-per-module, never-cloned table, was deliberately
    left as plain `BTreeMap`). `im::OrdMap`'s `.clone()` is O(1)
    (ref-counted structural sharing) and its `.insert`/`.extend` are
    O(log n) persistent updates instead of full copies, with an API
    (`.get`/`.contains_key`/`.insert`/`.extend`/`FromIterator`) close
    enough to `BTreeMap`'s to be a drop-in replacement at every existing
    call site (`core_check_module.rs`, `core_program.rs`,
    `raise_core.rs`, 5 signatures in `core_check.rs`,
    `lower_core_ir.rs`) — no logic changes anywhere, ~15 type-annotation
    edits total. **Measured**: `cargo run --release -- test init std lang
    examples slow_tests` (the full corpus, 1387/1387 passing unchanged
    before/after — corpus has grown since item 13's 1274/1274 count)
    dropped from **307.62s to 244.14s wall (-20.6%)**, and — a cleaner
    signal since wall time is subject to scheduling noise — **772.36s to
    511.47s in summed CPU-seconds (-33.8%)**. `cargo test` (627/627 core
    tests, unchanged) and `cargo run --release -- check init std lang
    examples` (2 errors/7 warnings, unchanged) both confirm no behavior
    change. **Not confirmed on the isolated benchmark**: unlike item 13,
    this fix's win doesn't show up on `test_typecheck_lang_main` run
    alone (`git stash` before/after, same session: self-reported test
    time 133.16s → 130.69s, within run-to-run noise) — the opposite
    pattern from item 13, where the per-*file* `LoadedModules` fix helped
    the single-file benchmark barely at all but the per-*def*
    `global_atom_paths` cost apparently doesn't dominate that one
    benchmark's own cost either, even though its dependency closure
    (`lang/main.mo` pulling in essentially all of `lang/`) is large.
    Separately: this session's baseline isolated run measured 133.16s,
    not the ~7-minute figure commit `7350f96`'s message cited for the
    same test — a large, unexplained discrepancy, not reproduced or
    chased further here (plausibly machine-load variance between
    sessions, given item 13's own note of ~20s run-to-run noise on this
    same benchmark — though a 5x gap is far outside that band and
    deserves its own look before being written off). The full-corpus
    number is the one that matters for the original complaint ("bootstrap
    compile takes many minutes" — i.e. checking/testing many files in one
    session, not one giant file in isolation), and it moved for real.
15. **Follow-up: the literal `bootstrap compile <file>` command has its OWN,
    much bigger, entirely separate bug — a diamond-dependency re-parse
    blowup in the self-hosted loader, not touched by items 13/14.**
    Prompted by a direct question ("does the self-hosted checker load
    modules once or several times?"). Found **two structurally different
    module-graph traversals** in `lang/module.mo`:
    - `extract_all_dependencies`/`extract_all_dependencies_go` (lines
      366-419) — a correct, single-flat-list, cycle-safe walk with a
      `visited` set checked BEFORE the expensive work (disk read + parse)
      at line 393/399. Backs `load_module_with_dependencies`, which backs
      `check` and `test_typecheck_lang_main`'s `typecheck_file` — i.e.
      everything items 13/14 measured. A module reachable via N import
      paths is loaded exactly once here; traced directly against
      `lang/types.mo` (47/57 `lang/*.mo` files import it) to confirm.
    - `load_dependencies_with_info` (lines 1958-1993) — backs
      `load_file_modules`, which is what `compile`, `pretty`, and `test`
      (the three self-hosted CLI subcommands OTHER than `check`) actually
      run on — confirmed by grep, `lang/main.mo` lines 63/243/374. Despite
      `load_file_modules` already computing the complete, deduplicated
      closure ONCE up front (line 1941), `load_dependencies_with_info`
      re-called `extract_all_dependencies` AGAIN (old line 1974, from a
      FRESH empty `visited` set) for every node the first time it's
      visited, to re-derive that node's own dependency list, then
      recursed into it — completely ignorant that the outer list already
      contains everything that re-walk would rediscover. Every module in
      the closure paid its own full parse-and-walk of its downward subtree
      once per ancestor that reached it in the recursion — a superlinear
      (Σ over the closure of each node's own subtree size) blowup, same
      shape as the already-fixed "54× `lang/types.mo` reload" cross-FILE
      bug (items 9-10's `ModuleScopeCache`), just a fresh instance of the
      same pattern inside an unrelated function, and entirely un-touched
      by anything in items 13/14 (which only improved `check`/
      `test_typecheck_lang_main`, both on the OTHER, already-correct
      traversal). This is the literal path `bootstrap compile <file>`
      (`devenv.nix`'s `bootstrap` script → `lang/main.mo compile` →
      `compile_file` → `load_file_modules`) runs on — the exact command
      named in the original "bootstrap compile takes many minutes"
      complaint, and item 14's own closing note ("the full-corpus number
      is what matters... not one giant file in isolation") turned out to
      be only half the story: the ONE-file `compile`/`pretty`/`test`
      commands had their own, much larger, independent bug the whole time.
    **Fix**: simplified `load_dependencies_with_info` to a flat fold over
    the already-complete `deps` list — one `load_module_with_info` per
    entry, no re-derivation, no per-node subtree re-walk — mirroring the
    already-correct `load_dependency_scopes` (line 884) shape exactly.
    Kept the existing `list_contains_module_info` dedup guard (line 1965):
    not a leftover, since `load_file_modules` manually prepends
    `[prelude_module_path, init_module_path]` ahead of the already-flattened
    list, which can genuinely duplicate an entry. Pure `.mo`-source change,
    `lang/module.mo` only — no Rust touched. **Also removed, while in the
    area**: 9 dead top-level defs in the same file, each verified (via
    whole-repo grep, `.mo`/`.rs`/`.md`) to have zero references anywhere
    outside their own definition — `init_module_file_path`,
    `std_module_path`, `examples_module_path`, `lang_module_path` (a set
    of directory-path-string builders, superseded by
    `resolve_module_file`'s search-path resolution and never called),
    `parse_all_decls_strict` (superseded by `try_parse_decls_strict`
    calling `decls_parser_strict` directly, never through this wrapper),
    `try_read_module_file_default`, `load_module_with_dependencies_default`,
    `load_module_decls_with_dependencies_default` (three unused `""`-base-dir
    convenience wrappers), and `get_module_info_file_path` (an unused
    `ModuleInfo` accessor — its sibling `get_module_info_decls` IS used and
    was left alone). **Measured** (`git stash` before/after, same session):
    `bootstrap pretty lang/main.mo` (chosen because `pretty` only calls
    `load_file_modules` then prints decls — no type-checking, no codegen —
    so it isolates this fix's effect from everything else) dropped from
    **746.01s to 130.21s wall (-82.5%)**, **647.47s to 127.40s CPU-seconds
    (-80.4%)** — a ~5.7x speedup. Output verified byte-identical before/after
    (the only diffs: a build timestamp and one internal gensym counter,
    `_anon#NNNN`, which naturally shifts since fewer atoms get minted along
    the way — not user-visible). Smoke-tested the real commands:
    `bootstrap compile examples/hello.mo` succeeds end-to-end
    ("Compilation finished"); `bootstrap test examples/structs.mo` correctly
    loads and SKIPs (no codegen needed, so it exercises the fixed loader
    without hitting unrelated bugs). `bootstrap test` on files that DO need
    codegen (`examples/tests.mo`, `pattern_matching.mo`, `iteration.mo`)
    hits pre-existing, unrelated `llc` codegen failures (void-typed
    values in generated LLVM IR) — confirmed via `git stash` that these
    fail identically without this fix, so they're not a regression, just
    a separate, already-broken area this pass didn't touch. `cargo test`
    (627/627) and `check init std lang examples` (2 errors/7 warnings)
    both unchanged, confirming no effect on the unrelated,
    already-correct `check` traversal.
16. **New "unused def" warning — Rust-native checker only, `monad-rs
    check`.** `module_warnings`/`collect_referenced_names`
    (`core/src/term/module.rs`) already existed for unused-*import*
    detection, per-file. Added a sibling, `unused_def_warnings`, but it
    genuinely needs the WHOLE loaded corpus (`LoadedModules`), not one
    file: a def used only by a sibling file would be a false "unused"
    positive checked one file at a time. Wired into `check_files`
    (`core/src/lib.rs`) as a pass run once after the per-file loop
    finishes (once `master_loaded` holds every checked file), matched
    back onto each warning's own originating `FileCheckResult` via a
    `ModulePath -> PathBuf` map built during that same loop (`Diagnostic`/
    `SourceRange` never carry a real file path at parse time in this
    codebase — that's threaded explicitly by callers — so a `ModulePath`,
    via `Module::path`, is the only reliable key to match a warning back
    to its file).
    Deliberately **not** wired into the test runner
    (`run_tests`/`run_tests_for_files`): that path loads each file
    independently, in parallel, from a shared read-only starting
    snapshot (`base_loaded.clone()`, O(1) thanks to item 13's Arc-wrap),
    never merging back into one final whole-corpus `LoadedModules` the
    way `check_files`'s sequential loop does — there is no single
    "everything loaded" structure to run a whole-program pass against
    without a real architectural change, out of scope here.
    Exemptions: `pub` (may be used by another mote, invisible to this
    checker), `#[test]`-attributed (called by the harness, not
    referenced by name), named `main` (the entry point). A third
    exemption was added after direct measurement, not anticipated up
    front: a synthesized typeclass-instance dictionary def
    (`instance-{class}-{args}`, `core/src/term.rs`'s `instance()`
    constructor) is found by the type system's own dictionary-resolution
    machinery (dispatched by TYPE, at typecheck/eval time), never
    through a named `Term::Var` reference — exempted the same way `main`
    is, a root the ordinary reachability model doesn't apply to.
    Matching a def's own name against the whole-corpus reference set
    deliberately does NOT reuse `referenced_contains_name`'s own
    broadest fallback (any referenced path anywhere ending in this
    identifier) — confirmed empirically that doing so suppressed nearly
    every real warning across this project's own ~100-file corpus (that
    fallback is calibrated for one file's small reference set, not
    a multi-hundred-file union). Only the two precise checks survive:
    exact full-path match, and bare-last-segment match (a same-module or
    post-`open` reference resolved to just the local name).
    **Known, accepted precision gap, found by direct testing, not
    theoretical**: a def that shares its bare name with something else
    also in scope (e.g. `lang/module.mo`'s own `file_exists`, which
    wraps an `open`ed `IO.file_exists` of the identical bare name) can
    read as unused even when genuinely called, if the checker's own
    elaboration resolves same-file bare references to a DIFFERENT
    same-named target than the literal local def — narrow (one
    confirmed instance in the real corpus), not chased further this
    pass; flagged here rather than silently shipped.
    **Verified** via a 5-case fixture (`pub` def, def used only by a
    sibling file, genuinely-unused private def, `#[test]` def, `main`) —
    all 5 behaved correctly, both as a manual end-to-end `monad-rs
    check` run (`examples/unused_def_fixture_a.mo`/`_b.mo`, not checked
    in) and as a new permanent unit test
    (`term::module::test::test_unused_def_warnings_five_cases`,
    `core/src/term/module/test.rs`). On the real corpus (`check init std
    lang examples`): 52 warnings, spot-checked several by hand (real
    dead utility functions, unused derive-generated constructors) after
    the instance-dictionary exemption cut an initial ~80 down by ~28
    false positives. `cargo test` 628/628 (627 + the new test); `check
    init std lang examples`'s 2 errors/7 pre-existing import warnings
    unchanged, confirming this is purely additive.
    **Self-hosted checker's own "unused def" warning is a separate,
    larger, not-yet-done piece of this same request** — no warning/
    severity concept exists in the self-hosted pipeline at all today,
    and `check`'s self-hosted command has no whole-corpus flat `Def`
    list the way `compile`/`test` already do via `load_file_modules` —
    see the module-loading investigation (this same session) for the
    concrete design (generalize `lang/codegen/emit.mo`'s existing
    `reachable_defs_from`/`collect_referenced_names` reachability pass,
    already rooted at `main`, to also root at every `pub`/`#[test]` def;
    "unused" is the complement of the final `visited` set).
17. **`Value::Con`/`Value::PartialNtv` args Arc-wrap — closes the last big
    deep-clone gap item 13 flagged but ruled out for the wrong benchmark.**
    Full writeup: `plans/implementations/value-con-arc-wrap-optimization.md`.
    Item 13's callgrind profile found `Value::clone()` on `Con`/
    `PartialNtv` "real but negligible" — but that was measured against
    `test_typecheck_lang_main`, dominated by the (then-unfixed)
    `LoadedModules` clone cost, not a workload that exercises list/ADT
    churn. A parallel session's own callgrind profile on a genuinely
    List/`Con`-heavy workload (`count_eq`/`build_list`, the self-hosted
    checker's own `Map`/`Scope`/`Option`/`List` shape) found the opposite:
    ~90% of eval cost (`Value::to_vec` clone ~32%, drop_glue ~16.5%,
    allocator churn ~42%) was exactly this. Root cause: `Value::Con { tag,
    args: Vec<Value> }` derived `Clone` structurally, so cloning one
    deep-copied its entire nested-`Con` structure (a list's `cons head
    tail`, `tail` itself a `Con`) — every ordinary variable read
    (`Env::get(...).cloned()`, `GlobalCache::get`'s `v.clone()`, both
    `core_eval.rs`) paid a full O(current-size) clone, reproducing
    `SharedStr`'s (item 12) exact O(N²) shape for arbitrary structured
    values, never just strings. **Fix**: `args: Vec<Value> ->
    Arc<Vec<Value>>` on both variants (not the whole `Value` enum, so
    every existing match arm stays unchanged) — same idiom as `SharedStr`/
    `Module`'s Arc-wrap. Mutating sites (`core_eval.rs`'s incremental
    application and `Match`-arm field-binding; `eval/meta_reflect.rs`'s
    macro-reflection reify helpers) use `Arc::make_mut` (copy-on-write).
    `eval/meta_reflect.rs`'s ~19 candidate sites collapsed to ~6 real
    edits in practice — nearly all of them already funneled through one
    shared `pop_front` helper, so changing its signature
    (`&mut Vec<Value> -> &mut Arc<Vec<Value>>`) fixed every call site with
    zero call-site changes. Added
    `test_partial_con_application_from_shared_value_does_not_leak_across_branches`
    (`core_eval.rs`) for the COW correctness hazard (two aliases of one
    memoized constructor global, via `GlobalCache`, each applying a
    different extra argument — neither may leak into the other or into
    the cache's own stored copy). **Measured** (same `count_eq`/
    `build_list` shape as `core_eval_bench.rs`'s `class_dispatch`, `git
    stash` before/after): n=500/2000/8000 went from 16ms/246ms/4076ms
    (quadratic — 4x n gives ~16x time) to 0ms/2ms/8ms (linear — 4x n gives
    ~4x time) — a 123x-509x speedup that GROWS with N, the actual
    signature of an algorithmic fix, not a constant-factor one. Added a
    permanent `class_dispatch_large` criterion benchmark
    (`core/benches/core_eval_bench.rs`, 5x `CLASS_DISPATCH`'s size) as
    standing infrastructure. Verified: `cargo test`/`cargo test --release`
    all green (676+ core tests + 6 integration suites); `cargo clippy --`
    exits 0, no new warnings; `cargo run --release -- test init std lang
    examples` 1287/1287 unchanged; `cargo run --release -- check init std
    lang examples` byte-identical (101 files, 2 errors, 62 warnings,
    confirmed via direct `git stash` comparison); `cargo run --release --
    test slow_tests` — same 29 pre-existing `test_typecheck_*` failures
    (a known, unrelated self-hosted-checker gap — see this file's
    Troubleshooting section on `Map`/`BOrd` dispatch inside
    `load_module_with_dependencies`), not a new regression. **Not yet
    re-measured**: the `check_deps=true` 28GB-RSS repro from
    `check-deps-memory-blowup.md` — not reachable from this branch (that
    flag lives on `checker/fix-coverage`, not merged here). This fix
    targets that investigation's leading hypothesis #1 directly; re-run
    that repro once `check_deps` is available here to confirm how much of
    it this closes.

## Committing Changes

### Commit Message Format

Do not include a `Claude-Session:` trailer (or link) in commit messages
for this repo.

### Pre-commit Hooks

Always commit with pre-commit hooks enabled. **Never** use `git commit --no-verify` — the pre-commit hooks ensure clippy, rustfmt, `cargo test`, and `cargo run --release -- test init std lang examples` all pass before each commit. If a hook fails:
1. Read the error message to identify the issue
2. Fix the underlying problem (code warnings, test failures, formatting)
3. Stage the fix and retry the commit

**IMPORTANT**: When `rustfmt` hook fails, the commit DID NOT succeed (the files
were modified by the hook but NOT committed). Always run `cargo fmt` manually
BEFORE committing. If the hook modifies files, the commit was rejected — run
`cargo fmt && git add <modified files> && git commit ...` to retry.

**DO NOT** assume the commit succeeded when you see "files were modified by
this hook" — that means the hook rejected the commit. Always check
`git log -1` after committing to verify.

### Pre-commit Checklist

Before committing, ensure:
```bash
cargo fmt
cargo build --package monad-core 2>&1 | grep -E "warning:|error"
cargo test
cargo run -- test init/
cargo run -- test std/
cargo run -- test lang/
```

## Coding Agent Guide

### Agent Skills

Look in `plans/.opencode/skills/` for skill documents. Read the relevant
skill before starting any task — they contain checklists, command templates,
and anti-patterns that prevent common errors. List available skills with:

```bash
ls plans/.opencode/skills/
```

### Problem-Solving Workflow

1. **Reproduce first** — Before any change, confirm you can reproduce the bug or observe the missing behavior. Run the exact command the user provides.

2. **Search evidence, not guesses** — When investigating a bug, anchor every hypothesis in code. Search for the error message string in the source. Search for the function name mentioned in stack traces. Never assume — verify.

3. **Isolate the failure** — Minimize the failing case. Reduce a complex Monad program to the smallest example that still fails. This tells you which language feature is involved and narrows which compiler pass to modify.

4. **Trace the pipeline** — A Monad program goes through: parsing → elaboration → type checking → evaluation. Identify which stage fails:
   - **Parser errors** mention `parse` or show unexpected tokens
   - **Elaboration errors** mention free variables or implicit binding
   - **Type errors** mention `TypeError` and expected/found types
   - **Eval errors** mention `CoreEvalError`, stack overflow, or missing native
   - **Panics** mean an `unreachable!()` was hit — often a missing case in a match

### Fast Iteration

```bash
# Fastest: build just the core crate (avoids CLI/WASM/LLVM)
cargo build -p monad-core 2>&1 | head -20

# Run a single test by name
cargo test core_check_module::some_test_name

# Run all parser tests
cargo test parser

# Run Monad stdlib tests (fast feedback on language semantics)
cargo run -- test init/tests.mo

# Run a specific example
cargo run -- run examples/specific.mo
```

Prefer `cargo test parser::test_do_parser` over `cargo test` when working
on the parser — it saves minutes per iteration.

### Finding the Right Code

| Symptom | Look In |
|---|---|
| Parse error / wrong syntax accepted | `core/src/parser.rs` — search for the relevant parse function |
| Wrong type inferred / type error missing | `core/src/eval/type.rs` — search for the type form |
| Wrong evaluation result / runtime error | `core/src/eval.rs` — search for the term variant |
| Native function wrong / missing | `core/src/eval/native.rs` — search for the function name |
| Term representation / new AST node | `core/src/term.rs` — add new `Term` variants here |
| Constraint solving / instance resolution | `core/src/eval/constraint.rs` |
| Module loading / use/open | `core/src/term/module.rs` |
| CLI flags / command handling | `cli/src/main.rs` |

Use `rg` (ripgrep) to search — it respects `.gitignore` and is fast:

```bash
# Find where an error message is emitted
rg "expected function"

# Find all references to a function
rg "fn type_check_free_var"

# Find Monad code using a feature
rg "linear\|affine" init/ --include "*.mo"
```

### Common Bug Patterns in Compiler Development

**1. Missing match arm on a new Term variant.**

When you add a `Term::Foo` variant, every `match` on `Term` in the codebase
needs handling. The Rust compiler catches this — follow the compilation
errors. The most common locations: `eval.rs` (evaluation), `type.rs` (type
checking), `module.rs` (scope building), `term.rs` (Display, substitution).

**2. Forgetting to add a new Term variant to `substitute()` or
`free_vars()`.**

These are in `eval.rs` / `term.rs`. If substitution doesn't handle the new
variant, variables won't be replaced and evaluation will use stale bindings.
**Check these even if the Rust compiler doesn't force you to** (some
`substitute` impls have a catch-all `_ => term`).

**3. Adding a parser test but not testing the desugared AST.**

Parser tests compare against expected ASTs. If a test passes but produces
wrong output, check that the expected AST in the test matches what the
evaluator expects. The desugaring is often in a separate function from the
parser.

**4. Instance resolution loops.**

Recursive instances (`instance [Show A] Show (List A)`) can cause infinite
resolution. The constraint solver at `constraint.rs` has a visiting set.
If it doesn't, or the visiting set misses a path, the compiler hangs.
Always check the visiting set when modifying instance resolution.

**5. The evaluator and type checker use different `Scope` types.**

`eval.rs` uses `scope.resolve_name()` which goes through `GlobalScope`.
`type.rs` uses `find_var_ref_of` which walks the linked-list `Scope`.
A def that's visible to one may not be visible to the other. When a name
resolves in the type checker but not the evaluator (or vice versa), the
scope builder (`module.rs`) is usually the culprit.

### Writing Tests for Bug Fixes

1. **Add a parser test** (`core/src/parser/test/`) if the bug involves syntax
2. **Add an eval test** (`core/src/eval/test.rs`) if the bug involves evaluation
3. **Add a Monad test** — use `#[test]` in:
   - `init/tests.mo` for bugs involving core language semantics (prelude types, operators, etc.)
   - `std/<module>_test.mo` for bugs in `std/` modules (concurrency, collections, etc.)
   - Never add `std/`-dependent tests to `init/tests.mo` — `init/` must not depend on `std/`
4. **Test the failing case first** — confirm it fails before your fix, then
   confirm it passes after

Follow the existing test patterns exactly. Parser tests use the `similar!`
macro with `do_parser()`/`def_parser()`. Eval tests use `run_test()`/`run_test_err()`.

### Incremental Changes

Always take the smallest possible step:

1. One failing test → one fix → one commit
2. Don't refactor unrelated code while fixing a bug
3. Don't add new features while fixing a bug
4. If you need to refactor to fix, do it in a separate commit

When a change touches multiple files, commit after each file if the
intermediate state compiles and passes tests. This makes `git bisect`
precise.

### Debugging the Evaluator

When a Monad program produces the wrong result:

1. Add `--debug` to see evaluation steps: `cargo run -- run file.mo -- --debug`
2. Or insert `println` in the Rust evaluator at `eval.rs` around the
   relevant term case
3. Check that native functions match their declarations — the Monad type
   signature and the Rust handler must agree on argument count and types
4. Verify that substitution produces the expected term — many eval bugs
   are actually substitution bugs

### Rebase Resolution Workflow

When rebasing a feature branch onto upstream changes that touch the same
Monad source files, the safest resolution strategy is:

1. **Accept the upstream file as-is**: `git checkout --theirs <file>` to
   start from a clean upstream state. This avoids tedious per-hunk conflict
   resolution when large AST renames (e.g., `Term` → `TermV0`) sweep
   through the file.
2. **Reapply your edits on top**: Port each logical change set (function
   compactions, table conversions, etc.) onto the fresh upstream base.
3. **Audit for leftover artifacts**: Check for:
   - Double `#[partial]` annotations (both upstream and your stashed code
     may have had one → both land after checkout/reapply)
   - `#[partial]` on pure (non-parsing) helper functions (not needed)
   - Old helper functions that upstream renamed parameters on but you
     removed entirely (check with `rg -n 'helper_name' <file>`)
4. **Verify**: Run `cargo run -- test <file>` and verify all tests pass.
   If the number of tests changes, confirm the delta is expected (e.g.,
   upstream added tests to match new AST variants).
5. **Verify no unmerged files remain**: `git diff --name-only --diff-filter=U`

**Common artifacts after checkout/reapply**:
- Double `#[partial]`: the upstream `#[partial]` + your stashed `#[partial]`
  both survive. Remove duplicates.
- `#[partial]` on pure helpers: `num_to_term`, `op_check` don't need it.
- Old helper definitions that were supposed to be deleted but survived
  because upstream changed their parameter names (making the conflict
  resolution merge them back as "separate" definitions).

**`fn` lambda parameter syntax**: When reapplying compactions that use
`bind_parse`/`map_parse`, inline `fn` lambda arguments work fine
(including generic combinators) as long as annotated parameters are
parenthesized — `fn (s : String) => ...`, not `fn s : String => ...` (see
Known Issues above).
