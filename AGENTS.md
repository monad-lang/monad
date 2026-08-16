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

### Pre-commit

The pre-commit config (`.pre-commit-config.yaml`) is managed by Nix via `git-hooks.nix`. Do NOT edit it directly. Instead, modify the Nix configuration that generates it. The `monad-tests` hook currently runs `cargo run -- test init/tests.mo`. If this hook fails, run `cargo run -- test init/` to see all test failures.

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

### Struct Field Access via Dot Syntax Is Not Valid Monad

**Problem**: Writing `loc.offset` or `span.fragment` to access struct fields appears natural but does NOT work. Dot syntax in Monad is method-call syntax (`x.fun` desugars to `Type.fun x`), NOT field access. Using dot syntax on a struct produces "unexpected token" or "not a function" errors.

**Root cause**: Monad has no dedicated field access syntax for structs. Dot syntax is exclusively for method calls and module paths.

**Correct pattern**: Access struct fields via pattern matching on the `mk` constructor:
```monad
// Struct definition:
struct Location { offset : I64, line : I64, column : I64 }

// BROKEN — dot syntax:
let off : I64 := loc.offset in   // interpreted as method call!

// CORRECT — pattern matching:
match loc {
    mk off line col => ...
}
```

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
   `lang/tests/typecheck_lang_tests.mo`'s `test_typecheck_lang_main`, the
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
   `time cargo run -- test lang/tests/typecheck_lang_tests.mo`) — Big-O
   analysis alone is not a reliable guide to real performance here.

## Committing Changes

### Commit Message Format

Do not include a `Claude-Session:` trailer (or link) in commit messages
for this repo.

### Pre-commit Hooks

Always commit with pre-commit hooks enabled. **Never** use `git commit --no-verify` — the pre-commit hooks ensure clippy, rustfmt, `cargo test`, and `cargo run -- test init/tests.mo` all pass before each commit. If a hook fails:
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
