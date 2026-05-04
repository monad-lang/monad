# Monad Language Developer Guide

This document explains how to modify the Monad language codebase and write correct Monad code.

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
├── llvm-codegen/     # LLVM native compilation backend
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
└── examples/         # Example programs
```

## Building and Running

```bash
# Build the compiler
cargo build --package monad-core

# Run a Monad file
cargo run -- run examples/hello.mo

# Run with debug output
cargo run -- run examples/hello.mo -- --debug

# Run @[test] annotated definitions
cargo run -- test init/tests.mo

# Compile to native binary (requires llvm feature)
cargo run -- compile examples/hello.mo

# Use the REPL (interactive, requires repl feature)
cargo run -- repl
```

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
    let value := 42
    println "Done"
}
```

### Do Notation

Do notation provides syntactic sugar for monadic operations. It can be used with the `do { ... }` syntax or directly in function definitions using `{ ... }`.

```monad
// Standard do notation
def example : IO Unit := do {
    let x <- get_value
    let y := x + 1
    return y
}

// Do block in function definition (equivalent)
def example : IO Unit {
    let x <- get_value
    let y := x + 1
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

```monad
let x := 10 in
let x + y := 10 in
x + y

// With type annotation
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
// Load a module
use prelude
use io

// Open namespace. Make defs available without given prefix.
open IO
```

### Native Functions

Call Rust functions from Monad using the `@[native "..."]` attribute:

```monad
@[native "add"]
def add (a: I64) (b: I64) : I64
```

## Attributes

Declarations can be annotated with `@[...]` attributes:

```monad
@[native "function_name"]   // Declare a Rust-native function
@[test]                     // Mark as a test (run via `cargo run -- test <file>`)
```

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

### Evaluator (`core/src/eval.rs`)
- Beta reduction happens in the `eval` function
- Native functions are executed in `native_execute`

### Type Checker (`core/src/eval/type.rs`)
- Type checking and constraint resolution

## Testing

```bash
# Run Rust tests
cargo test

# Run a specific test
cargo test eval::test
```

### Running Monad Tests

```bash
cargo run -- test init/tests.mo
```

This runs all definitions annotated with `@[test]` in the given file, evaluating them and reporting pass/fail.

## Development Workflow

Always use Test-Driven Development (TDD):
1. Write a **failing test** first
2. Implement the fix/feature
3. Run tests to confirm pass
4. Run `cargo fmt && cargo test` to ensure formatting and all tests pass
5. Make a **small, focused commit** with a descriptive message

Always make small, incremental changes. Each commit should be a single logical change.
After each commit, confirm the test suite still passes.

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
@[native "function_name"]
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

## Formatting

Always format Rust code according to `rustfmt.toml` before committing:

```bash
cargo fmt
```
