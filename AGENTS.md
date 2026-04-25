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
│   │   └── main.rs     # CLI entry point
│   └── Cargo.toml
├── wasm/             # WebAssembly bindings
├── init/             # Standard library
│   ├── prelude.mo     # Basic types (Bool, List, Option, etc.)
│   ├── io.mo         # IO operations
│   ├── term.mo        # Term manipulation
│   └── parser.mo      # Parser combinators
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

# Use the REPL (interactive)
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

// Struct-like type
struct Point {
    x : I64,
    y : I64
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
```

### Lambda Expressions

```monad
fn x => x + 1
\ x => x + 1
ꟛ x => x + 1
```

### Let Expressions

```monad
let x := 10 in
let y := x * 2 in
x + y
```

### Match Expressions

```monad
match value {
    some a => a,
    none => default
}
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

## Key Language Features

1. **Dependent Types**: Types can depend on values (using `{x : Type}` forall syntax)

2. **Type Classes**: Like Haskell, with automatic instance resolution

3. **Linear Types**: Currently managed via the `!` convention (not fully implemented)

4. **Native Functions**: Call Rust functions from Monad

```monad
@[native "add"]
def add (a: I64) (b: I64) : I64
```

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

## Style Conventions

- Use 2 spaces for indentation
- Lowercase identifiers for functions/variables
- Uppercase for types/type classes
- Prefer descriptive names
- Comment with `//`
