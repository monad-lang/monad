# Reference

This chapter provides a quick reference for Monad syntax and built-in features.

## Keywords

```
def, let, in, use, open, class, struct, instance, type, fn, ꟛ, match,
if, then, else, infix, return, for, do
```

Reserved names: `Type`, `Pred`

## Comments

```monad
// Single line comment

/* Multi-line
   comment */
```

## Docstrings

```monad
/// Documentation for the following declaration
def greet (name : String) : IO Unit := println name

/// Module-level documentation (at top of file)
```

Docstrings are parsed and stored on declarations, retained through module loading for tooling and inspection.

## Lambda Expressions

Three equivalent syntaxes:

```monad
fn x => x + 1
\ x => x + 1
ꟛ x => x + 1
```

## Backtick Operators

```monad
x `f` y   // Equivalent to f x y
```

Identifiers in backticks are treated as infix operators (like Haskell).

## Let Expressions

```monad
// Inline style
let x := 10 in x + 1

// Semicolon style
let x := 10;
let y := 20;
in x + y

// With type annotation
let x : I64 := 10 in x + 1
```

## Numeric Literals

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

## Type Annotations

```monad
(expr : Type)
```

Any term can be annotated with its type using `(term : Type)` syntax.

## Method Call Syntax

```monad
x.fun        // Desugared to A.fun x (where A is the type of x)
x.fun args   // Desugared to A.fun args x
```

Method calls are desugared in the type checker. The receiver type is extracted and prepended to the method name.

## Match Expressions

```monad
match value {
    constructor args => body,
    constructor => body
}
```

## If Expressions

```monad
if condition then thenBranch else elseBranch
```

## Do Notation

Two equivalent syntaxes are available:

```monad
// Standard syntax
def example : IO Unit := do {
    let name <- action;
    let x := value;
    return value
}

// Inline do block (equivalent)
def example : IO Unit {
    let name <- action;
    let x := value;
    return value
}
```

### Statement Types

| Statement | Syntax | Desugars To |
|-----------|--------|-------------|
| Bind | `let x <- action` | `Monad.bind action (fn x => ...)` |
| Let | `let x := value` | `let x := value in ...` |
| Return | `return value` | `Monad.pure value` |
| Expression | `expr` | `Monad.bind expr (fn _ => ...)` |

Multiple statements are separated by semicolons.

## Struct Values

```monad
struct Point {
    x : I64,
    y : I64
}

def p := { x := 3, y := 4 }
```

## Attributes

Declarations can be annotated with `@[...]` attributes:

```monad
@[native "function_name"]   // Declare a Rust-native function
@[test]                     // Mark as a test (run via `cargo run -- test <file>`)
```

## Native Functions

Mark functions as implemented in Rust:

```monad
@[native nativeName]
def functionName (params) : ReturnType
```

Example from the standard library:

```monad
@[native println]
def IO.println (s : String) : IO Unit

@[native num_add]
def I64.add (a b : I64) : I64
```

## Infix Operators

```monad
infix (operator) := functionName
```

### Built-in Operators

| Operator | Precedence | Associativity | Function |
|----------|------------|---------------|----------|
| `\|>` | 5 | Left | `apply_fun` |
| `<\|` | 5 | Right | `fun_apply` |
| `>>=` | 10 | Right | `Monad.bind` |
| `.` | 12 | Right | Dot macro (path) |
| `<*>` | 15 | Left | `Applicative.apply` |
| `<\|>` | 20 | Left | - |
| `\|\|` | 25 | Right | `Bool.or` |
| `&&` | 30 | Right | `Bool.and` |
| `==`, `!=` | 40 | Left | - |
| `++` | 50 | Right | `List.append` |
| `>>`, `<<` | 60 | Left | - |
| `+`, `-` | 65 | Left | `I64.add` |
| `*`, `/` | 70 | Left | `HMul.mul` |

## Type Definitions

```monad
// Simple type
type Bool {
    true,
    false
}

// Type with parameters
type Result E A {
    ok (a : A),
    err (e : E)
}

// Type with constructors carrying data
type Option A {
    some (a : A),
    none
}

// Empty type
type Void {}
```

## Struct Definitions

```monad
struct Point {
    x : I64,
    y : I64,
    z : I64 := 0,   // default value
    !name : String  // linear field (!) or affine (?)
}
```

## Class Definitions

```monad
// Simple class
class Functor (F : Type -> Type) {
    def map (f : A -> B) : (F A) -> F B
}

// Class with constraints
class [Functor F] Applicative (F : Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}
```

## Instance Definitions

```monad
// Simple instance
instance FromListLiteral List {
    def cons (a : A) (l : List A) : List A := List.cons a l
    def empty : List A := List.empty
}

// Instance with constraints
instance [Add A] Add (List A) {
    def add (a b : List A) : List A := List.append a b
}
```

## Function Definitions

```monad
// Basic function
def add (a : I64) (b : I64) : I64 := a + b

// With implicit parameters
def identity {A : Type} (x : A) : A := x

// With constraints
def double [Add A] (x : A) : A := HAdd.add x x

// Do block syntax (alternative to :=)
def greet (name : String) : IO Unit {
    println name
}

// Do block with multiple statements
def multiStep : IO Unit {
    println "Step 1";
    println "Step 2"
}

// Native function
@[native println]
def IO.println (s : String) : IO Unit
```

## Modules

```monad
// Import module
use io

// Open module (no prefix needed)
open IO

// Access by path
IO.println "hello"
```

## Dot Macro

The `.` operator (`x.y.z`) is treated as a compile-time macro that concatenates module paths into a single variable reference. This is how module paths like `List.append` work.

## Constraint Solver

Recursive instance constraints (e.g., `instance [Show A] Show (List A) { ... }`) are handled by the constraint solver. It uses a visiting set to detect and resolve cyclic constraint dependencies during instance resolution.

## Standard Library Types

| Type | Constructors | Description |
|------|-------------|-------------|
| `Unit` | `unit` | Single value |
| `Bool` | `true`, `false` | Boolean |
| `I64` | (primitive) | 64-bit signed int |
| `I32` | (primitive) | 32-bit signed int |
| `U64` | (primitive) | 64-bit unsigned int |
| `U32` | (primitive) | 32-bit unsigned int |
| `U16` | (primitive) | 16-bit unsigned int |
| `U8` | (primitive) | 8-bit unsigned int |
| `String` | `of_bytes` | UTF-8 string |
| `Nat` | `zero`, `succ` | Natural numbers |
| `List A` | `empty`, `cons` | Linked list |
| `Option A` | `some`, `none` | Optional value |
| `Result E A` | `ok`, `err` | Success or error |
| `Void` | (none) | Empty type |
| `Any` | `any` | Existential type |
| `IO A` | `io` | IO monad |

## Standard Library Classes

| Class | Parameters | Description |
|-------|-----------|-------------|
| `Functor` | `F : Type -> Type` | Mapping over containers |
| `Applicative` | `F : Type -> Type` | Applicative functors |
| `Monad` | `M : Type -> Type` | Monadic binding |
| `FromListLiteral` | `L : Type -> Type` | List literal desugaring |
| `HAdd` | `A, B, C` | Heterogeneous addition |
| `Add` | `A` | Homogeneous addition |
| `Sub` | `A` | Subtraction |
| `Mul` | `A` | Homogeneous multiplication |
| `Div` | `A` | Division |
| `HMul` | `A, B, C` | Heterogeneous multiplication |
| `BEq` | `A` | Boolean equality |
| `BOrd` | `A` | Ordering |
| `Show` | `A` | String conversion |
| `Append` | `A` | Append/concatenation |
| `From` | `T, A` | Type conversion |
| `DefaultValue` | `A` | Default/empty value |

## Standard Library Functions

### Bool

- `Bool.not (b : Bool) : Bool`
- `Bool.and (a b : Bool) : Bool`
- `Bool.or (a b : Bool) : Bool`

### Option

- `Option.get_or_default (default : A) (self : Option A) : A`

### List

- `List.is_empty (self : List A) : Bool`
- `List.append (a b : List A) : List A`
- `List.first (self : List A) : Option A`
- `List.last (self : List A) : Option A`
- `List.flatten (self : List (List A)) : List A`
- `List.tail (l : List A) : List A`

### IO

- `IO.println (s : String) : IO Unit`

### I64

- `I64.add (a b : I64) : I64`

### Pipeline

- `fun_apply (f : A -> B) (a : A) : B` — `f <| a`
- `apply_fun (a : A) (f : A -> B) : B` — `a |> f`

## CLI Usage

```bash
# Build the compiler
cargo build --package monad-core

# Run a Monad file
cargo run -- run file.mo

# Run with debug output
cargo run -- run file.mo -- --debug

# Run @[test] annotated definitions
cargo run -- test file.mo

# Compile to native binary (requires llvm feature)
cargo run -- compile file.mo

# Start the REPL (requires repl feature)
cargo run -- repl
```
