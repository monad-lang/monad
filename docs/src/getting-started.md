# Getting Started

Welcome to the Monad language! This tutorial walks through the fundamentals of
programming in Monad, a dependently typed language.

## Prerequisites

Before getting started, ensure you have:
- A `monad` binary. The compiler is written in Monad, so the first one is either
  built by the bootstrap host or installed as a nightly with `monadup` — see
  [Compiling and Running](./compiling.md#getting-a-compiler). (Nightlies are
  Linux x86_64 and currently need Nix; building from source is the portable
  route.)
- `llc`, `clang`, and the Boehm GC development files, which the compiler links
  against. `devenv shell` provides all three.
- A text editor. There is no syntax-highlighting plugin yet; the bootstrap host
  ships an [LSP server](./bootstrap-host.md#editor-and-agent-tooling) for
  diagnostics.

## Your First Program

Let's start with the classic "Hello, World!" program:

```monad
use io {IO}
open IO {println}

def main (args : List String) : IO Unit := println "Hello, World!"
```

Save this as `hello.mo`, then run it:

```bash
monad run hello.mo
```

You should see:
```
Hello, World!
```

`run` compiles the program and executes the result — a Monad program is always a
native binary. To keep the binary, use `compile` and give it an **absolute**
output path, since a relative one lands in the compiler's scratch directory:

```bash
monad compile hello.mo -o "$PWD/hello"
./hello
```

## Understanding the Structure

Every Monad program follows this basic structure:

1. **Imports** (`use`): bring modules into scope
2. **Open declarations** (`open`): make definitions available without prefixes
3. **Definitions** (`def`): declare functions and values
4. **Type signatures**: annotate the types of definitions

Point 4 is not optional. **Every `def` must carry a type annotation** — there is
no top-level type inference. `def x := 42` is a parse error; write
`def x : I64 := 42`.

## Variables and Basic Types

```monad
def x : I64 := 42            // 64-bit signed integer
def name : String := "Monad" // String
def flag : Bool := true      // Boolean
def nothing : Unit := unit   // Unit type (single value)
def ratio : F64 := 3.14      // 64-bit float
```

The other fixed-width numeric types are `I32`, `I16`, `I8`, `U64`, `U32`, `U16`,
`U8`, and `F32`. Integer literals default to `I64` and float literals to `F64`;
a suffix picks another width (`42u8`, `3.14f32`).

Character literals are written with single quotes, and take the same escapes as
strings:

```monad
def letter : Char := 'M'
def newline : Char := '\n'
def lambda : Char := 'λ'
```

A literal holds one Unicode codepoint. There is no `\u{...}` escape — write the
character itself. Be aware that **`Char` is a stub type**: it has no operations
at all, no equality and no `ToString`, so you can hold and pass a `Char` but not
yet inspect one. For text you work with, use `String`.

## Functions

Functions are defined using `def` with curried parameters:

```monad
// Simple function
def double (n : I64) : I64 := n + n

// Multi-parameter function (curried)
def add (a : I64) (b : I64) : I64 := a + b

// Two parameters of the same type share one annotation
def mul (a b : I64) : I64 := a * b

// A plain value
def greeting : String := "Hello"
```

### Function Application

Function application is written with spaces:

```monad
def double (n : I64) : I64 := n + n
def add (a : I64) (b : I64) : I64 := a + b

def result : I64 := double (add 3 4)  // 14
```

### Anonymous Functions (Lambdas)

Lambda expressions use `fn`, `\`, or `ꟛ` — the three spellings are identical:

```monad
def square : I64 -> I64 := fn n => n * n
def add_one : I64 -> I64 := \ x => x + 1
def identity {A : Type} : A -> A := ꟛ x => x
```

The annotation on the `def` is what gives the lambda's parameter its type, so a
lambda-bodied definition always needs a function type in its signature.

## Pattern Matching

Match on values to deconstruct them:

```monad
def is_zero (n : Nat) : Bool :=
  match n {
    zero => true,
    succ _ => false
  }

// Pattern matching on booleans
def negate (b : Bool) : Bool :=
  match b {
    true => false,
    false => true
  }
```

Patterns are one level deep: each constructor argument is a fresh name or `_`.
Nested patterns, literal patterns, and guards are not supported, and match
expressions are not checked for exhaustiveness — see the
[Maturity Matrix](./maturity.md).

## Let Bindings

A `let` binds one name, and `in` gives the body:

```monad
def compute : I64 :=
  let x := 10 in
  let y := x * 2 in
  x + y
```

Chain them for several bindings, as above. Unlike a top-level `def`, a `let`
binding infers its type; you can still annotate one explicitly:

```monad
def hypotenuse_squared (a : I64) (b : I64) : I64 :=
  let a2 : I64 := a * a in
  let b2 : I64 := b * b in
  a2 + b2
```

Several bindings can also share one `let`, separated by `;`:

```monad
def multi : I64 := let x := 10; y := 20 in x + y
```

Each binding sees the ones before it, and each may carry its own annotation. The
`;` is required — the [bootstrap host](./bootstrap-host.md) lets you leave it
out, the self-hosted compiler does not. Nested `let … in` works everywhere and is
the form used through most of this book.

## Docstrings

Document your declarations with `///` docstrings. They are retained through
module loading, so the [bootstrap host](./bootstrap-host.md)'s LSP server can
show them:

```monad
/// Greet a user by name.
def greet (name : String) : String := "Hello, " ++ name
```

## Comments

```monad
// Single line comment

/* Multi-line
   comment */

def answer : I64 := 42
```

## Operators

Monad supports infix operators with defined precedence:

```monad
def result : I64 := 3 + 4 * 2  // 11 (multiplication binds tighter)
```

Most operators are bound to a type-class method in the prelude, so they work for
any type with the right instance:

| Operator | Bound to | Description |
|----------|----------|-------------|
| `+`, `-` | `HAdd.add`, `Sub.sub` | Add / subtract |
| `*`, `/` | `HMul.mul`, `Div.div` | Multiply / divide |
| `++` | `Append.append` | Append (strings, lists, …) |
| `&&`, `\|\|` | `Bool.and`, `Bool.or` | Boolean and / or |
| `==` | `BEq.beq` | Equality |
| `<`, `>` | `BOrd.lt`, `BOrd.gt` | Ordering |
| `>>=` | `Monad.bind` | Monadic bind |
| `\|>` | `apply_fun` | Forward pipe (`x \|> f`) |
| `<\|` | `fun_apply` | Backward pipe (`f <\| x`) |

A handful of operator *tokens* have a precedence but no binding in the prelude
yet, so using them is an error: `!=`, `<=`, `>=`, `<*>`, `<\|>`, `>>`, `<<`, and
`@`. The [Reference](./reference.md#built-in-operators) has the full precedence
table, and you can bind any of them yourself with `infix (op) := someFunction`.

## Summary

In this chapter, you learned:
- How to write a basic Monad program
- That every `def` needs a type annotation
- Function definitions and lambdas
- Pattern matching with `match`
- Local bindings with `let … in`, chained or separated by `;`
- Comments, docstrings, and operators

Next, we'll explore **types**, the foundation of data structures in Monad.
