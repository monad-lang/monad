# Getting Started

Welcome to the Monad language! This tutorial will guide you through the fundamentals of programming in Monad, a dependently typed language.

## Prerequisites

Before getting started, ensure you have:
- A text editor with Monad syntax support (or basic text editing)
- The Monad compiler built (see README for instructions)

## Your First Program

Let's start with the classic "Hello, World!" program:

```monad
use io
open IO

def main (args : List String) : IO Unit := println "Hello, World!"
```

Save this as `hello.mo` and run it with:

```bash
cargo run -- run hello.mo
```

You should see:
```
Hello, World!
```

## Understanding the Structure

Every Monad program follows this basic structure:

1. **Imports** (`use`): Bring modules into scope
2. **Open declarations** (`open`): Make definitions available without prefixes
3. **Definitions** (`def`): Declare functions and values
4. **Type signatures**: Annotate the types of definitions

## Variables and Basic Types

Monad supports explicit type annotations. The basic types include:

```monad
def x : I64 := 42            -- 64-bit integer
def name : String := "Monad" -- String
def flag : Bool := true      -- Boolean
def nothing : Unit := unit   -- Unit type (single value)
```

You can also use other integer types: `I32`, `U64`, `U32`, `U16`, `U8`.

## Functions

Functions are defined using `def` with curried parameters:

```monad
-- Simple function
def double (n : I64) : I64 := n + n

-- Multi-parameter function (curried)
def add (a : I64) (b : I64) : I64 := a + b

-- With type annotation on the result
def greeting : String := "Hello"
```

### Function Application

Function application is written with spaces:

```monad
def result := double (add 3 4)  -- result = 14
```

### Anonymous Functions (Lambdas)

Lambda expressions use `fn`, `\`, or `ꟛ`:

```monad
def square := fn n => n * n
def add_one := \ x => x + 1
def identity := ꟛ x => x
```

## Pattern Matching

Match on values to deconstruct them:

```monad
def isZero (n : Nat) : Bool :=
  match n {
    zero => true,
    succ _ => false
  }

-- Pattern matching on booleans
def not (b : Bool) : Bool :=
  match b {
    true => false,
    false => true
  }
```

## Let Bindings

Local bindings with `let`:

```monad
def compute : I64 :=
  let x := 10
  let y := x * 2
  in x + y
```

You can also use semicolon-style let bindings:

```monad
def hypotenuse (a : I64) (b : I64) : I64 :=
  let a2 := a * a;
  let b2 := b * b;
  in a2 + b2
```

## Comments

```monad
// Single line comment

/* Multi-line
   comment */
```

## Operators

Monad supports infix operators with defined precedence:

```monad
use init
use math

def result : I64 := 3 + 4 * 2  -- 11 (multiplication binds tighter)
```

Built-in operators include:
- `(+)` -- Addition (via `I64.add`)
- `(*)` -- Multiplication (via `HMul.mul`)
- `(++)` -- List append
- `(&&)` -- Boolean and
- `(||)` -- Boolean or
- `(>>=)` -- Monad bind
- `(<|)` -- Function application (reverse)
- `(|>)` -- Pipeline (forward application)

## Summary

In this chapter, you learned:
- How to write a basic Monad program
- Variable declarations and basic types
- Function definitions and lambdas
- Pattern matching with `match`
- Local bindings with `let`
- Comments and operators

Next, we'll explore **types**, the foundation of data structures in Monad.
