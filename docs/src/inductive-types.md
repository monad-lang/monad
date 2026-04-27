# Types

Types are the foundation of data structures in Monad. This chapter covers inductive types, the primary way to define new types.

## Basic Syntax

Types are declared with the `type` keyword:

```monad
type Bool {
    true,
    false
}
```

This defines a type `Bool` with two constructors: `true` and `false`.

## Constructors with Fields

Constructors can carry data:

```monad
type Option A {
    some (a : A),
    none
}
```

## Natural Numbers

The canonical example of inductive types is natural numbers:

```monad
type Nat {
    zero,
    succ (n : Nat)
}
```

This defines:
- `zero`: The natural number 0
- `succ n`: The successor of `n` (i.e., `n + 1`)

So `3` is represented as `succ (succ (succ zero))`.

## Lists

Lists are defined inductively:

```monad
type List A {
    empty,
    cons (a : A) (List A) : List A
}
```

The type parameter `A` makes this polymorphic:
- `List I64`: A list of 64-bit integers
- `List String`: A list of strings
- `List (List Bool)`: A list of boolean lists

### List Literals

Monad supports list literal syntax `[a, b, c]`, which desugars using the `FromListLiteral` class:

```monad
def nums := [1, 2, 3]
// Desugars to:
// FromListLiteral.cons 1 (FromListLiteral.cons 2 (FromListLiteral.cons 3 FromListLiteral.empty))
```

## Result Type

For representing computations that may fail:

```monad
type Result E A {
    ok (a : A),
    err (e : E)
}
```

## Pattern Matching on Types

When defining functions on types, use pattern matching:

```monad
def isZero (n : Nat) : Bool :=
  match n {
    zero => true,
    succ _ => false
  }

def pred (n : Nat) : Nat :=
  match n {
    zero => zero,
    succ m => m
  }

def plus (n : Nat) (m : Nat) : Nat :=
  match n {
    zero => m,
    succ k => succ (plus k m)
  }
```

## Recursive Functions

Functions on inductive types can be recursive:

```monad
def List.is_empty (self : List A) : Bool :=
  match self {
    empty => true,
    cons a tail => false
  }

def List.append (a b : List A) : List A :=
  match a {
    empty => b,
    cons el_a tail => cons el_a (List.append tail b)
  }

def List.first (self : List A) : Option A :=
  match self {
    empty => none,
    cons a tail => some a
  }
```

## Type Parameters

Types can have type parameters for polymorphism:

```monad
type Option A {
    some (a : A),
    none
}

type Result E A {
    ok (a : A),
    err (e : E)
}
```

## Built-in Types

Monad provides several built-in types in the prelude:

| Type | Description |
|------|-------------|
| `Unit` | Single value `unit` |
| `Bool` | `true` or `false` |
| `I64` | 64-bit signed integer |
| `I32` | 32-bit signed integer |
| `U64` | 64-bit unsigned integer |
| `U32` | 32-bit unsigned integer |
| `U16` | 16-bit unsigned integer |
| `U8` | 8-bit unsigned integer |
| `String` | UTF-8 string |
| `Nat` | Natural numbers (`zero`, `succ`) |
| `List A` | Linked list |
| `Option A` | Optional value |
| `Result E A` | Success or error |
| `Void` | Empty type (no constructors) |
| `Any` | Existential type |

## Summary

- Types define new types through constructors
- Pattern matching destructs values
- Recursive functions operate on types
- Type parameters (`A`) make types polymorphic

Next, we'll explore **type classes**, Monad's mechanism for ad-hoc polymorphism.
