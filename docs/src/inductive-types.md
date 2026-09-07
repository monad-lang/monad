# Types

Types are the foundation of data structures in Monad. This chapter covers
inductive types, the primary way to define new types.

## Basic Syntax

Types are declared with the `type` keyword:

```monad
type Colour {
    red,
    green,
    blue
}
```

This defines a type `Colour` with three constructors.

## Constructors with Fields

Constructors can carry data:

```monad
type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64)
}
```

## Natural Numbers

The canonical example of an inductive type is the natural numbers, defined in
the prelude as:

```monad,ignore
type Nat {
    zero,
    succ (n : Nat)
}
```

This defines:
- `zero`: the natural number 0
- `succ n`: the successor of `n` (i.e. `n + 1`)

So `3` is represented as `succ (succ (succ zero))`.

## Lists

Lists are defined inductively:

```monad,ignore
type List A {
    empty,
    cons (a : A) (List A) : List A
}
```

The type parameter `A` makes this polymorphic:
- `List I64`: a list of 64-bit integers
- `List String`: a list of strings
- `List (List Bool)`: a list of boolean lists

### List Literals

Monad supports list literal syntax `[a, b, c]`, which desugars through the
`FromListLiteral` class:

```monad
def nums : List I64 := [1, 2, 3]
// Desugars to:
// FromListLiteral.cons 1 (FromListLiteral.cons 2
//   (FromListLiteral.cons 3 FromListLiteral.empty))
```

The annotation matters: the literal is polymorphic in its container, so the
checker needs the target type to pick the instance.

## Tuples

Parenthesised comma-separated values are tuple literals. They desugar to
right-nested `Pair.pair` applications, so `(x, y, z)` is
`Pair.pair x (Pair.pair y z)`:

```monad
def point : Pair I64 I64 := (3, 4)
def triple : Pair I64 (Pair String Bool) := (1, "two", true)
```

`(x,)` and `(x)` both mean just `x`.

## Result Type

For representing computations that may fail:

```monad,ignore
type Result E A {
    ok (a : A),
    err (e : E)
}
```

## Pattern Matching on Types

When defining functions over a type, use pattern matching:

```monad
def is_zero (n : Nat) : Bool :=
  match n {
    zero => true,
    succ _ => false
  }

def pred (n : Nat) : Nat :=
  match n {
    zero => Nat.zero,
    succ m => m
  }

def plus (n : Nat) (m : Nat) : Nat :=
  match n {
    zero => m,
    succ k => Nat.succ (plus k m)
  }
```

Constructors used in a *pattern* are written bare (`zero`, `succ k`), but
constructors used to *build* a value need their qualified name (`Nat.succ`)
unless the type has been `open`ed. The prelude opens `Bool`, `Option`, `Result`,
and `Unit`, which is why `true`, `some`, and `ok` work bare everywhere.

## Recursive Functions

Functions over inductive types can be recursive:

```monad
def is_empty {A : Type} (self : List A) : Bool :=
  match self {
    empty => true,
    cons a tail => false
  }

def append {A : Type} (a : List A) (b : List A) : List A :=
  match a {
    empty => b,
    cons el_a tail => List.cons el_a (append tail b)
  }

def first {A : Type} (self : List A) : Option A :=
  match self {
    empty => none,
    cons a tail => some a
  }
```

Each of these recurses on a structural subterm of its argument, so the
[termination checker](./termination.md) accepts them without an attribute.
(`List.is_empty`, `List.append`, and `List.first` already exist in the prelude —
these are shown as illustrations.)

## Type Parameters

Types can have type parameters for polymorphism:

```monad,ignore
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

Monad provides these types in the prelude, available without any import:

| Type | Constructors | Description |
|------|-------------|-------------|
| `Unit` | `unit` | Single value |
| `Bool` | `true`, `false` | Boolean |
| `I64` … `I8` | (primitive) | Signed integers, 64/32/16/8 bit |
| `U64` … `U8` | (primitive) | Unsigned integers, 64/32/16/8 bit |
| `F64`, `F32` | (primitive) | Floats |
| `String` | `of_bytes` | UTF-8 string |
| `Char` | `of_bytes` | One Unicode codepoint, written `'x'` — but see the caveat below |
| `Nat` | `zero`, `succ` | Natural numbers |
| `List A` | `empty`, `cons` | Linked list |
| `Option A` | `some`, `none` | Optional value |
| `Result E A` | `ok`, `err` | Success or error |
| `Pair A B` | `pair` | Two-element product; the target of tuple syntax |
| `Void` | (none) | Empty type |
| `Any` | `any` | Existential wrapper |
| `IO A` | `io` | The IO monad |
| `True` | `trivial` | Trivially true proposition (in `Prop`) |
| `Eq A a b` | `refl` | Propositional equality (in `Prop`) |
| `Vec n A` | `nil`, `cons` | Length-indexed vector |

`True`, `Eq`, and `Vec` are the dependently typed corner of the prelude — see
[Dependent Types](./dependent-types.md).

> **`Char` is a stub type.** Character literals (`'M'`, `'\n'`, `'λ'`) parse,
> type-check and compile in both implementations, but `Char` has no operations
> at all — no `BEq`, no `ToString`, no `Char.*` functions. A `Char` can be
> written, typed, passed and stored; nothing can inspect one. Use `String` for
> text you need to work with.

## Summary

- `type` defines new types through constructors
- Pattern matching destructures values, one constructor level at a time
- Recursive functions operate on inductive types
- Type parameters (`A`) make types polymorphic
- Tuple syntax `(a, b)` is sugar for `Pair`

Next, we'll explore **type classes**, Monad's mechanism for ad-hoc polymorphism.
