# Dependent Types

Monad supports dependent types, where types can depend on values. This enables precise specifications and expressive type signatures.

## Pi Types (Function Types)

The standard function type `A -> B` is a Pi type where the result type does not depend on the input value.

```monad
def add (a : I64) (b : I64) : I64 := a + b
```

## Forall Types (Implicit Arguments)

The `{A : Type}` syntax introduces implicit arguments that are inferred by the type checker:

```monad
def identity {A : Type} (x : A) : A := x

// Called without specifying A:
def result := identity 42  // A is inferred as I64
```

## Type Annotations

You can add type annotations with `:`:

```monad
def x : I64 := 42
```

## Holes (Type Inference)

The `_` placeholder (Hole) tells the type checker to infer the type:

```monad
def x := _  // Type will be inferred
```

## Universe Levels

`Type` represents the universe of types (universe 0). You can also use higher universes:

```monad
Type      // Universe 0
Type 1    // Universe 1
Type 2    // Universe 2
```

## Prop

`Prop` is the type of propositions, used for logical statements:

```monad
def myProp : Prop := ...
```

## Type-Level Functions

Types can be computed from values:

```monad
type Result E A {
    ok (a : A),
    err (e : E)
}

// Result takes type parameters E and A
def success : Result String I64 := ok 42
```

## Dependent Type Examples

### Option with Default

```monad
def Option.get_or_default (default : A) (self : Option A) : A :=
    match self {
        some a => a,
        none => default
    }
```

The return type `A` depends on the type parameter of `Option A`.

### Polymorphic List Operations

```monad
def List.first (self : List A) : Option A :=
    match self {
        empty => none,
        cons a tail => some a
    }
```

The return type `Option A` depends on the element type of the list.

## Summary

- Pi types represent function types
- Forall types `{A : Type}` introduce implicit arguments
- Holes `_` enable type inference
- Universe levels (`Type`, `Type 1`) organize types
- `Prop` represents logical propositions
- Dependent types enable precise specifications

Next, we'll explore **structs**, a convenient way to define record types.
