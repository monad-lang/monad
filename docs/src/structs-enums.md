# Structs

Structs define record types with named fields, providing a convenient syntax for single-constructor types.

## Basic Syntax

Structs are declared with the `struct` keyword:

```monad
struct Point {
    x : I64,
    y : I64
}
```

## Field Default Values

Fields can have default values using `:=`:

```monad
struct Point3D {
    x : I64,
    y : I64,
    z : I64 := 0
}

def origin := { x := 0, y := 0 }
// z defaults to 0
```

## Linear and Affine Fields

Field access can be restricted with multiplicity annotations `!` (linear, exactly once) or `?` (affine, at most once):

```monad
struct Resource {
    !handle : FileHandle,   // linear — must be used exactly once
    ?label : String,        // affine — may be unused
    metadata : I64          // unrestricted (default)
}
```

## Creating Struct Values

Struct values are created with brace syntax:

```monad
def origin := { x := 0, y := 0 }
def p := { x := 3, y := 4 }
```

## Field Access

Access fields using dot notation:

```monad
def getX (p : Point) : I64 := p.x
def getY (p : Point) : I64 := p.y
```

## Structs vs Types

A struct is equivalent to a single-constructor type. This struct:

```monad
struct Point {
    x : I64,
    y : I64
}
```

Is equivalent to:

```monad
type Point {
    mk (x : I64) (y : I64)
}
```

## Generic Structs

Structs can have type parameters:

```monad
struct Pair A B {
    first : A,
    second : B
}

def example := { first := "hello", second := 42 }
```

## Pattern Matching on Structs

You can pattern match on struct constructors:

```monad
def swap (p : Point) : Point :=
    match p {
        mk x y => { x := y, y := x }
    }
```

## Summary

- `struct` defines record types with named fields
- Struct values use `{ field := value }` syntax
- Field access uses dot notation
- Structs are equivalent to single-constructor types

Next, we'll explore **error handling** patterns in Monad.
