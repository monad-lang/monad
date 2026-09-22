# Structs

Structs define record types with named fields, providing a convenient syntax for
single-constructor types.

## Basic Syntax

Structs are declared with the `struct` keyword:

```monad
struct Point {
    x : I64,
    y : I64
}
```

## Creating Struct Values

Struct values are created with brace syntax. The literal is not inferrable on
its own, so it needs a type from context — usually the `def`'s own annotation:

```monad
struct Point {
    x : I64,
    y : I64
}

def origin : Point := { x := 0, y := 0 }
def p : Point := { x := 3, y := 4 }
```

## Field Default Values

Fields can have default values using `:=`, and may then be omitted:

```monad
struct Rect {
    w : I64,
    h : I64 := 100
}

def wide : Rect := { w := 50 }   // h defaults to 100
```

## Struct Update

`{ base with field := value }` copies a value, replacing the named fields:

```monad
struct Point {
    x : I64,
    y : I64
}

def p1 : Point := { x := 1, y := 2 }
def p2 : Point := { p1 with x := 10 }   // { x := 10, y := 2 }
```

## Field Access

Access fields using dot notation, which chains:

```monad
struct Inner { v : I64 }
struct Outer { inner : Inner }

def get_v (o : Outer) : I64 := o.inner.v
```

Dot notation is **field access only**. `x.some_function` does not call
`Type.some_function x` — there is no UFCS-style method dispatch, and naming
something that is not a declared field is an error. Call functions with their
qualified name: `String.length s`, not `s.length`.

## Pattern Matching on Structs

A struct's implicit constructor is called `mk`, so you can match positionally:

```monad
struct Point {
    x : I64,
    y : I64
}

def swap (p : Point) : Point :=
    match p {
        mk x y => { x := y, y := x }
    }
```

Or match on field names, in any order, with `..` to ignore the rest:

```monad
struct Point3 {
    x : I64,
    y : I64,
    z : I64
}

def flatten (p : Point3) : I64 :=
    match p {
        {y, x, ..} => x + y
    }
```

## Destructuring in Parameters

The same field pattern works directly in a parameter position:

```monad
struct Point {
    x : I64,
    y : I64
}

def sum_point ({x, y} : Point) : I64 := x + y
```

## Keyword Arguments

A constructor or a `def` can be called with its parameters named, in any order:

```monad
type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64)
}

def area (s : Shape) : I64 :=
    match s {
        circle r => r * r,
        rectangle w h => w * h
    }

def r : Shape := Shape.rectangle { height := 3, width := 4 }
def c : Shape := Shape.circle { radius := 5 }
```

A `def` can also declare its whole parameter list as one brace block, which is
the only spelling that allows parameter defaults:

```monad
def scale {factor : I64 := 2, p : I64} : I64 := factor * p

def a : I64 := scale { p := 4, factor := 3 }   // 12
def b : I64 := scale { p := 4 }                // 8, factor defaulted
```

Both compilers honour it. A def's own parameter defaults now behave exactly
like a `struct`/`type` field's: `scale { p := 4 }` is 8 everywhere, and an
omitted parameter is an error only when it declares no default. See
[The Bootstrap Host](./bootstrap-host.md) for what is still host-only.

## Linear and Affine Fields

Fields can carry a multiplicity annotation — `!` (linear, exactly once), `?`
(affine, at most once), or nothing (unrestricted):

```monad
struct Buffer {
    !data : String,
    ?label : String,
    size : I64
}
```

These parse and are stored, but are **not currently enforced** — see
[Linear Types](./linear-types.md).

## Structs vs Types

A struct is a single-constructor type whose constructor is named `mk`. This
struct:

```monad,ignore
struct Point {
    x : I64,
    y : I64
}
```

is equivalent to:

```monad,ignore
type Point {
    mk (x : I64) (y : I64)
}
```

## Generic Structs: a Known Limitation

`struct` accepts type parameters, but a generic struct is currently very hard to
construct: the brace literal cannot be inferred even with an annotation
(`cannot infer the type of { .. }`), and calling `mk` directly reports a type
mismatch between the bare type constructor and its application.

Until that is fixed, write a generic record as a `type` with a positional
constructor instead:

```monad
type Box A {
    mk (item : A)
}

def b : Box I64 := Box.mk 42
```

## Summary

- `struct` defines record types with named fields
- Struct values use `{ field := value }` and need a type from context
- `{ base with f := v }` updates; `{x, y}` destructures, in patterns and params
- Constructors and defs accept keyword arguments; brace-form params take defaults
- Dot notation is field access, not method dispatch
- Generic structs are not usable yet — use a `type` instead

Next, we'll explore **error handling** patterns in Monad.
