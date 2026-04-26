# Error Handling

Monad provides functional error handling through the `Result` and `Option` types.

## The Result Type

The `Result` type represents computations that may fail with an error:

```monad
type Result E A {
    ok (a : A),
    err (e : E)
}
```

### Basic Usage

```monad
def divide (a : I64) (b : I64) : Result String I64 :=
    if b == 0
    then err "division by zero"
    else ok (a / b)
```

### Handling Results

Use pattern matching to handle both cases:

```monad
def handleResult (r : Result String I64) : String :=
    match r {
        ok n => "Success: " ++ n,
        err e => "Error: " ++ e
    }
```

### Chaining Results with Monad

The `Result` type can have a `Monad` instance for chaining:

```monad
def compute (x : I64) (y : I64) : Result String I64 :=
    divide x y >>= fn result =>
        ok (result * 2)
```

## The Option Type

The `Option` type represents computations that may return nothing:

```monad
type Option A {
    some (a : A),
    none
}
```

### Basic Usage

```monad
def List.first (self : List A) : Option A :=
    match self {
        empty => none,
        cons a tail => some a
    }
```

### Handling Options

```monad
def getFirst (xs : List I64) : I64 :=
    match List.first xs {
        some a => a,
        none => 0
    }
```

### Using get_or_default

```monad
def firstOrDefault (xs : List I64) : I64 :=
    Option.get_or_default 0 (List.first xs)
```

## Custom Error Types

Define domain-specific error types:

```monad
type DatabaseError {
    notFound,
    connectionFailed,
    permissionDenied,
    timeout
}

def findUser (id : I64) : Result DatabaseError String :=
    err notFound
```

## Combining with the IO Monad

Error handling in effectful code:

```monad
use io
open IO

def main (args : List String) : IO Unit :=
    match List.first args {
        some arg => println ("First arg: " ++ arg),
        none => println "No arguments provided"
    }
```

## Summary

- `Result E A` for errors with payloads
- `Option A` for simple failure cases
- Pattern matching for handling both types
- Monad instances enable chaining with `>>=`
- Define custom error types for domain-specific errors

Next, we'll explore **modules and imports** for organizing code.
