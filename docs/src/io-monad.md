# The IO Monad

Monad provides a safe way to perform side effects through the `IO` monad.

## IO as a Monad

`IO A` represents a computation that, when executed, produces an `A` and may have side effects:

```monad
use io
open IO

def main (args : List String) : IO Unit := println "Hello, World!"
```

## Basic IO Operations

### Printing Output

```monad
use io
open IO

def main (args : List String) : IO Unit :=
    println "Hello, World!"
```

`IO.println` takes a `String` and returns `IO Unit`.

## The IO Type

The IO type is defined as:

```monad
type IO A {
    io A
}
```

## IO Monad Instance

```monad
instance Monad IO {
    def pure (a : A) : IO A := a
    def bind (a : IO A) (f : A -> IO B) : IO B :=
        match a {
            io a => f a
        }
}
```

## Do Notation

The `do` block sequences IO actions:

```monad
use io
open IO

def greet : IO Unit :=
    do {
        println "Enter your name:"
        -- name <- getLine  -- Note: getLine not yet implemented
        println "Hello!"
    }
```

## Native Functions

IO operations are implemented as native functions that call Rust code:

```monad
@[native println]
def IO.println (s : String) : IO Unit
```

The `@[native name]` attribute marks a function as implemented in Rust.

## Running IO Programs

The runtime executes the `main` function:

```monad
use io
open IO

def main (args : List String) : IO Unit :=
    println "Starting..."
```

Run with:

```bash
cargo run -- run program.mo
```

Command-line arguments are passed to `main` as `List String`.

## Combining IO with Other Types

```monad
use io
use init
open IO

def printResult (r : Result String I64) : IO Unit :=
    match r {
        ok n => println ("Success: " ++ n),
        err e => println ("Error: " ++ e)
    }

def main (args : List String) : IO Unit :=
    printResult (ok 42)
```

## Summary

- `IO A` encapsulates side effects
- `IO.println` is the primary output function
- `do` notation sequences IO actions
- `IO` is a proper monad with `pure` and `bind`
- `main` is the program entry point, receiving `List String` arguments
- Native functions bridge Monad and Rust

This concludes the tutorial series. Continue to the reference documentation for detailed API information.
