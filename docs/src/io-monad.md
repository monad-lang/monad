# The IO Monad

Monad manages side effects through the `IO` monad.

## IO as a Monad

`IO A` represents a computation that, when executed, produces an `A` and may
have side effects:

```monad
use io {IO}
open IO {println}

def main (args : List String) : IO Unit := println "Hello, World!"
```

## The IO Type

`IO` is defined in `init/io.mo`, the pure and portable half of the standard
library:

```monad,ignore
type IO A {
    io A
}

def IO.pure (a : A) : IO A := IO.io a

instance Monad IO {
    def pure (a : A) : IO A := IO.pure a
    def bind (a : IO A) (f : A -> IO B) : IO B :=
        match a {
            io a => f a
        }
}
```

Wrap a pure value with **`IO.pure`**, not the `IO.io` constructor: `io` exists so
`bind` can match on it, and is meant to become an implementation detail.

The *operations* — printing, files, the clock — live in `std/io.mo`, because
they touch the operating system.

## Basic IO Operations

```monad
use io {}
open IO {println}

def main (args : List String) : IO Unit :=
    println "Hello, World!"
```

`IO.println` takes a `String` and returns `IO Unit`. It does not coerce, so
print a number via `I64.to_string` or `ToString.to_string`.

Other operations in `std.io`:

| Function | Type |
|----------|------|
| `IO.println` | `String -> IO Unit` |
| `IO.read_file` | `Path -> IO String` |
| `IO.write_file` | `Path -> String -> IO Unit` |
| `IO.file_exists` | `Path -> IO Bool` |
| `IO.is_dir` | `Path -> IO Bool` |
| `IO.list_dir` | `Path -> IO (List String)` |
| `IO.get_env` | `String -> IO (Option String)` |
| `IO.current_time` | `IO I64` (monotonic milliseconds) |

There is no `getLine` — reading stdin is not implemented yet.

> **A gotcha worth knowing.** Listing names in `use io {IO}` can break
> `do`-notation's implicit `Monad IO` lookup at run time ("instance-Monad-IO not
> found"), even though the file type-checks. `open`'s filtering is unaffected.
> The workaround, used throughout `examples/`, is `use io {}` plus
> `open IO {println}`. This is a known bug in how instance resolution interacts
> with non-empty `use` filters.

## Do Notation

A `do` block sequences monadic actions. Two equivalent spellings:

### `do { ... }`

```monad
use io {}
open IO {println}

def greet : IO Unit := do {
    println "Enter your name:";
    println "Hello!"
}
```

### Inline block on the definition

A definition can use `{ ... }` directly in place of `:= do { ... }`:

```monad
use io {}
open IO {println}

def greet : IO Unit {
    println "Enter your name:";
    println "Hello!"
}

def greet_with_name (name : String) : IO Unit {
    let greeting := "Hello, " ++ name;
    println greeting
}
```

**Separate statements with `;`.** Two adjacent expressions without a semicolon
are parsed as a single application, which produces a confusing error like
`expected a function type, found (IO Unit)`.

### Do Block Statements

| Statement | Syntax | Desugars to |
|-----------|--------|-------------|
| Bind | `let x <- action` | `Monad.bind action (fn x => ...)` |
| Let | `let x := value` | `let x := value in ...` |
| Return | `return value` | `Monad.pure value` |
| Expression | `expr` | `Monad.bind expr (fn _ => ...)` |

A worked example using all four:

```monad
use io {}
use std.io {}
open IO {println}

def show_home : IO Unit {
    println "Looking up $HOME";
    let home <- IO.get_env "HOME";
    let shown := Option.get_or_default "(unset)" home;
    println shown
}

def five : IO I64 {
    let x := 5;
    return x
}
```

Do notation is not IO-specific — it works for any type with a `Monad` instance.
The standard library provides `Monad IO` and `Monad Id`; notably **not**
`Monad Result` or `Monad Option`.

## Native Functions

IO operations are implemented as natives that call into Rust:

```monad,ignore
#[native print_str]
def IO.println (s : String) : IO Unit
```

The `#[native name]` attribute marks a definition as implemented outside Monad,
and such a definition has no body. The name in the attribute is the runtime's
identifier for the operation, which is not always the Monad-side name — the
native behind `IO.println` is `print_str`.

There are 134 natives declared across `init/` and `std/`. Three — `eq_rec`, `string_to_chars`, and
`string_from_chars` — are declared but not implemented anywhere, and calling one
fails at run time with `unknown native`. The compiler backend wires a subset of
the rest; see [Compiling and Running](./compiling.md#native-coverage).

## Running IO Programs

The runtime executes `main`, passing command-line arguments as a `List String`:

```monad
use io {}
open IO {println}

def main (args : List String) : IO Unit :=
    println "Starting..."
```

```bash
monad compile program.mo -o program
./program arg1 arg2      # args reach `main`
```

`main` may also return `I64`, in which case it becomes the process exit code.
See [Compiling and Running](./compiling.md).

## Combining IO with Other Types

```monad
use io {}
open IO {println}

def print_result (r : Result String I64) : IO Unit :=
    match r {
        ok n => println ("Success: " ++ I64.to_string n),
        err e => println ("Error: " ++ e)
    }

def main (args : List String) : IO Unit :=
    print_result (ok 42)
```

## Summary

- `IO A` encapsulates side effects; the type is in `init.io`, the operations in `std.io`
- `do` notation sequences actions, in both `do { }` and inline `def f : T { }` form
- Statements must be separated by `;`
- `IO` is a proper monad with `pure` and `bind`
- `main` is the entry point, receiving `List String`
- Natives bridge Monad and Rust

That concludes the tutorial. The Advanced chapters go deeper: **dependent types**,
**macros**, **linear types**, and **concurrency**.
