# Modules and Imports

Monad organizes code into modules, allowing you to structure, reuse, and namespace your code effectively.

## Basic Module Structure

Each `.mo` file is a module. The module name is derived from the file path.

## Importing Modules

Use `use` to bring a module into scope:

```monad
use io
use init
use math
```

After `use io`, you can access definitions with their full path:

```monad
use io

def main (args : List String) : IO Unit := IO.println "Hello"
```

## Opening Modules

Use `open` to make a module's definitions available without prefixes:

```monad
use io
open IO

def main (args : List String) : IO Unit := println "Hello"
```

Now `println` is available directly instead of `IO.println`.

## Opening Standard Types

The prelude opens several types by default:

```monad
open Unit    // makes `unit` available
open Bool    // makes `true`, `false` available
open Result  // makes `ok`, `err` available
open Option  // makes `some`, `none` available
```

## Module Paths

Definitions are accessed using dot notation:

```monad
use init

def result : I64 := I64.add 3 4
```

## The Standard Library

Monad ships with several standard modules:

| Module | Description |
|--------|-------------|
| `prelude` | Basic types and classes (auto-loaded) |
| `init` | Initialization, I64.add, From class |
| `io` | IO monad and IO.println |
| `math` | HMul class and (*) operator |
| `string` | String operations (concat, length, get) |
| `term` | Meta-representation of Monad's AST |
| `parser` | Parser combinators |
| `tests` | Standard library tests |
| `std/test` | Test utilities (Test.assert) |

## Complete Example

```monad
use io
use init
open IO

def say_hello (s : String) : IO Unit := println s

def main (args : List String) : IO Unit :=
    args
        |> List.last
        |> (Option.get_or_default "no arguments")
        |> say_hello
```

## Summary

- Each `.mo` file is a module
- `use` brings modules into scope
- `open` makes definitions available without prefixes
- Dot notation accesses definitions by path
- Standard library modules provide common functionality

Next, we'll explore **the IO monad** for effectful programming.
