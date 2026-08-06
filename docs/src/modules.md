# Modules and Imports

Monad organizes code into modules, allowing you to structure, reuse, and namespace your code effectively.

## Basic Module Structure

Each `.mo` file is a module. The module name is derived from the file path.

## Importing Modules

Use `use` to bring a module into scope, listing exactly the names you need in `{...}`:

```monad
use io {IO}
use init {IO}
use math {}
```

An empty `{}` still imports the module (for qualified access) without bringing any bare names into scope.

After `use io {...}`, you can access definitions with their full path:

```monad
use io {IO}

def main (args : List String) : IO Unit := IO.println "Hello"
```

Bare `use io` (no braces) still parses but is deprecated — the compiler warns and suggests `use io {*}`.

## Opening Modules

Use `open` to make a module's definitions available without prefixes, again naming exactly what you need:

```monad
use io {IO}
open IO {println}

def main (args : List String) : IO Unit := println "Hello"
```

Now `println` is available directly instead of `IO.println`. Like `use`, a bare `open IO` (no braces) still parses but is deprecated in favor of an explicit filter — `open IO {*}` if you genuinely need everything.

## Opening Standard Types

The prelude opens several types by default:

```monad
open Unit {unit}                  // makes `unit` available
open Bool {and, false, not, or, true}
open Result {err, ok}
open Option {none, some}
```

## Module Paths

Definitions are accessed using dot notation:

```monad
use init {}

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
use io {IO}
use init {}
open IO {println}

def say_hello (s : String) : IO Unit := println s

def main (args : List String) : IO Unit :=
    args
        |> List.last
        |> (Option.get_or_default "no arguments")
        |> say_hello
```

## Unused Imports

The compiler warns when an explicitly-listed `use`/`open` name is never referenced in the file — remove it, or run `monad-rs organize-imports --write` to have the compiler rewrite (and, where a `use` contributes nothing at all, delete) the declaration for you.

## Summary

- Each `.mo` file is a module
- `use Module {names}` brings a module into scope, selecting exactly which names become bare-accessible
- `open Module {names}` makes definitions available without prefixes
- `{*}` imports/opens everything explicitly; bare `use`/`open` (no braces) still works but is deprecated
- Dot notation accesses definitions by path
- Standard library modules provide common functionality

Next, we'll explore **the IO monad** for effectful programming.
