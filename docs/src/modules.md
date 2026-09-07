# Modules and Imports

Monad organizes code into modules, allowing you to structure, reuse, and
namespace your code.

## Basic Module Structure

Each `.mo` file is a module. The module name is derived from its path relative
to a search-path root, with `.` separating directories: `std/concurrent/fiber.mo`
is the module `std.concurrent.fiber`.

## Importing Modules

Use `use` to bring a module into scope, listing exactly the names you want in
`{...}`:

```monad
use io {IO}
use std.path {Path}

def p : Option Path := none
def io_unit : Option (IO Unit) := none
```

An empty `{}` still loads the module — for qualified access, and for its
instances — without binding any bare names:

```monad
use io {}
open IO {println}

def main (args : List String) : IO Unit := println "Hello"
```

`{*}` imports everything explicitly. A bare `use io` with no braces at all still
parses, but the compiler warns that it is deprecated.

## Opening Modules

`open` makes a module's definitions available without their prefix:

```monad
use io {IO}
open IO {println}

def main (args : List String) : IO Unit := println "Hello"
```

Without the `open`, write the full path — which always works:

```monad
use io {IO}

def main (args : List String) : IO Unit := IO.println "Hello"
```

## What the Prelude Opens

The prelude is loaded into every file and opens these, which is why their
constructors are available bare:

```monad,ignore
open Unit {unit}
open Bool {and, false, not, or, true}
open Result {err, ok}
open Option {none, some}
open True {trivial}
```

## The Standard Library

The library is split in two, and the split is a rule, not a convention:

- **`init/`** — pure, portable core. Code that must work in any environment,
  including wasm and embedded targets. No OS-specific natives.
- **`std/`** — OS-specific implementations and genuine side effects.

`IO` itself (the type and its `Monad` instance) lives in `init/io.mo`;
`IO.println` and file access live in `std/io.mo`, because they touch the
operating system.

### What is available without importing

Twelve modules are loaded ambiently: the prelude, plus `id`, `io`, `number`,
`math`, `string`, `list`, the `init` hub, `std.path`, `std.io`, `std.process`,
and the `std` hub. Everything else must be imported.

Note that `prelude` is not a module you can `use` — it is loaded for you.

### The re-export hubs do not cover everything

`use init {...}` resolves to `init/lib.mo`, which re-exports only `id`, `io`,
`number`, `math`, `string`, and `list`. `use std {...}` resolves to
`std/lib.mo`, which re-exports only `std.path`, `std.io`, and `std.process`.

Everything else needs an explicit qualified import. This catches people out, so
here is the full list:

| Module | Ambient? | Contents |
|--------|----------|----------|
| `init` | yes | Re-export hub; `From` class |
| `init.list` | yes | `List.get` |
| `init.string` | yes | String operations |
| `init.math` / `init.number` | yes | All fixed-width numeric ops and instances |
| `init.id` | yes | The `Id` identity monad |
| `init.foldable` | **no** | `Semigroup`, `Monoid`, `Foldable`, `Traversable` |
| `init.optics` | **no** | `Lens`, `Prism`, `view`, `set`, `over` |
| `init.meta` | **no** | Reflection types used by `#[derive]` |
| `io` | yes | The `IO` type and its `Monad` instance |
| `std` | yes | Re-export hub |
| `std.io` | yes | `IO.println`, file I/O, `get_env`, `current_time` |
| `std.path` | yes | The validated `Path` type |
| `std.process` | yes | `exec_cmd`, `process_id` |
| `std.list` | **no** | `length`, `filter`, `any`, `all`, `sum`, `dedup_by`, … |
| `std.map` | **no** | `Map` class, `HashMap`, `BTreeMap` |
| `std.base` | **no** | `Ordering`, `Ord`, `Default`, `Enum`, `Bounded` |
| `std.show` / `std.debug` | **no** | The `Show` and `Debug` classes |
| `std.derive` | **no** | The `#[derive]` backends |
| `std.test` | **no** | `Test.assert` |
| `std.bench` | **no** | Timing helpers |
| `std.ansi` | **no** | Terminal colours |
| `std.sha256` | **no** | SHA-256, in pure Monad |
| `std.concurrent.fiber` / `.combine` | **no** | Fibers and combinators |

See [The Standard Library](./stdlib.md) for what is in each.

## How Modules Are Found

Resolution is a fixed cascade with three special cases, and no configuration.
For a module path `a.b`, the compiler tries, in order:

| Candidate | Notes |
|-----------|-------|
| `init/prelude.mo` | only for the exact name `prelude` |
| `init/lib.mo` | only for the exact name `init` |
| `std/lib.mo` | only for the exact name `std` |
| `{dir of the importing file}/a/b.mo` | relative to the file doing the `use` |
| `a/b.mo` | relative to the working directory |
| `init/a/b.mo` | |
| `std/a/b.mo` | |
| `lang/a/b.mo` | |
| `examples/a/b.mo` | |

First hit wins. `init` and `std` need their own cases because their module
*names* no longer match their *file* names — both resolve to a `lib.mo`
re-export hub.

Four of the nine candidates are relative to the working directory, so running
the compiler from a different directory can change which modules resolve. That
is the most common cause of a surprising "module not found".

There is no search-path flag and no environment variable. There is also no
package system — the [bootstrap host](./bootstrap-host.md#packages-motes) has
one (*motes*), but the self-hosted compiler does not read manifests at all.

## Visibility

Declarations have three visibility levels:

```monad
pub def exported : I64 := 1        // visible everywhere
priv def internal : I64 := 2       // visible only in this file
def package_private : I64 := 3     // the default
```

The default is package-private. `pub use module {*}` re-exports an import, which
is how the `init` and `std` hubs work.

## Unused Imports

The compiler warns when a name listed in a `use`/`open` is never referenced:

```text
warning: unused import `Path` from `std.path`
```

The [bootstrap host](./bootstrap-host.md#editor-and-agent-tooling) can rewrite
the declarations for you — `monad-rs organize-imports --write` computes the
minimal name list, converts bare `use`/`open` to the explicit form, and deletes
imports that contribute nothing. There is no equivalent in the self-hosted
compiler.

## Complete Example

```monad
use io {IO}
open IO {println}

def say_hello (s : String) : IO Unit := println s

def main (args : List String) : IO Unit :=
    args
        |> List.last
        |> (Option.get_or_default "no arguments")
        |> say_hello
```

## Summary

- Each `.mo` file is a module; paths use `.` for directories
- `use Module {names}` loads a module; `open Module {names}` drops the prefix
- `{*}` imports everything; bare `use`/`open` is deprecated
- `init/` is pure and portable, `std/` is OS-specific
- Only 12 modules are ambient — most of `std/` needs an explicit import
- Resolution is a fixed nine-candidate cascade, partly working-directory relative
- There is no package system in the self-hosted compiler
- `pub`/`priv`/package-private control visibility

Next, we'll explore **the IO monad** for effectful programming.
