# The IO Monad

Monad manages side effects through the `IO` monad.

## IO as a Monad

`IO A` represents a computation that, when executed, produces an `A` and may
have side effects:

```monad
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

**Never name the `io` constructor outside `init/src/io.mo`.** Wrap a pure value
with **`IO.pure`**, and reach a value's contents with **`Monad.bind`** —
`let x <- action;` in a `do` block — which is what the instance above does.
Constructing with `IO.io`, or matching on it, is not what the constructor is
for, and keeping every other file off it is what leaves it free to become a
native.

The *operations* — printing, files, the clock — live in `std/io.mo`, because
they touch the operating system.

## Basic IO Operations

```monad
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

> **A wart worth knowing.** Naming `IO` in a *non-empty* `use` filter can break
> `do`-notation's implicit `Monad IO` lookup at run time ("instance-Monad-IO not
> found"), even though the file type-checks. `open`'s filtering is unaffected.
> Since `IO` and its instance are ambient, the fix is to import nothing at all:
> `open IO {println}` for the bare names you write, and no `use` line. This is a
> known bug in how instance resolution interacts with non-empty `use` filters.

## Sockets and TCP

`std.io` also holds the whole TCP surface — two opaque types and nine blocking
natives:

| Function | Type |
|----------|------|
| `IO.tcp_connect` | `String -> U16 -> IO (Result String Socket)` |
| `IO.tcp_listen` | `U16 -> IO (Result String Listener)` |
| `IO.tcp_accept` | `Listener -> IO (Result String Socket)` |
| `IO.tcp_read` | `Socket -> U64 -> IO (Result String (List U8))` |
| `IO.tcp_write` | `Socket -> List U8 -> IO (Result String U64)` |
| `IO.tcp_close` | `Socket -> IO Unit` |
| `IO.tcp_close_listener` | `Listener -> IO Unit` |
| `IO.tcp_local_port` | `Listener -> IO U16` |
| `IO.tcp_fd` | `Socket -> IO I32` |

`IO.tcp_fd` extracts the raw descriptor behind a `Socket` — typed extraction,
not a lookup (a `Socket` IS the fd), for handing to an FFI function such as
OpenSSL's `SSL_set_fd`.

`Socket` and `Listener` are opaque. Each has a single zero-arity constructor so
that the type checker has a name for the type; the runtime value is never one of
them. That is what lets the implementation carry a bare file descriptor instead
of a handle — so nothing may pattern-match, compare or print either.

```monad

/// Send one request over a fresh connection and return whatever comes back.
/// Every step can fail, so each is matched on rather than discarded.
def fetch (host : String) (port : U16) : IO (Result String String) := do {
    let opened <- IO.tcp_connect host port;
    match opened {
        Result.err e => return (Result.err e),
        Result.ok sock => do {
            let sent <- IO.tcp_write sock (String.to_list "GET / HTTP/1.0\r\n\r\n");
            match sent {
                Result.err e => do {
                    IO.tcp_close sock;
                    return (Result.err e)
                },
                Result.ok _ => do {
                    let got <- IO.tcp_read sock 4096u64;
                    IO.tcp_close sock;
                    match got {
                        Result.err e => return (Result.err e),
                        Result.ok bytes => return (Result.ok (String.from_list bytes))
                    }
                }
            }
        }
    }
}
```

`IO.tcp_listen 0u16` binds `0.0.0.0` on an OS-assigned port; read the port it
actually settled on back with `IO.tcp_local_port`:

```monad
open IO {println}

/// Listen on an OS-assigned port, print it, accept one connection, echo back
/// what it sends, and close everything.
def echo_once : IO Unit := do {
    let bound <- IO.tcp_listen 0u16;
    match bound {
        Result.err e => println e,
        Result.ok listener => do {
            let port <- IO.tcp_local_port listener;
            println (U16.to_string port);
            let accepted <- IO.tcp_accept listener;
            IO.tcp_close_listener listener;
            match accepted {
                Result.err e => println e,
                Result.ok conn => do {
                    let got <- IO.tcp_read conn 1024u64;
                    match got {
                        Result.err e => println e,
                        Result.ok bytes => do {
                            let written <- IO.tcp_write conn bytes;
                            match written {
                                Result.err e => println e,
                                Result.ok n => println (U64.to_string n)
                            }
                        }
                    };
                    IO.tcp_close conn
                }
            }
        }
    }
}
```

`IO.tcp_close_listener` closes the listening socket only; connections already
accepted from it keep working, which is why the snippet above can close the
listener and then talk on `conn`. `IO.tcp_write` writes *all* of the bytes it is
given — the count it returns is the full length, never a partial one, so there
is no write loop to write.

### What is not there

- **TCP is self-hosted only.** The eight natives are implemented by
  `runtime/src/runtime.c`, which the self-hosted backend compiles; the Rust
  bootstrap host deliberately has no TCP implementation at all, so under it any
  of these fails at run time with `unknown native: tcp_listen` (or whichever was
  called). A socket test therefore cannot run under `cargo run -- test`, and the
  `examples/` HTTP entry is pure by design for exactly that reason.
- **No read timeout, and no non-blocking mode.** `tcp_connect`, `tcp_accept` and
  `tcp_read` block until they complete. A peer that connects and then sends
  nothing holds the accepting fiber and its OS thread indefinitely; nothing in
  the library breaks that. The mitigation in `motes/moon/src/server.mo` is a cap
  on requests served per connection, which bounds an *idle keep-alive client*,
  not a silent one. A real timeout is not implemented.
- **EOF is not an error.** When the peer closes, `IO.tcp_read` returns
  `Result.ok List.empty` rather than failing, and read loops terminate on exactly
  that. `IO.tcp_close` never fails.

A working server and client built on these live in `motes/moon/src/server.mo` and
`motes/moose/src/client.mo`.

## Do Notation

A `do` block sequences monadic actions. Two equivalent spellings:

### `do { ... }`

```monad
open IO {println}

def greet : IO Unit := do {
    println "Enter your name:";
    println "Hello!"
}
```

### Inline block on the definition

A definition can use `{ ... }` directly in place of `:= do { ... }`:

```monad
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

There are 146 natives declared across `init/` and `std/`. Three — `eq_rec`, `string_to_chars`, and
`string_from_chars` — are declared but not implemented anywhere, and calling one
fails at run time with `unknown native`. The compiler backend wires a subset of
the rest; see [Compiling and Running](./compiling.md#native-coverage). The eight
`tcp_*` natives above are among the wired ones, but only in the self-hosted
backend — the Rust host has no TCP implementation at all.

## Running IO Programs

The runtime executes `main`, passing command-line arguments as a `List String`:

```monad
open IO {println}

def main (args : List String) : IO Unit :=
    println "Starting..."
```

```bash
monad build program.mo -o program
./program arg1 arg2      # args reach `main`
```

`main` may also return `I64`, in which case it becomes the process exit code.
See [Compiling and Running](./compiling.md).

## Combining IO with Other Types

```monad
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
