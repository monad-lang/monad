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
| `IO.read_file` | `Path -> IO (Result StreamError String)` |
| `IO.write_file` | `Path -> String -> IO (Result StreamError Unit)` |
| `IO.read_line` | `IO (Result StreamError (Option String))` |
| `IO.file_exists` | `Path -> IO Bool` |
| `IO.is_dir` | `Path -> IO Bool` |
| `IO.list_dir` | `Path -> IO (List Path)` (entries joined onto the directory, sorted) |
| `IO.get_env` | `String -> IO (Option String)` |
| `IO.current_time` | `IO I64` (monotonic milliseconds) |

An operation that can fail returns its failure as a `Result.err` carrying a
`std.stream` `StreamError`: a `kind` to match on (`not_found`,
`permission_denied`, ...) and the OS `message`. A missing file is
`not_found`, never an empty string, so a caller decides for itself what
absence means. `IO.read_line` is `Result.ok Option.none` at end of input.

> **A wart worth knowing.** Naming `IO` in a *non-empty* `use` filter can break
> `do`-notation's implicit `Monad IO` lookup at run time ("instance-Monad-IO not
> found"), even though the file type-checks. `open`'s filtering is unaffected.
> Since `IO` and its instance are ambient, the fix is to import nothing at all:
> `open IO {println}` for the bare names you write, and no `use` line. This is a
> known bug in how instance resolution interacts with non-empty `use` filters.

## Sockets and TCP

`std.io` holds TCP's setup calls: four blocking functions that open
connections and listeners. Both are `FdStream`s from `std.stream`, so you
read, write and close them with the same `Stream` methods you use for a file:

| Function | Type |
|----------|------|
| `IO.tcp_connect` | `String -> U16 -> IO (Result StreamError FdStream)` |
| `IO.tcp_listen` | `U16 -> IO (Result StreamError FdStream)` |
| `IO.tcp_accept` | `FdStream -> IO (Result StreamError FdStream)` |
| `IO.tcp_local_port` | `FdStream -> IO U16` |
| `Stream.read` | `FdStream -> I64 -> IO (Result StreamError ByteBuf)` |
| `Stream.write` | `FdStream -> ByteBuf -> IO (Result StreamError I64)` |
| `Stream.close` | `FdStream -> IO Unit` |
| `FdStream.raw_fd` | `FdStream -> IO I32` |

The payload is a `ByteBuf` from `std.bytebuf`, a flat byte buffer, not a
`List U8`. A read costs one allocation, whatever its size. Free every buffer
with `ByteBuf.free` once you are done with it. That covers both the buffers a
read hands you and the ones you build for a write.

A failure is a `StreamError`: a `kind` you can `match` on (`connection_refused`,
`address_in_use`, `host_unresolved`, ...) plus the OS's `message`.
`FdStream.raw_fd` hands the descriptor to an FFI function such as OpenSSL's
`SSL_set_fd`.

An `FdStream` is opaque. At runtime it is the bare file descriptor, so never
pattern-match, compare or print one, and never use it after `Stream.close`.

```monad
use std::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.length, ByteBuf.of_string, ByteBuf.to_string}
use std::stream {Stream, StreamError, FdStream}

/// Send one request over a fresh connection and return whatever comes back.
def fetch (host : String) (port : U16) : IO (Result String String) := do {
    let opened <- IO.tcp_connect host port;
    fetch_on opened
}

def fetch_on (opened : Result StreamError FdStream) : IO (Result String String) :=
    match opened {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok sock => fetch_over sock
    }

def fetch_over (sock : FdStream) : IO (Result String String) := do {
    let request <- ByteBuf.of_string "GET / HTTP/1.0\r\n\r\n";
    let sent <- Stream.write sock request;
    ByteBuf.free request;
    let got <- Stream.read sock 4096;
    Stream.close sock;
    fetch_reply sent got
}

def fetch_reply (sent : Result StreamError I64) (got : Result StreamError ByteBuf) : IO (Result String String) :=
    match sent {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok _ => reply_text got
    }

def reply_text (got : Result StreamError ByteBuf) : IO (Result String String) :=
    match got {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok buf => do {
            let text <- ByteBuf.to_string buf (ByteBuf.length buf);
            ByteBuf.free buf;
            return (Result.ok text)
        }
    }
```

`IO.tcp_listen 0u16` binds `0.0.0.0` on an OS-assigned port; read the port it
actually settled on back with `IO.tcp_local_port`:

```monad
use std::bytebuf {ByteBuf, ByteBuf.free}
use std::stream {Stream, StreamError, FdStream}
open IO {println}

/// Listen on an OS-assigned port, print it, accept one connection, echo back
/// what it sends, and close everything.
def echo_once : IO Unit := do {
    let bound <- IO.tcp_listen 0u16;
    match bound {
        Result.err e => println e.message,
        Result.ok listener => do {
            let port <- IO.tcp_local_port listener;
            println (U16.to_string port);
            let accepted <- IO.tcp_accept listener;
            Stream.close listener;
            echo_on accepted
        }
    }
}

def echo_on (accepted : Result StreamError FdStream) : IO Unit :=
    match accepted {
        Result.err e => println e.message,
        Result.ok conn => do {
            let got <- Stream.read conn 1024;
            echo_back conn got;
            Stream.close conn
        }
    }

def echo_back (conn : FdStream) (got : Result StreamError ByteBuf) : IO Unit :=
    match got {
        Result.err e => println e.message,
        Result.ok buf => do {
            let written <- Stream.write conn buf;
            ByteBuf.free buf;
            match written {
                Result.err e => println e.message,
                Result.ok n => println (I64.to_string n)
            }
        }
    }
```

Closing a listener closes the listening socket only. Connections already
accepted from it keep working, which is why the snippet above can close the
listener and then talk on `conn`. `Stream.write` writes *all* of the buffer it
is given. The count it returns is always the full length, never a partial one,
so you never need a write loop.

### What is not there

- **TCP is self-hosted only.** The four `tcp_*` natives are implemented by
  `runtime/src/runtime.c`, which the self-hosted backend compiles; the Rust
  bootstrap host deliberately has no TCP implementation at all, so under it any
  of these fails at run time with `unknown native: tcp_listen` (or whichever was
  called). A socket test therefore cannot run under `cargo run -- test`, and the
  `examples/` HTTP entry is pure by design for exactly that reason.
- **No read timeout, and no non-blocking mode.** `tcp_connect`, `tcp_accept` and
  `Stream.read` block until they complete. A peer that connects and then sends
  nothing holds the accepting fiber and its OS thread indefinitely; nothing in
  the library breaks that. The mitigation in `motes/moon/src/server.mo` is a cap
  on requests served per connection, which bounds an *idle keep-alive client*,
  not a silent one. A real timeout is not implemented.
- **EOF is not an error.** When the peer closes, `Stream.read` returns a
  zero-length buffer rather than failing, and read loops terminate on exactly
  that. `Stream.close` never fails.

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

IO operations bottom out in natives, implemented by the Rust host and by the
compiled backend's C runtime:

```monad,ignore
#[native "get_env"]
pub def IO.get_env (s : String) : IO (Option String)
```

The `#[native name]` attribute marks a definition as implemented outside Monad,
and such a definition has no body. The name in the attribute is the runtime's
identifier for the operation, which is not always the Monad-side name — the
native behind `IO.read_stdin_exact` is a `priv` `read_stdin_exact` returning
`RawIO String`, which the public def wraps. The same split applies to
`#[extern "c"]`: a declaration with side effects is typed `RawIO A` and
bound with `IO.mk` (the generated wrapper adds the one `RawIO.io` box),
while a pure getter keeps its raw return type. Not every IO operation is a native:
`IO.println`, `IO.write_stdout`, `IO.write_stderr`, `IO.read_line`,
`IO.read_file` and `IO.write_file` are ordinary Monad over `std/stream.mo`'s
byte streams.

There are 169 natives declared across `init/` and `std/`. Three — `eq_rec`, `string_to_chars`, and
`string_from_chars` — are declared but not implemented anywhere, and calling one
fails at run time with `unknown native`. The compiler backend wires a subset of
the rest; see [Compiling and Running](./compiling.md#native-coverage). The four
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
