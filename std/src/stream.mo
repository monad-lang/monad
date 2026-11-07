/// Standard library: byte streams -- one read/write/close surface over
/// every file-descriptor-backed channel (stdio, an open file, and in
/// later phases a TCP connection and a child-process pipe), with a
/// `ByteBuf` payload and a structured `StreamError`
/// (`plans/implementations/io-streams.md`).
///
/// Every `ByteBuf` a `Stream.read` hands back must be released with
/// `ByteBuf.free` exactly once after it is consumed, and so must every
/// buffer built for a `Stream.write`. Compiled, `free` is a no-op;
/// interpreted, a missing one leaks a registry slot for the life of the
/// process.

use lib::bytebuf {ByteBuf}
use lib::path {Path}

// ─── StreamError ────────────────────────────────────────────────────────

/// What kind of failure a stream operation hit. Not exhaustive: `other`
/// is the escape valve, and `StreamError.message` always carries the OS
/// text.
///
/// The DECLARATION ORDER is the natives' kind code (0 = `not_found` ..
/// 9 = `other`): `stream_error_kind_of_errno` (runtime/src/runtime.c)
/// and `stream_error_code` (rust/core/src/core_native.rs) produce it, and
/// `StreamError.kinds` below decodes it. Keep all four in lock-step.
pub type StreamErrorKind {
  not_found,
  permission_denied,
  connection_refused,
  connection_reset,
  broken_pipe,
  invalid_input,
  timed_out,
  address_in_use,
  host_unresolved,
  other
}

pub struct StreamError {
  kind : StreamErrorKind,
  message : String
}

/// A kind is a plain tag and a `StreamError` is a tag plus a `Copy`
/// `String`, so sharing one is a bit-copy, not an ownership move.
pub instance Copy StreamErrorKind {
  def copy (k : StreamErrorKind) : Pair StreamErrorKind StreamErrorKind :=
    Pair.pair k k
}

pub instance Copy StreamError {
  def copy (e : StreamError) : Pair StreamError StreamError := Pair.pair e e
}

/// `StreamErrorKind` in declaration order, so a kind code IS an index.
/// A table rather than an `if` ladder: there are no integer patterns.
def StreamError.kinds : List StreamErrorKind :=
  [StreamErrorKind.not_found, StreamErrorKind.permission_denied,
   StreamErrorKind.connection_refused, StreamErrorKind.connection_reset,
   StreamErrorKind.broken_pipe, StreamErrorKind.invalid_input,
   StreamErrorKind.timed_out, StreamErrorKind.address_in_use,
   StreamErrorKind.host_unresolved, StreamErrorKind.other]

/// A native's kind code as the kind; anything out of range is `other`.
pub def StreamError.kind_of_code (code : I64) : StreamErrorKind :=
  match List.get code StreamError.kinds {
    Option.some kind => kind,
    Option.none => StreamErrorKind.other
  }

pub def StreamError.of (kind : StreamErrorKind) (message : String) : StreamError :=
  let e : StreamError := { kind := kind, message := message } in e

/// Whether `e` is `not_found` -- the one kind a caller may read as
/// "absent" (an optional file) rather than as a failure.
pub def StreamError.is_not_found (e : StreamError) : Bool :=
  match e.kind {
    StreamErrorKind.not_found => true,
    _ => false
  }

/// Natives cannot build a `StreamErrorKind` -- its constructor tags are
/// per-program, unlike `Result`'s and `Pair`'s fixed ones -- so they
/// report `Pair.pair <kind code> <message>` and every wrapper passes the
/// result through this exactly once.
def stream_result {A : Type} (r : Result (Pair I64 String) A) : Result StreamError A :=
  match r {
    Result.ok a => Result.ok a,
    Result.err raw => Result.err (stream_error_of_raw raw)
  }

def stream_error_of_raw (raw : Pair I64 String) : StreamError :=
  match raw {
    Pair.pair code message => StreamError.of (StreamError.kind_of_code code) message
  }

// ─── The Stream class ───────────────────────────────────────────────────

/// A byte stream. `read` of a zero-length buffer is END OF STREAM, never
/// an error; `write` writes ALL of the buffer and reports its full
/// length; `close` never fails.
pub class Stream S {
  def read (s : S) (max_bytes : I64) : IO (Result StreamError ByteBuf)
  def write (s : S) (buf : ByteBuf) : IO (Result StreamError I64)
  def close (s : S) : IO Unit
}

// ─── FdStream ───────────────────────────────────────────────────────────

/// A stream over one file descriptor. Opaque, like `Child`: compiled,
/// the value IS the descriptor; interpreted, it is a slot in the
/// evaluator's stream registry whose slots 0/1/2 are stdio. The
/// constructor is never built -- never pattern-match, compare or print
/// one.
///
/// Never use an `FdStream` after `Stream.close`: the same value may
/// already name a LATER stream (the OS reuses the descriptor number
/// compiled, the registry reuses the slot interpreted), so a stale
/// read or write lands on someone else's file.
pub type FdStream {
  fdstream
}

#[native "stream_open"]
priv def stream_open (path : String) (mode : I64) : RawIO (Result (Pair I64 String) FdStream)

#[native "stream_read"]
priv def stream_read (s : FdStream) (max_bytes : I64) : RawIO (Result (Pair I64 String) ByteBuf)

#[native "stream_write"]
priv def stream_write (s : FdStream) (buf : ByteBuf) : RawIO (Result (Pair I64 String) I64)

#[native "stream_close"]
priv def stream_close (s : FdStream) : RawIO Unit

#[native "stream_fd"]
priv def stream_fd (s : FdStream) : RawIO I32

/// `lseek(2)`: `whence` 0 from the start, 1 from the current offset, 2
/// from the end; the ok payload is the new offset. Bytes a line read
/// carried past its newline are dropped, since they belong to the old
/// position.
#[native "stream_seek"]
priv def stream_seek (s : FdStream) (offset : I64) (whence : I64) : RawIO (Result (Pair I64 String) I64)

#[native "stream_poll"]
priv def stream_poll (s : FdStream) (events : I64) (timeout_ms : I64) : RawIO (Result (Pair I64 String) I64)

#[native "stream_set_timeout"]
priv def stream_set_timeout (s : FdStream) (recv_ms : I64) (send_ms : I64) : RawIO (Result (Pair I64 String) Unit)

/// Pure: naming one of the three standard descriptors is not an effect.
#[native "std_fd"]
priv def std_fd (which : I64) : FdStream

pub instance Stream FdStream {
  def read (s : FdStream) (max_bytes : I64) : IO (Result StreamError ByteBuf) := do {
    let r <- IO.mk (stream_read s max_bytes);
    return (stream_result r)
  }
  def write (s : FdStream) (buf : ByteBuf) : IO (Result StreamError I64) := do {
    let r <- IO.mk (stream_write s buf);
    return (stream_result r)
  }
  def close (s : FdStream) : IO Unit := IO.mk (stream_close s)
}

/// `FdStream.open_file`'s modes.
pub def FdStream.read_mode : I64 := 0
/// Create or truncate.
pub def FdStream.write_mode : I64 := 1
/// Create or append (every write lands at the end).
pub def FdStream.append_mode : I64 := 2

/// Open `path` for reading (`FdStream.read_mode`), writing
/// (`FdStream.write_mode`: created 0644, or truncated) or appending
/// (`FdStream.append_mode`).
pub def FdStream.open_file (path : Path) (mode : I64) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (stream_open (Path.to_string path) mode);
  return (stream_result r)
}

/// The raw descriptor, for FFI calls that take one (`SSL_set_fd`).
pub def FdStream.raw_fd (s : FdStream) : IO I32 := IO.mk (stream_fd s)

/// Adopt a raw descriptor an FFI call handed back (a pty master).
///
/// COMPILED ONLY: compiled, an `FdStream` IS the descriptor; interpreted, it
/// is a slot in the evaluator's stream registry, so adopting an arbitrary
/// descriptor would alias a stranger. Callers must pass a descriptor the OS
/// just produced for them (`forkpty`'s master), and a test harness that uses
/// this is self-hosted/LLVM-only by construction.
pub def FdStream.of_raw_fd (fd : I32) : FdStream := std_fd (I32.to_i64 fd)

/// `FdStream.poll`'s readiness bits (`poll(2)`'s POLLIN/POLLOUT).
pub def FdStream.poll_read : I64 := 1
pub def FdStream.poll_write : I64 := 2

/// Wait up to `timeout_ms` for readiness: `ok true` ready, `ok false`
/// timed out. The deadline belongs to the caller; this is one wait, not
/// a loop.
pub def FdStream.poll (s : FdStream) (events : I64) (timeout_ms : I64) : IO (Result StreamError Bool) := do {
  let r <- IO.mk (stream_poll s events timeout_ms);
  return (match stream_result r {
    Result.err e => Result.err e,
    Result.ok n => Result.ok (Bool.not (I64.beq n 0)),
  })
}

/// `FdStream.seek`'s origins (`lseek(2)`'s SEEK_SET/SEEK_CUR/SEEK_END).
pub def FdStream.seek_start : I64 := 0
pub def FdStream.seek_current : I64 := 1
pub def FdStream.seek_end : I64 := 2

/// Move the stream's offset to `offset` bytes from `whence` and return
/// the new offset from the start. Only a file seeks; a pipe, socket or
/// terminal is an error. `seek 0 seek_end` is the file's size.
pub def FdStream.seek (s : FdStream) (offset : I64) (whence : I64) : IO (Result StreamError I64) := do {
  let r <- IO.mk (stream_seek s offset whence);
  return (stream_result r)
}

/// A socket's per-read and per-write timeout (`SO_RCVTIMEO`/`SO_SNDTIMEO`).
/// A read or write that exceeds it fails with `timed_out`. Only sockets
/// accept this; a file descriptor is `invalid_input`. A write that hits
/// the bound may already have sent a PREFIX of its buffer: that stream
/// is not resumable (a retry would duplicate the prefix), so abandon the
/// connection rather than retry.
pub def FdStream.set_timeout (s : FdStream) (recv_ms : I64) (send_ms : I64) : IO (Result StreamError Unit) := do {
  let r <- IO.mk (stream_set_timeout s recv_ms send_ms);
  return (stream_result r)
}

/// Writes to stdout go through the C runtime's stdio buffer (Rust's
/// `Stdout` when interpreted) -- `IO.println` and `IO.write_stdout` are
/// exactly such writes -- and `IO.flush_stdout` flushes them.
pub def FdStream.stdin : FdStream := std_fd 0
pub def FdStream.stdout : FdStream := std_fd 1
/// Written unbuffered -- a log line must not wait for a flush.
pub def FdStream.stderr : FdStream := std_fd 2

// ─── Line reading ───────────────────────────────────────────────────────

/// What a line reader does with a final line cut off by end of stream
/// rather than by `\n`.
pub type PartialLinePolicy {
  /// Hand it over anyway (stdin's historical policy).
  deliver,
  /// Drop it: on a protocol pipe a frame without its terminator is a
  /// truncated message, not a message.
  discard
}

/// A two-way tag: sharing one is a register move.
pub instance Copy PartialLinePolicy {
  def copy (p : PartialLinePolicy) : Pair PartialLinePolicy PartialLinePolicy :=
    Pair.pair p p
}

/// `PartialLinePolicy` as the native's flag: 0 = deliver, 1 = discard.
def PartialLinePolicy.discard_flag (policy : PartialLinePolicy) : I64 :=
  match policy {
    PartialLinePolicy.deliver => 0,
    PartialLinePolicy.discard => 1
  }

/// `stream_read_line : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
/// String) (Option String))` -- one line WITHOUT its `\n` (a `\r`
/// stays), `Option.none` at end of stream or when `discard` (the third
/// argument) drops a partial line, and `invalid_input` when the content
/// exceeds `max_len` bytes (`max_len <= 0` is unbounded).
///
/// A NATIVE rather than the per-byte Monad recursion Phases 1-3 used:
/// that loop consumed one Rust/machine stack frame per byte, so a line of
/// a few thousand bytes overflowed the interpreter and a few hundred
/// kilobytes overflowed a compiled binary -- both far below the one
/// mebibyte bound the shell tool relies on. Reading in chunks also needs
/// the bytes after the newline kept for the next call, so the runtime
/// holds a per-stream carry (and the interpreter's stdin carry is the
/// same one `read_stdin_exact` drains), which no `.mo` code could hold --
/// `std` has no mutable cell.
#[native "stream_read_line"]
priv def stream_read_line (s : FdStream) (max_len : I64) (discard : I64) : RawIO (Result (Pair I64 String) (Option String))

/// One line from `s`, WITHOUT its `\n` (a `\r` stays). `Result.ok
/// Option.none` at end of stream. A line longer than `max_len` bytes is
/// `invalid_input`; `max_len <= 0` means unbounded.
///
/// Specialised to `FdStream` rather than generic over `[Stream S]`: the
/// self-hosted backend miscompiles a constrained generic's dictionary
/// call (plans/implementations/2026-10-18-compiled-constrained-generic-
/// dict-call-miscompiles.md) -- the generic version segfaulted compiled
/// while passing interpreted. Go back to `[Stream S]` once that is fixed.
pub def FdStream.read_line_bounded (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) : IO (Result StreamError (Option String)) := do {
  let r <- IO.mk (stream_read_line s max_len (PartialLinePolicy.discard_flag policy));
  return (stream_result r)
}
