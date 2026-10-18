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

use lib::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.to_list}

// ─── StreamError ────────────────────────────────────────────────────────

/// What kind of failure a stream operation hit. Not exhaustive: `other`
/// is the escape valve, and `StreamError.message` always carries the OS
/// text.
///
/// The DECLARATION ORDER is the natives' kind code (0 = `not_found` ..
/// 9 = `other`): `stream_error_kind_of_errno` (runtime/src/runtime.c)
/// and `stream_error_code` (core/src/core_native.rs) produce it, and
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
class Stream S {
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

/// Pure: naming one of the three standard descriptors is not an effect.
#[native "std_fd"]
priv def std_fd (which : I64) : FdStream

instance Stream FdStream {
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

/// Open `path` for reading (`FdStream.read_mode`) or writing
/// (`FdStream.write_mode`: created 0644, or truncated).
pub def FdStream.open_file (path : String) (mode : I64) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (stream_open path mode);
  return (stream_result r)
}

/// The raw descriptor, for FFI calls that take one (`SSL_set_fd`).
pub def FdStream.raw_fd (s : FdStream) : IO I32 := IO.mk (stream_fd s)

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

/// One line from `s`, WITHOUT its `\n` (a `\r` stays). `Result.ok
/// Option.none` at end of stream. A line longer than `max_len` bytes is
/// `invalid_input`; `max_len <= 0` means unbounded.
///
/// Specialised to `FdStream` rather than generic over `[Stream S]`: the
/// self-hosted backend miscompiles a constrained generic's dictionary
/// call (plans/implementations/2026-10-18-compiled-constrained-generic-
/// dict-call-miscompiles.md) -- the generic version segfaulted compiled
/// while passing interpreted. Go back to `[Stream S]` once that is fixed.
///
/// One byte per read, deliberately: a reader that read ahead would have
/// to keep the extra bytes for the NEXT call, and a caller like
/// `IO.read_line` has no state to keep them in -- one byte at a time
/// leaves the stream exactly where the next reader expects it.
pub def FdStream.read_line_bounded (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) : IO (Result StreamError (Option String)) :=
  stream_line_go s max_len policy List.empty 0

#[terminating]
def stream_line_go (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) : IO (Result StreamError (Option String)) := do {
  let r <- Stream.read s 1;
  stream_line_got s max_len policy acc_rev n r
}

#[terminating]
def stream_line_got (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) (r : Result StreamError ByteBuf) : IO (Result StreamError (Option String)) :=
  match r {
    Result.err e => IO.pure (Result.err e),
    Result.ok buf => stream_line_buf s max_len policy acc_rev n buf
  }

#[terminating]
def stream_line_buf (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) (buf : ByteBuf) : IO (Result StreamError (Option String)) := do {
  let bytes <- ByteBuf.to_list buf 1;
  let _ <- ByteBuf.free buf;
  stream_line_bytes s max_len policy acc_rev n bytes
}

#[terminating]
def stream_line_bytes (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) (bytes : List U8) : IO (Result StreamError (Option String)) :=
  match bytes {
    List.empty => IO.pure (stream_line_at_eof policy acc_rev n),
    List.cons b _ => stream_line_byte s max_len policy acc_rev n b
  }

#[terminating]
def stream_line_byte (s : FdStream) (max_len : I64) (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) (b : U8) : IO (Result StreamError (Option String)) :=
  if U8.beq b 10u8
  then IO.pure (Result.ok (Option.some (String.from_list (List.reverse acc_rev))))
  else if max_len > 0 && Bool.not (n < max_len)
  then IO.pure (Result.err (StreamError.of StreamErrorKind.invalid_input (String.concat "line longer than " (String.concat (I64.to_string max_len) " bytes"))))
  else stream_line_go s max_len policy (List.cons b acc_rev) (n + 1)

/// End of stream with `n` bytes of an unterminated line in hand.
def stream_line_at_eof (policy : PartialLinePolicy) (acc_rev : List U8) (n : I64) : Result StreamError (Option String) :=
  match policy {
    PartialLinePolicy.discard => Result.ok Option.none,
    PartialLinePolicy.deliver =>
      if n == 0
      then Result.ok Option.none
      else Result.ok (Option.some (String.from_list (List.reverse acc_rev)))
  }
