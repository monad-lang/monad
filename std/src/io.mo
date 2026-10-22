// OS-specific I/O: console output, the filesystem, and TCP networking.
// The `IO` type itself lives in init/io.mo (pure, portable); everything
// here is a genuine side effect, hence std/. See AGENTS.md's "init vs
// std" section.

// Qualified (not bare `use path {...}`) deliberately: the Rust
// reference's module loader registers std/*.mo siblings under their
// full `std.<name>` path (to avoid colliding with init/io.mo's own
// bare `io`), and has no base-dir-relative fallback the way the
// self-hosted loader does -- a bare `use path {...}` here resolves
// fine self-hosted but fails "module not found: path" under `cargo
// run`. Qualified works identically on both sides.
use lib::path {Path}
use lib::bytebuf {
  ByteBuf, ByteBuf.alloc, ByteBuf.copy_into, ByteBuf.free, ByteBuf.length,
  ByteBuf.of_list, ByteBuf.of_string, ByteBuf.to_list, ByteBuf.to_string,
}
use lib::stream {
  Stream, FdStream, FdStream.open_file, FdStream.read_line_bounded,
  FdStream.read_mode, FdStream.stderr, FdStream.stdin, FdStream.stdout,
  FdStream.write_mode, PartialLinePolicy, StreamError, stream_result,
}

/// Write `s` and a newline to stdout (buffered; see `IO.flush_stdout`).
pub def IO.println (s : String) : IO Unit := IO.write_to FdStream.stdout (String.concat s "\n")

// ── Whole files ─────────────────────────────────────────────────────────
// Built on `std/stream.mo`: open, a chunked read or one write, close.
// Every failure is a `Result.err` -- a missing file is `not_found`,
// never an empty string -- and the caller decides what absence means.

/// Bytes asked for per `Stream.read` while reading a whole file.
def IO.read_chunk_size : I64 := 65536

/// Create or truncate `path` and write `content` to it. A missing parent
/// directory is `not_found`; it is not created.
pub def IO.write_file (path : Path) (content : String) : IO (Result StreamError Unit) := do {
  let opened <- FdStream.open_file path FdStream.write_mode;
  IO.write_opened opened content
}

/// Write raw bytes to `path`, truncating it. The byte counterpart of
/// `IO.write_file`; no decoding is involved.
pub def IO.write_file_bytes (path : Path) (bytes : List U8) : IO (Result StreamError Unit) := do {
  let opened <- FdStream.open_file path FdStream.write_mode;
  IO.write_bytes_opened opened bytes
}

def IO.write_bytes_opened (opened : Result StreamError FdStream) (bytes : List U8) : IO (Result StreamError Unit) :=
  match opened {
    Result.err e => IO.pure (Result.err e),
    Result.ok s => IO.write_bytes_all s bytes
  }

def IO.write_bytes_all (s : FdStream) (bytes : List U8) : IO (Result StreamError Unit) := do {
  let buf <- ByteBuf.of_list bytes;
  let r <- Stream.write s buf;
  let _ <- ByteBuf.free buf;
  let _ <- Stream.close s;
  return (IO.written r)
}

def IO.write_opened (opened : Result StreamError FdStream) (content : String) : IO (Result StreamError Unit) :=
  match opened {
    Result.err e => IO.pure (Result.err e),
    Result.ok s => IO.write_all s content
  }

def IO.write_all (s : FdStream) (content : String) : IO (Result StreamError Unit) := do {
  let buf <- ByteBuf.of_string content;
  let r <- Stream.write s buf;
  let _ <- ByteBuf.free buf;
  let _ <- Stream.close s;
  return (IO.written r)
}

def IO.written (r : Result StreamError I64) : Result StreamError Unit :=
  match r {
    Result.err e => Result.err e,
    Result.ok _ => Result.ok Unit.unit
  }

/// The whole file at `path` as text; a missing file is `not_found`.
///
/// The chunks are gathered into ONE buffer and decoded once: decoding
/// each 64 KiB chunk on its own would split a multi-byte character that
/// straddles a chunk boundary, which the interpreter's lossy UTF-8
/// decode turns into U+FFFD.
pub def IO.read_file (path : Path) : IO (Result StreamError String) := do {
  let opened <- FdStream.open_file path FdStream.read_mode;
  IO.read_opened opened
}

/// The whole file at `path` as raw bytes; a missing file is `not_found`.
/// Unlike `IO.read_file`, this never decodes, so NUL bytes and arbitrary
/// binary content survive. One chunk is returned directly; several are
/// copied into one buffer first.
pub def IO.read_file_bytes (path : Path) : IO (Result StreamError (List U8)) := do {
  let opened <- FdStream.open_file path FdStream.read_mode;
  IO.read_bytes_opened opened
}

def IO.read_bytes_opened (opened : Result StreamError FdStream) : IO (Result StreamError (List U8)) :=
  match opened {
    Result.err e => IO.pure (Result.err e),
    Result.ok s => IO.read_bytes_all s
  }

def IO.read_bytes_all (s : FdStream) : IO (Result StreamError (List U8)) := do {
  let chunks <- IO.read_chunks s List.empty;
  let _ <- Stream.close s;
  IO.read_bytes_joined chunks
}

def IO.read_bytes_joined (chunks : Result StreamError (List ByteBuf)) : IO (Result StreamError (List U8)) :=
  match chunks {
    Result.err e => IO.pure (Result.err e),
    Result.ok bufs => IO.read_bytes_flatten bufs
  }

def IO.read_bytes_flatten (bufs : List ByteBuf) : IO (Result StreamError (List U8)) :=
  match bufs {
    List.empty => IO.pure (Result.ok List.empty),
    List.cons one rest =>
      match rest {
        List.empty => IO.buf_bytes_result one,
        List.cons _ _ => IO.gather_bytes bufs
      }
  }

def IO.buf_bytes_result (b : ByteBuf) : IO (Result StreamError (List U8)) := do {
  let bytes <- ByteBuf.to_list b (ByteBuf.length b);
  let _ <- ByteBuf.free b;
  return (Result.ok bytes)
}

def IO.gather_bytes (bufs : List ByteBuf) : IO (Result StreamError (List U8)) := do {
  let dst <- ByteBuf.alloc (IO.total_length bufs);
  let _ <- IO.copy_chunks dst 0 bufs;
  IO.buf_bytes_result dst
}

def IO.read_opened (opened : Result StreamError FdStream) : IO (Result StreamError String) :=
  match opened {
    Result.err e => IO.pure (Result.err e),
    Result.ok s => IO.read_all s
  }

def IO.read_all (s : FdStream) : IO (Result StreamError String) := do {
  let chunks <- IO.read_chunks s List.empty;
  let _ <- Stream.close s;
  IO.read_joined chunks
}

def IO.read_joined (chunks : Result StreamError (List ByteBuf)) : IO (Result StreamError String) :=
  match chunks {
    Result.err e => IO.pure (Result.err e),
    Result.ok bufs => IO.read_text bufs
  }

def IO.read_text (bufs : List ByteBuf) : IO (Result StreamError String) := do {
  let text <- IO.chunks_text bufs;
  return (Result.ok text)
}

/// The chunks read so far are `acc_rev`, newest first. Every chunk is
/// freed on the error path; on success the caller owns them.
#[terminating]
def IO.read_chunks (s : FdStream) (acc_rev : List ByteBuf) : IO (Result StreamError (List ByteBuf)) := do {
  let r <- Stream.read s IO.read_chunk_size;
  IO.read_chunk_got s acc_rev r
}

#[terminating]
def IO.read_chunk_got (s : FdStream) (acc_rev : List ByteBuf) (r : Result StreamError ByteBuf) : IO (Result StreamError (List ByteBuf)) :=
  match r {
    Result.err e => IO.read_failed acc_rev e,
    Result.ok buf =>
      if ByteBuf.length buf == 0
      then IO.read_at_eof acc_rev buf
      else IO.read_chunks s (List.cons buf acc_rev)
  }

def IO.read_at_eof (acc_rev : List ByteBuf) (eof : ByteBuf) : IO (Result StreamError (List ByteBuf)) := do {
  let _ <- ByteBuf.free eof;
  return (Result.ok (List.reverse acc_rev))
}

def IO.read_failed (acc_rev : List ByteBuf) (e : StreamError) : IO (Result StreamError (List ByteBuf)) := do {
  let _ <- IO.free_all acc_rev;
  return (Result.err e)
}

#[terminating]
def IO.free_all (bufs : List ByteBuf) : IO Unit :=
  match bufs {
    List.empty => IO.pure Unit.unit,
    List.cons b rest => IO.free_then b rest
  }

#[terminating]
def IO.free_then (b : ByteBuf) (rest : List ByteBuf) : IO Unit := do {
  let _ <- ByteBuf.free b;
  IO.free_all rest
}

/// Decode `bufs` as one text, freeing each. One chunk -- every file
/// under 64 KiB -- decodes directly; more are copied into a single
/// buffer first.
def IO.chunks_text (bufs : List ByteBuf) : IO String :=
  match bufs {
    List.empty => IO.pure "",
    List.cons one rest =>
      match rest {
        List.empty => IO.buf_text one,
        List.cons _ _ => IO.gathered_text bufs
      }
  }

def IO.buf_text (b : ByteBuf) : IO String := do {
  let text <- ByteBuf.to_string b (ByteBuf.length b);
  let _ <- ByteBuf.free b;
  return text
}

def IO.gathered_text (bufs : List ByteBuf) : IO String := do {
  let dst <- ByteBuf.alloc (IO.total_length bufs);
  let _ <- IO.copy_chunks dst 0 bufs;
  IO.buf_text dst
}

#[terminating]
def IO.total_length (bufs : List ByteBuf) : I64 :=
  match bufs {
    List.empty => 0,
    List.cons b rest => ByteBuf.length b + IO.total_length rest
  }

/// Copy each of `bufs` into `dst` from `offset` on, freeing each.
#[terminating]
def IO.copy_chunks (dst : ByteBuf) (offset : I64) (bufs : List ByteBuf) : IO Unit :=
  match bufs {
    List.empty => IO.pure Unit.unit,
    List.cons b rest => IO.copy_chunk dst offset b rest
  }

#[terminating]
def IO.copy_chunk (dst : ByteBuf) (offset : I64) (b : ByteBuf) (rest : List ByteBuf) : IO Unit := do {
  let n := ByteBuf.length b;
  let _ <- ByteBuf.copy_into dst offset b;
  let _ <- ByteBuf.free b;
  IO.copy_chunks dst (offset + n) rest
}

#[native "file_exists"]
def IO.file_exists_native (path : String) : IO Bool

#[native "is_dir"]
def IO.is_dir_native (path : String) : IO Bool

// Bare entry names (not full paths), sorted, one directory level.
#[native "list_dir"]
def IO.list_dir_native (path : String) : IO (List String)

// `pub`: three motes outside `std` read the environment through this --
// `lang/src/mote.mo`'s toolchain-root discovery, `llvm/src/link.mo`'s
// build-commit override, and `build/src/store.mo`'s MONAD_TARGET_DIR --
// and the cross-mote warning was already pointing at it before the third
// arrived.
#[native "get_env"]
pub def IO.get_env (s : String) : IO (Option String)

// ── Raw stdio ───────────────────────────────────────────────────────────
// The group below is the byte-level half of stdio, over `std/stream.mo`'s
// `FdStream.stdin`/`stdout`/`stderr`: `IO.println` writes
// a line to stdout and `IO.read_file` reads a whole named file, and
// neither is usable when the process's own stdin/stdout IS the channel.
// That is the language server's situation, and it is why each of these
// exists:
//
//   - an LSP peer speaks a framed protocol over stdout (`Content-Length:
//     N\r\n\r\n<JSON>`), so a frame must go out VERBATIM -- one extra
//     newline from `println` corrupts the stream and desynchronizes the
//     peer's parser permanently;
//   - diagnostics/progress logging has to go to stderr instead, and
//     must be flushed at once (a log line is worthless if it sits in a
//     buffer until the process exits, which for a server is never);
//   - a frame's header can be split across two reads by the OS, so the
//     reader must be able to ask for "up to N bytes, as many as are
//     ready, right now" and accumulate a byte stream itself.
//
// Being a byte stream is the whole reason these are separate from the
// line- and String-oriented natives: the caller slices the accumulated
// bytes at BYTE offsets taken from `Content-Length`, so every byte has
// to arrive unaltered.

// Write `text` to `s` verbatim, discarding a write error: the stdio
// writers' type has no error channel, and a vanished stdout/stderr
// reader kills the process by SIGPIPE before an error could surface
// (`stdio_die_on_epipe`, runtime.c; the interpreter mirrors it).
pub def IO.write_to (s : FdStream) (text : String) : IO Unit := do {
  let buf <- ByteBuf.of_string text;
  let _ <- Stream.write s buf;
  ByteBuf.free buf
}

// One line from stdin, WITHOUT its trailing newline. `Result.ok
// Option.none` at EOF, meaning nothing at all was read -- a final line
// with no trailing newline is still `Option.some line`, so a caller
// reading a sequence of lines terminates on `none` rather than on an
// empty string. `\r` is
// NOT stripped (the caller wants the bytes the peer actually sent). A
// read error is a `Result.err`, distinct from end of input.
//
// One byte per read (`FdStream.read_line_bounded`), so the bytes after
// the line stay in the kernel for the caller's next `read_stdin_exact`
// or `poll(2)` -- a reader that read ahead would desynchronize both.
pub def IO.read_line : IO (Result StreamError (Option String)) :=
  FdStream.read_line_bounded FdStream.stdin 0 PartialLinePolicy.deliver

#[native "read_stdin_exact"]
priv def read_stdin_exact (n : I64) : RawIO String

// Blocking read of UP TO `n` bytes from stdin, returning exactly the
// bytes read. A result SHORTER than `n` -- including "" -- means EOF;
// `n <= 0` returns "". Bytes, not characters: see this group's own
// comment, the caller accumulates the result and slices it at byte
// offsets, so a chunk may end in the middle of a multi-byte UTF-8
// character and must still be handed over unaltered.
pub def IO.read_stdin_exact (n : I64) : IO String := IO.mk (read_stdin_exact n)

// Write `s` to stdout VERBATIM -- no trailing newline, which is the
// whole difference from `IO.println`. No flush either: a protocol
// writer batches a frame's pieces and calls `IO.flush_stdout` once the
// frame is complete.
pub def IO.write_stdout (s : String) : IO Unit := IO.write_to FdStream.stdout s

#[native "flush_stdout"]
priv def flush_stdout : RawIO Unit

// Flush stdout. Needed because stdout is block-buffered when it is a
// pipe (which is how a language server's peer reads it), so a written
// frame stays invisible to the peer until this runs. The one stdio
// operation the stream primitives cannot express.
pub def IO.flush_stdout : IO Unit := IO.mk flush_stdout

// Write `s` to stderr verbatim, no trailing newline, flushed at once:
// a log line must not sit in a buffer, and it must never interleave
// into the protocol stream on fd 1.
pub def IO.write_stderr (s : String) : IO Unit := IO.write_to FdStream.stderr s

// Milliseconds since the Unix epoch, from the system WALL clock
// (`SystemTime::now`, core/src/core_native.rs). Use it for differences
// between two readings; because it is the wall clock and not a
// monotonic one, a clock adjustment (NTP, a manual set, a suspend) can
// make a later reading SMALLER than an earlier one, so a computed
// interval can come out negative -- callers that render a duration
// must handle that (`fmt_dur_ns`, lang/codegen/test_driver.mo, clamps
// it to zero).
//
// TODO: back this with a genuinely monotonic source
// (`Instant`/`CLOCK_MONOTONIC`), which is what an interval timer
// actually wants; the epoch-based reading would then move to a
// separate `IO.current_time_epoch` for the callers that want a real
// timestamp. Documented as the wall clock rather than quietly changed
// because the two natives must agree across BOTH runtimes at once.
//
// `IO` because reading a clock is a side effect in the same sense
// reading a file is: two calls in one expression may legitimately differ,
// so it must not be something the evaluator can duplicate, reorder or
// share. `std/bench.mo`'s `Bench.now` is the name callers use.
#[native current_time]
pub def IO.current_time : IO I64

// Nanoseconds since the Unix epoch, from the same system WALL clock as
// `IO.current_time` above -- same caveats (a backwards clock step can
// make an interval negative), just finer.
//
// Exists because per-test timing needs sub-millisecond resolution: the
// self-hosted test runner reports each test's duration the way the Rust
// runner's `format_duration` does (`core/src/lib.rs`), and most tests
// finish well inside one millisecond, where `current_time` can only
// ever say "0ms". The native hands over RAW NANOSECONDS and nothing
// else -- every unit conversion and all the ns/us/ms/s formatting is
// done in Monad, by the driver this runner synthesizes
// (`lang/codegen/test_driver.mo`).
#[native current_time_nano]
pub def IO.current_time_nano : IO I64

pub def IO.file_exists (path : Path) : IO Bool :=
    IO.file_exists_native (Path.to_string path)

pub def IO.is_dir (path : Path) : IO Bool :=
    IO.is_dir_native (Path.to_string path)

/// The entries of the directory `path`, one level, sorted, each joined
/// onto `path` (`Path.file_name` gives the bare name back).
pub def IO.list_dir (path : Path) : IO (List Path) := do {
    let names <- IO.list_dir_native (Path.to_string path);
    return (List.map (fn (name : String) => Path.join path (Path.path name)) names)
}

// ── TCP networking ──────────────────────────────────────────────────────
// Four blocking `#[native "tcp_*"]` defs, implemented ONLY by the
// self-hosted backend (`runtime/src/runtime.c`); the Rust evaluator
// deliberately has no TCP implementation, so a second one cannot drift
// away from this one.  These declarations are therefore the contract,
// and `slow_tests/src/codegen_wired_natives_e2e_tests.mo` is what holds
// the implementation to it:
//
//   tcp_connect      blocking; the host is resolved with `getaddrinfo`
//                    (so a name works, not just a literal address) and
//                    each address it returns is tried in turn; a name
//                    that does not resolve is `host_unresolved`
//   tcp_listen       binds `0.0.0.0:port`; port `0u16` asks the OS for
//                    one, read it back with `tcp_local_port`
//   tcp_accept       blocking; the stream is a NEW connection
//   tcp_local_port   the port the listener actually bound; a failure
//                    returns 0 (the type has no `Result` channel)
//
// Connections AND listeners are `FdStream`s (std/stream.mo): read, write
// and close them with `Stream.read`/`write`/`close` -- end of stream is
// a zero-length buffer, a write writes everything -- and take the raw
// descriptor for an FFI call (`SSL_set_fd` in motes/tls) with
// `FdStream.raw_fd`. Reading or writing a listener is a runtime
// `invalid_input`, not a type error.

#[native "tcp_connect"]
priv def tcp_connect (host : String) (port : U16) : RawIO (Result (Pair I64 String) FdStream)

#[native "tcp_listen"]
priv def tcp_listen (port : U16) : RawIO (Result (Pair I64 String) FdStream)

#[native "tcp_listen_on"]
priv def tcp_listen_on (host : String) (port : U16) : RawIO (Result (Pair I64 String) FdStream)

#[native "tcp_accept"]
priv def tcp_accept (listener : FdStream) : RawIO (Result (Pair I64 String) FdStream)

#[native "tcp_local_port"]
priv def tcp_local_port (listener : FdStream) : RawIO U16

pub def IO.tcp_connect (host : String) (port : U16) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (tcp_connect host port);
  return (stream_result r)
}

pub def IO.tcp_listen (port : U16) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (tcp_listen port);
  return (stream_result r)
}

/// Listen on a specific host address or name (`"127.0.0.1"`, `"localhost"`,
/// `""` for the wildcard) instead of always `0.0.0.0`.
pub def IO.tcp_listen_on (host : String) (port : U16) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (tcp_listen_on host port);
  return (stream_result r)
}

pub def IO.tcp_accept (listener : FdStream) : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (tcp_accept listener);
  return (stream_result r)
}

pub def IO.tcp_local_port (listener : FdStream) : IO U16 := IO.mk (tcp_local_port listener)

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
