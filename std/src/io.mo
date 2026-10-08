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

#[native print_str]
pub def IO.println (s: String) : IO Unit

#[native "write_file"]
def IO.write_file_native (path : String) (content : String) : IO Unit

// TODO Return Option and none on failure
#[native "read_file"]
def IO.read_file_native (path : String) : IO String

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
// The five below are the byte-level half of stdio: `IO.println` writes
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

// One line from stdin, WITHOUT its trailing newline. `Option.none` at
// EOF, meaning nothing at all was read -- a final line with no trailing
// newline is still `Option.some line`, so a caller reading a sequence of
// lines terminates on `none` rather than on an empty string. `\r` is
// NOT stripped (the caller wants the bytes the peer actually sent).
#[native "read_line"]
pub def IO.read_line : IO (Option String)

// Blocking read of UP TO `n` bytes from stdin, returning exactly the
// bytes read. A result SHORTER than `n` -- including "" -- means EOF;
// `n <= 0` returns "". Bytes, not characters: see this group's own
// comment, the caller accumulates the result and slices it at byte
// offsets, so a chunk may end in the middle of a multi-byte UTF-8
// character and must still be handed over unaltered.
#[native "read_stdin_exact"]
pub def IO.read_stdin_exact (n : I64) : IO String

// Write `s` to stdout VERBATIM -- no trailing newline, which is the
// whole difference from `IO.println`. No flush either: a protocol
// writer batches a frame's pieces and calls `IO.flush_stdout` once the
// frame is complete.
#[native "write_stdout"]
pub def IO.write_stdout (s : String) : IO Unit

// Flush stdout. Needed because stdout is block-buffered when it is a
// pipe (which is how a language server's peer reads it), so a written
// frame stays invisible to the peer until this runs.
#[native "flush_stdout"]
pub def IO.flush_stdout : IO Unit

// Write `s` to stderr verbatim, no trailing newline, and flush it. A
// separate native from `IO.write_stdout` for more than the stream it
// names: a log line must not sit in a buffer, and it must never
// interleave into the protocol stream on fd 1.
#[native "write_stderr"]
pub def IO.write_stderr (s : String) : IO Unit

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
def IO.current_time : IO I64

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
def IO.current_time_nano : IO I64

pub def IO.write_file (path : Path) (content : String) : IO Unit :=
    IO.write_file_native (Path.to_string path) content

pub def IO.read_file (path : Path) : IO String :=
    IO.read_file_native (Path.to_string path)

pub def IO.file_exists (path : Path) : IO Bool :=
    IO.file_exists_native (Path.to_string path)

pub def IO.is_dir (path : Path) : IO Bool :=
    IO.is_dir_native (Path.to_string path)

pub def IO.list_dir (path : Path) : IO (List String) :=
    IO.list_dir_native (Path.to_string path)

// ── TCP networking ──────────────────────────────────────────────────────
// Eight blocking `#[native "tcp_*"]` defs, implemented ONLY by the
// self-hosted backend (`runtime/src/runtime.c`); the Rust evaluator
// deliberately has no TCP implementation, so a second one cannot drift
// away from this one.  These declarations are therefore the contract,
// and `slow_tests/src/codegen_wired_natives_e2e_tests.mo` is what holds
// the implementation to it:
//
//   tcp_connect      blocking; the host is resolved with `getaddrinfo`
//                    (so a name works, not just a literal address) and
//                    each address it returns is tried in turn
//   tcp_listen       binds `0.0.0.0:port`; port `0u16` asks the OS for
//                    one, read it back with `tcp_local_port`
//   tcp_accept       blocking; the `Socket` is a NEW connection
//   tcp_read         blocking, at most `max_bytes`; EOF (the peer
//                    closed) is `Result.ok List.empty`, NOT an error —
//                    read loops terminate on exactly that
//   tcp_write        writes ALL of `data`; the ok payload is the full
//                    length, not the last partial count
//   tcp_close        never fails; closing a listener does not touch
//   tcp_close_listener  connections already accepted from it
//   tcp_local_port   the port the listener actually bound; a failure
//                    returns 0 (the type has no `Result` channel)
//   tcp_fd           the connection's raw descriptor, for FFI calls that
//                    take one (`SSL_set_fd` in motes/tls); the Socket IS
//                    the fd, so this is typed extraction, not a lookup
//
// `Socket` and `Listener` are opaque: their single zero-arity
// constructor exists only so the type checker has a type to name, and
// the runtime value is never one of them.  Nothing may pattern-match,
// compare or print these — that is what lets the implementation carry a
// bare file descriptor instead of a handle.

type Socket {
  socket
}

type Listener {
  listener
}

#[native "tcp_connect"]
def IO.tcp_connect (host : String) (port : U16) : IO (Result String Socket)

#[native "tcp_listen"]
def IO.tcp_listen (port : U16) : IO (Result String Listener)

#[native "tcp_accept"]
def IO.tcp_accept (listener : Listener) : IO (Result String Socket)

#[native "tcp_read"]
def IO.tcp_read (sock : Socket) (max_bytes : U64) : IO (Result String (List U8))

#[native "tcp_write"]
def IO.tcp_write (sock : Socket) (data : List U8) : IO (Result String U64)

#[native "tcp_close"]
def IO.tcp_close (sock : Socket) : IO Unit

#[native "tcp_close_listener"]
def IO.tcp_close_listener (listener : Listener) : IO Unit

#[native "tcp_local_port"]
def IO.tcp_local_port (listener : Listener) : IO U16

#[native "tcp_fd"]
def IO.tcp_fd (sock : Socket) : IO I32

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
