//! `std/io.mo`'s stdin readers, interpreted, against a real fd 0: the
//! io-streams plan's Phase 3 gate (`plans/implementations/io-streams.md`).
//! `IO.read_line` is `FdStream.read_line_bounded` over slot 0 now, one
//! 1-byte `stream_read` per byte, so these pin what the old native
//! guaranteed: it never reads past the line (LSP framing mixes it with
//! `read_stdin_exact`; tui polls fd 0 after it), and it frees every
//! buffer it reads.
//!
//! ONE `#[test]`, in its own test binary: each case points the process's
//! fd 0 at a pipe, which no concurrently running test may share.
//! `slow_tests/src/stdio_stdin_e2e_tests.mo` runs the same programs
//! compiled.

use std::io::Write;
use std::os::fd::FromRawFd;

/// Run `source` with fd 0 reading what `feed` writes, and return its
/// exit code. `feed` runs on its own thread, so it may keep the pipe open
/// (sleep) while the program polls.
fn run_with_stdin(
  name: &str,
  source: &str,
  feed: impl FnOnce(std::fs::File) + Send + 'static,
) -> i64 {
  let dir = std::env::temp_dir().join(format!("monad_stdio_{}_{name}", std::process::id()));
  std::fs::create_dir_all(&dir).unwrap();
  let path = dir.join(format!("{name}.mo"));
  std::fs::write(&path, source).unwrap();

  let mut fds = [0 as libc::c_int; 2];
  assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
  let saved = unsafe { libc::dup(0) };
  assert!(saved >= 0);
  assert_eq!(unsafe { libc::dup2(fds[0], 0) }, 0);
  unsafe { libc::close(fds[0]) };
  let writer = unsafe { std::fs::File::from_raw_fd(fds[1]) };
  let feeder = std::thread::spawn(move || feed(writer));

  let code = monad_core::run(path, Vec::new(), Default::default(), Vec::new());

  feeder.join().unwrap();
  assert_eq!(unsafe { libc::dup2(saved, 0) }, 0);
  unsafe { libc::close(saved) };
  let _ = std::fs::remove_dir_all(&dir);
  code.unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn feed_bytes(bytes: &'static [u8]) -> impl FnOnce(std::fs::File) + Send + 'static {
  move |mut w| w.write_all(bytes).unwrap()
}

/// LSP framing: `read_line` header lines, then a `read_stdin_exact` body,
/// then more lines -- every byte lands with the reader that asked.
const FRAMING: &str = r#"
def is_line (o : Option String) (s : String) : Bool :=
  match o {
    Option.some l => String.beq l s,
    Option.none => false
  }

def is_none (o : Option String) : Bool :=
  match o {
    Option.some _ => false,
    Option.none => true
  }

def main (args : List String) : IO I64 := do {
  let h1 <- IO.read_line;
  let h2 <- IO.read_line;
  let body <- IO.read_stdin_exact 5;
  let after <- IO.read_line;
  let last <- IO.read_line;
  let eof <- IO.read_line;
  let ok := is_line h1 "Content-Length: 5\r" && is_line h2 "\r" && String.beq body "hello"
    && is_line after "XYZ" && is_line last "last" && is_none eof;
  return (if ok then 7 else 1)
}
"#;

/// tui's shape: read a line, one raw byte, then poll fd 0 while the
/// writer is still open -- the rest of the escape sequence must still be
/// in the kernel, not in a reader's buffer.
const POLL: &str = r#"
#[native "term_ctl"]
priv def term_ctl (op : I64) (arg : I64) : RawIO I64

def is_line (o : Option String) (s : String) : Bool :=
  match o {
    Option.some l => String.beq l s,
    Option.none => false
  }

def main (args : List String) : IO I64 := do {
  let line <- IO.read_line;
  let esc <- IO.read_stdin_exact 1;
  let ready <- IO.mk (term_ctl 3 0);
  let rest <- IO.read_stdin_exact 2;
  let ok := is_line line "ab" && String.length esc == 1 && ready == 1 && String.beq rest "[A";
  return (if ok then 7 else 1)
}
"#;

/// 10k lines through `IO.read_line`, counted.
const MANY_LINES: &str = r#"
#[terminating]
def count_lines (n : I64) : IO I64 := do {
  let line <- IO.read_line;
  count_from n line
}

#[terminating]
def count_from (n : I64) (line : Option String) : IO I64 :=
  match line {
    Option.some _ => count_lines (n + 1),
    Option.none => IO.pure n
  }

def main (args : List String) : IO I64 := do {
  let n <- count_lines 0;
  return (if n == 10000 then 7 else 1)
}
"#;

#[test]
fn stdin_readers_against_a_real_fd_0() {
  assert_eq!(
    run_with_stdin(
      "framing",
      FRAMING,
      feed_bytes(b"Content-Length: 5\r\n\r\nhelloXYZ\nlast")
    ),
    7,
    "framing"
  );

  assert_eq!(
    run_with_stdin("poll", POLL, |mut w| {
      w.write_all(b"ab\n\x1b[A").unwrap();
      // Held open past the program's poll: EOF would read as "ready".
      std::thread::sleep(std::time::Duration::from_secs(2));
    }),
    7,
    "read 1, then poll"
  );

  let lines: String = (1..=10000).map(|i| format!("{i}\n")).collect();
  let before = monad_core::runtime::global::live_count();
  assert_eq!(
    run_with_stdin("many_lines", MANY_LINES, move |mut w| {
      w.write_all(lines.as_bytes()).unwrap()
    }),
    7,
    "10k lines"
  );
  assert_eq!(
    monad_core::runtime::global::live_count(),
    before,
    "IO.read_line leaked ByteBuf registry slots"
  );
}
