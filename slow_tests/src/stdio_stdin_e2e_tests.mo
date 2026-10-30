/// `std/io.mo`'s stdin readers, compiled, against a real piped stdin:
/// the io-streams plan's Phase 3 gate. `IO.read_line` is
/// `FdStream.read_line_bounded` over fd 0 now -- one 1-byte read per
/// byte -- so these pin that it never reads past the line: LSP framing
/// mixes it with `read_stdin_exact`, and tui polls fd 0 after it.
/// `rust/core/tests/stdio_stdin_test.rs` runs the same programs interpreted
/// (and checks the 10k-line one leaks no ByteBuf slots).
use lang::codegen::test::e2e_harness {compile_source_run_stdin_expect}

/// `read_line` header lines, a `read_stdin_exact` body, more lines:
/// every byte lands with the reader that asked.
#[test]
def test_read_line_and_read_stdin_exact_share_the_stream : IO Bool :=
    let source := r#"use std::stream {StreamError}

def is_line (r : Result StreamError (Option String)) (s : String) : Bool :=
  match r {
    Result.ok o => line_is o s,
    Result.err _ => false
  }

def line_is (o : Option String) (s : String) : Bool :=
  match o {
    Option.some l => String.beq l s,
    Option.none => false
  }

def is_none (r : Result StreamError (Option String)) : Bool :=
  match r {
    Result.ok o => opt_none o,
    Result.err _ => false
  }

def opt_none (o : Option String) : Bool :=
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
"# in
    compile_source_run_stdin_expect source "stdio_framing" "printf 'Content-Length: 5\\r\\n\\r\\nhelloXYZ\\nlast'" 7

/// tui's shape: a line, one raw byte, then a poll of fd 0 while the
/// writer is still open -- the rest of the escape sequence must still be
/// in the kernel, not in a reader's buffer.
#[test]
def test_read_line_leaves_the_rest_pollable : IO Bool :=
    let source := r#"use std::stream {StreamError}

#[native "term_ctl"]
priv def term_ctl (op : I64) (arg : I64) : RawIO I64

def is_line (r : Result StreamError (Option String)) (s : String) : Bool :=
  match r {
    Result.ok o => line_is o s,
    Result.err _ => false
  }

def line_is (o : Option String) (s : String) : Bool :=
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
"# in
    compile_source_run_stdin_expect source "stdio_poll" "{ printf 'ab\\n\\033[A'; sleep 2; }" 7

/// 10k lines through `IO.read_line`, counted.
#[test]
def test_read_line_reads_ten_thousand_lines : IO Bool :=
    let source := r#"use std::stream {StreamError}

#[terminating]
def count_lines (n : I64) : IO I64 := do {
  let line <- IO.read_line;
  count_from n line
}

#[terminating]
def count_from (n : I64) (r : Result StreamError (Option String)) : IO I64 :=
  match r {
    Result.ok line => count_line n line,
    Result.err _ => IO.pure (0 - 1)
  }

#[terminating]
def count_line (n : I64) (line : Option String) : IO I64 :=
  match line {
    Option.some _ => count_lines (n + 1),
    Option.none => IO.pure n
  }

def main (args : List String) : IO I64 := do {
  let n <- count_lines 0;
  return (if n == 10000 then 7 else 1)
}
"# in
    compile_source_run_stdin_expect source "stdio_many_lines" "seq 1 10000" 7
