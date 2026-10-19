/// Tests for `std/src/stream.mo`.
///
/// A separate file for the reason `bytebuf_tests.mo` gives. Real files
/// under /tmp rather than mocks, so each test exercises the actual
/// open/read/write/close path on whichever backend runs it. Every match
/// lives in its own `st_*` helper: no `#[test]` def nests two
/// differently-typed matches (the recorded self-hosted codegen hazard).

use std::process {exec_cmd, process_id}
use std::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.length, ByteBuf.of_string, ByteBuf.to_string}
use std::stream {Stream, FdStream.read_line_bounded, StreamError, StreamError.kind_of_code, StreamErrorKind, FdStream, FdStream.open_file, FdStream.read_mode, FdStream.write_mode, FdStream.append_mode, PartialLinePolicy}

def st_path (name : String) : String :=
    "/tmp/monad_stream_tests_" ++ I64.to_string process_id ++ "_" ++ name

// ─── Helpers: writing ───

def st_wrote (r : Result StreamError I64) (n : I64) : Bool :=
    match r {
        Result.ok m => m == n,
        Result.err _ => false
    }

def st_write_all (s : FdStream) (text : String) : IO Bool := do {
    let buf <- ByteBuf.of_string text;
    let r <- Stream.write s buf;
    let _ <- ByteBuf.free buf;
    let _ <- Stream.close s;
    return (st_wrote r (String.length text))
}

def st_write_opened (opened : Result StreamError FdStream) (text : String) : IO Bool :=
    match opened {
        Result.err _ => IO.pure false,
        Result.ok s => st_write_all s text
    }

/// Create-or-truncate `path` holding exactly `text`.
def st_write_file (path : String) (text : String) : IO Bool := do {
    let opened <- FdStream.open_file (Path.path path) FdStream.write_mode;
    st_write_opened opened text
}

// ─── Helpers: reading ───

/// The whole stream, read in 4 KiB pieces until the zero-length end.
#[terminating]
def st_read_all (s : FdStream) (acc_rev : List String) : IO (Option String) := do {
    let r <- Stream.read s 4096;
    st_read_step s acc_rev r
}

#[terminating]
def st_read_step (s : FdStream) (acc_rev : List String) (r : Result StreamError ByteBuf) : IO (Option String) :=
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok buf => st_read_buf s acc_rev buf
    }

#[terminating]
def st_read_buf (s : FdStream) (acc_rev : List String) (buf : ByteBuf) : IO (Option String) := do {
    let n := ByteBuf.length buf;
    let text <- ByteBuf.to_string buf n;
    let _ <- ByteBuf.free buf;
    if n == 0
    then do { return (Option.some (String.concat_list (List.reverse acc_rev))) }
    else st_read_all s (List.cons text acc_rev)
}

def st_read_opened (opened : Result StreamError FdStream) : IO (Option String) :=
    match opened {
        Result.err _ => IO.pure Option.none,
        Result.ok s => st_read_and_close s
    }

def st_read_and_close (s : FdStream) : IO (Option String) := do {
    let text <- st_read_all s List.empty;
    let _ <- Stream.close s;
    return text
}

def st_read_file (path : String) : IO (Option String) := do {
    let opened <- FdStream.open_file (Path.path path) FdStream.read_mode;
    st_read_opened opened
}

def st_some_is (o : Option String) (expected : String) : Bool :=
    match o {
        Option.some s => String.beq s expected,
        Option.none => false
    }

/// `n` copies of a 10-byte piece, joined once.
#[terminating]
def st_pieces (n : I64) : List String :=
    if n == 0 then List.empty
    else List.cons "0123456789" (st_pieces (n - 1))

// ─── Helpers: error kinds ───

/// The declaration index of a kind -- the inverse of `kind_of_code`.
def st_kind_code (k : StreamErrorKind) : I64 :=
    match k {
        StreamErrorKind.not_found => 0,
        StreamErrorKind.permission_denied => 1,
        StreamErrorKind.connection_refused => 2,
        StreamErrorKind.connection_reset => 3,
        StreamErrorKind.broken_pipe => 4,
        StreamErrorKind.invalid_input => 5,
        StreamErrorKind.timed_out => 6,
        StreamErrorKind.address_in_use => 7,
        StreamErrorKind.host_unresolved => 8,
        StreamErrorKind.other => 9
    }

#[terminating]
def st_codes_round_trip (i : I64) : Bool :=
    if i > 9 then true
    else st_kind_code (StreamError.kind_of_code i) == i && st_codes_round_trip (i + 1)

def st_open_failed_with (r : Result StreamError FdStream) (code : I64) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => st_kind_code e.kind == code
    }

// ─── Helpers: lines ───

def st_line_is (r : Result StreamError (Option String)) (expected : String) : Bool :=
    match r {
        Result.ok o => st_some_is o expected,
        Result.err _ => false
    }

def st_none_is (o : Option String) : Bool :=
    match o {
        Option.none => true,
        Option.some _ => false
    }

def st_line_eof (r : Result StreamError (Option String)) : Bool :=
    match r {
        Result.ok o => st_none_is o,
        Result.err _ => false
    }

def st_line_err_kind (r : Result StreamError (Option String)) (code : I64) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => st_kind_code e.kind == code
    }

/// Three reads with `policy` off `path`, which holds "ab\ncd" (the last
/// line unterminated): "ab", then "cd" if `partial_delivered` else end
/// of stream, then end of stream.
def st_three_lines (path : String) (policy : PartialLinePolicy) (partial_delivered : Bool) : IO Bool := do {
    let opened <- FdStream.open_file (Path.path path) FdStream.read_mode;
    st_three_lines_opened opened policy partial_delivered
}

def st_three_lines_opened (opened : Result StreamError FdStream) (policy : PartialLinePolicy) (partial_delivered : Bool) : IO Bool :=
    match opened {
        Result.err _ => IO.pure false,
        Result.ok s => st_three_lines_of s policy partial_delivered
    }

def st_three_lines_of (s : FdStream) (policy : PartialLinePolicy) (partial_delivered : Bool) : IO Bool := do {
    let a <- FdStream.read_line_bounded s 0 policy;
    let b <- FdStream.read_line_bounded s 0 policy;
    let c <- FdStream.read_line_bounded s 0 policy;
    let _ <- Stream.close s;
    let second_ok := if partial_delivered then st_line_is b "cd" else st_line_eof b;
    return (st_line_is a "ab" && second_ok && st_line_eof c)
}

def st_bounded_line (path : String) (max_len : I64) : IO (Result StreamError (Option String)) := do {
    let opened <- FdStream.open_file (Path.path path) FdStream.read_mode;
    st_bounded_line_opened opened max_len
}

def st_bounded_line_opened (opened : Result StreamError FdStream) (max_len : I64) : IO (Result StreamError (Option String)) :=
    match opened {
        Result.err e => IO.pure (Result.err e),
        Result.ok s => st_bounded_line_of s max_len
    }

def st_bounded_line_of (s : FdStream) (max_len : I64) : IO (Result StreamError (Option String)) := do {
    let r <- FdStream.read_line_bounded s max_len PartialLinePolicy.deliver;
    let _ <- Stream.close s;
    return r
}

// ─── Tests: files ───

#[test]
def test_file_round_trips : IO Bool := do {
    let path := st_path "round_trip";
    let wrote <- st_write_file path "hello, stream\n";
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back "hello, stream\n")
}

/// Several 4 KiB reads and a final zero-length one: 70 KB written in one
/// buffer must come back byte-for-byte, however the reads split it.
#[test]
def test_file_larger_than_one_read_round_trips : IO Bool := do {
    let path := st_path "large";
    let text := String.concat_list (st_pieces 7000);
    let wrote <- st_write_file path text;
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back text)
}

/// Append mode adds to the existing file instead of replacing it.
#[test]
def test_append_mode_appends : IO Bool := do {
    let path := st_path "append";
    let _ <- st_write_file path "one";
    let opened <- FdStream.open_file (Path.path path) FdStream.append_mode;
    let wrote <- st_write_opened opened "two";
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back "onetwo")
}

/// Append mode creates a missing file.
#[test]
def test_append_mode_creates : IO Bool := do {
    let path := st_path "append_create";
    let _ <- exec_cmd "rm" ["-f", path];
    let opened <- FdStream.open_file (Path.path path) FdStream.append_mode;
    let wrote <- st_write_opened opened "fresh";
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back "fresh")
}

/// Write mode truncates: the second write replaces the first.
#[test]
def test_write_mode_truncates : IO Bool := do {
    let path := st_path "truncate";
    let _ <- st_write_file path "a much longer first version";
    let wrote <- st_write_file path "short";
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back "short")
}

/// An empty file reads as end of stream straight away.
#[test]
def test_empty_file_reads_as_end_of_stream : IO Bool := do {
    let path := st_path "empty";
    let wrote <- st_write_file path "";
    let back <- st_read_file path;
    exec_cmd "rm" ["-f", path];
    return (wrote && st_some_is back "")
}

// ─── Tests: errors ───

#[test]
def test_open_of_a_missing_file_is_not_found : IO Bool := do {
    let r <- FdStream.open_file (Path.path (st_path "does_not_exist")) FdStream.read_mode;
    return (st_open_failed_with r 0)
}

/// Skipped (passes) as root, who may read a mode-000 file anyway.
#[test]
def test_open_of_an_unreadable_file_is_permission_denied : IO Bool := do {
    let path := st_path "unreadable";
    let _ <- st_write_file path "secret";
    exec_cmd "chmod" ["000", path];
    let is_root <- exec_cmd "sh" ["-c", "test \"$(id -u)\" = 0"];
    let r <- FdStream.open_file (Path.path path) FdStream.read_mode;
    exec_cmd "rm" ["-f", path];
    return (is_root == 0 || st_open_failed_with r 1)
}

#[test]
def test_open_with_an_unknown_mode_is_invalid_input : IO Bool := do {
    let r <- FdStream.open_file (Path.path (st_path "mode")) 7;
    return (st_open_failed_with r 5)
}

/// Every native kind code decodes to the kind declared at that index.
#[test]
def test_kind_codes_round_trip : Bool := st_codes_round_trip 0

#[test]
def test_an_out_of_range_kind_code_is_other : Bool :=
    st_kind_code (StreamError.kind_of_code 42) == 9 && st_kind_code (StreamError.kind_of_code (0 - 1)) == 9

// ─── Tests: lines ───

#[test]
def test_read_line_delivers_a_partial_last_line : IO Bool := do {
    let path := st_path "lines_deliver";
    let _ <- st_write_file path "ab\ncd";
    let ok <- st_three_lines path PartialLinePolicy.deliver true;
    exec_cmd "rm" ["-f", path];
    return ok
}

#[test]
def test_read_line_discards_a_partial_last_line : IO Bool := do {
    let path := st_path "lines_discard";
    let _ <- st_write_file path "ab\ncd";
    let ok <- st_three_lines path PartialLinePolicy.discard false;
    exec_cmd "rm" ["-f", path];
    return ok
}

/// A line past the bound is `invalid_input`, not a longer line.
#[test]
def test_read_line_over_the_bound_is_invalid_input : IO Bool := do {
    let path := st_path "lines_bound";
    let _ <- st_write_file path "abcdef\n";
    let r <- st_bounded_line path 3;
    exec_cmd "rm" ["-f", path];
    return (st_line_err_kind r 5)
}

/// A line exactly at the bound still fits.
#[test]
def test_read_line_at_the_bound_fits : IO Bool := do {
    let path := st_path "lines_at_bound";
    let _ <- st_write_file path "abc\n";
    let r <- st_bounded_line path 3;
    exec_cmd "rm" ["-f", path];
    return (st_line_is r "abc")
}
