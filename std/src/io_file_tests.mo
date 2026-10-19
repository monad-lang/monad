/// Tests for `std/src/io.mo`'s whole-file `IO.read_file`/`IO.write_file`.
///
/// A separate file for the reason `process.mo` gives (a `#[test]` in a
/// `std/src/lib.mo` re-export is never discovered). Real files under
/// /tmp, so each test runs the actual open/read/write/close path on
/// whichever backend runs it. Every match lives in its own `iof_*`
/// helper, as in `stream_tests.mo`.

use std::process {exec_cmd, process_id}
use std::stream {StreamError, StreamError.is_not_found, StreamErrorKind}

def iof_path (name : String) : String :=
    "/tmp/monad_io_file_tests_" ++ I64.to_string process_id ++ "_" ++ name

def iof_write (path : String) (text : String) : IO (Result StreamError Unit) :=
    IO.write_file (Path.path path) text

def iof_read (path : String) : IO (Result StreamError String) :=
    IO.read_file (Path.path path)

def iof_wrote (r : Result StreamError Unit) : Bool :=
    match r {
        Result.ok _ => true,
        Result.err _ => false
    }

def iof_read_is (r : Result StreamError String) (expected : String) : Bool :=
    match r {
        Result.ok text => String.beq text expected,
        Result.err _ => false
    }

def iof_read_not_found (r : Result StreamError String) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => StreamError.is_not_found e
    }

def iof_write_not_found (r : Result StreamError Unit) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => StreamError.is_not_found e
    }

def iof_permission_denied (r : Result StreamError String) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e =>
            match e.kind {
                StreamErrorKind.permission_denied => true,
                _ => false
            }
    }

/// `n` copies of `s`, for `String.concat_list` (one allocation, where
/// `String.repeat` is a quadratic fold).
#[terminating]
def iof_pieces (s : String) (n : I64) : List String :=
    if n == 0 then List.empty else List.cons s (iof_pieces s (n - 1))

/// Write `text` to a fresh file, read it back, remove it.
def iof_round_trip (name : String) (text : String) : IO Bool := do {
    let path := iof_path name;
    let wrote <- iof_write path text;
    let back <- iof_read path;
    exec_cmd "rm" ["-f", path];
    return (iof_wrote wrote && iof_read_is back text)
}

#[test]
def test_small_file_round_trips : IO Bool := iof_round_trip "small" "hello, file\nsecond line\n"

#[test]
def test_empty_file_round_trips : IO Bool := iof_round_trip "empty" ""

/// 65535 ASCII bytes, then a two-byte `é` whose halves land in the first
/// and second 64 KiB read: decoding chunk by chunk would turn it into
/// U+FFFD (interpreted), so this pins the gather-then-decode join.
#[test]
def test_multibyte_character_across_a_chunk_boundary_survives : IO Bool :=
    iof_round_trip "boundary" (String.concat_list (iof_pieces "aaaaa" 13107) ++ "é and after")

/// About 200 KB: four reads, so more than two chunks are gathered.
#[test]
def test_multi_chunk_file_round_trips : IO Bool :=
    iof_round_trip "multi" (String.concat_list (iof_pieces "0123456789 ünïcödé\n" 9000))

/// Write truncates: the second write replaces the first entirely.
#[test]
def test_write_replaces_a_longer_file : IO Bool := do {
    let path := iof_path "overwrite";
    let _ <- iof_write path "a much longer first version";
    let wrote <- iof_write path "short";
    let back <- iof_read path;
    exec_cmd "rm" ["-f", path];
    return (iof_wrote wrote && iof_read_is back "short")
}

/// A missing file is an error, never an empty string.
#[test]
def test_read_of_a_missing_file_is_not_found : IO Bool := do {
    let r <- iof_read (iof_path "does_not_exist");
    return (iof_read_not_found r)
}

/// The parent directory is not created.
#[test]
def test_write_into_a_missing_directory_is_not_found : IO Bool := do {
    let r <- iof_write (iof_path "no_such_dir/file") "x";
    return (iof_write_not_found r)
}

/// Skipped (passes) as root, who may read a mode-000 file anyway.
#[test]
def test_read_of_an_unreadable_file_is_permission_denied : IO Bool := do {
    let path := iof_path "unreadable";
    let _ <- iof_write path "secret";
    exec_cmd "chmod" ["000", path];
    let is_root <- exec_cmd "sh" ["-c", "test \"$(id -u)\" = 0"];
    let r <- iof_read path;
    exec_cmd "rm" ["-f", path];
    return (is_root == 0 || iof_permission_denied r)
}
