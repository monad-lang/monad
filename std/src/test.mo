// Test module

use lib::stream {StreamError, StreamError.is_not_found}

def Test.assert (condition : Bool) : Bool := condition

/// Write a test fixture file; `false` after naming the failure on
/// stderr. A fixture that never landed then shows up as itself, not as a
/// puzzling failure in whatever step reads it next (an `llc` that cannot
/// find its input, a module that will not load).
pub def Test.write_fixture (path : String) (text : String) : IO Bool := do {
    let r <- IO.write_file (Path.path path) text;
    Test.fixture_written path r
}

def Test.fixture_written (path : String) (r : Result StreamError Unit) : IO Bool :=
    match r {
        Result.ok _ => IO.pure true,
        Result.err e => do {
            IO.write_stderr ("test fixture: writing " ++ path ++ " failed: " ++ e.message ++ "\n");
            return false
        }
    }

/// Read a file a test produced; `none` after naming the failure on
/// stderr (a missing file included -- a test reads only what it expects
/// to be there).
pub def Test.read_fixture (path : String) : IO (Option String) := do {
    let r <- IO.read_file (Path.path path);
    Test.fixture_read path r
}

def Test.fixture_read (path : String) (r : Result StreamError String) : IO (Option String) :=
    match r {
        Result.ok text => IO.pure (Option.some text),
        Result.err e => do {
            IO.write_stderr ("test fixture: reading " ++ path ++ " failed: " ++ e.message ++ "\n");
            return Option.none
        }
    }

/// `Test.read_fixture`, with `fallback` in place of a failed read (which
/// is still named on stderr) -- for a test that compares the text anyway.
pub def Test.read_fixture_or (path : String) (fallback : String) : IO String := do {
    let r <- Test.read_fixture path;
    return (match r {
        Option.some text => text,
        Option.none => fallback
    })
}

/// Append `text` to a fixture file -- read, then write back -- creating it
/// when it does not exist yet. A single-threaded test's tap: there is no
/// append mode and no `IORef`. `false` after naming a failure on stderr.
pub def Test.append_fixture (path : String) (text : String) : IO Bool := do {
    let r <- IO.read_file (Path.path path);
    Test.append_to path text r
}

def Test.append_to (path : String) (text : String) (r : Result StreamError String) : IO Bool :=
    match r {
        Result.ok old => Test.write_fixture path (String.concat old text),
        Result.err e =>
            if StreamError.is_not_found e
            then Test.write_fixture path text
            else Test.append_failed path e
    }

def Test.append_failed (path : String) (e : StreamError) : IO Bool := do {
    IO.write_stderr ("test fixture: reading " ++ path ++ " failed: " ++ e.message ++ "\n");
    return false
}

#[test]
def test_assert : Bool := Test.assert true
