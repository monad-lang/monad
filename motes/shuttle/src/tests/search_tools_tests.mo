use std::test {Test.write_fixture}
use shuttle::tools::search {grep_run, glob_run}
use shuttle::tools::search_args {GrepArgs, GlobArgs}
use shuttle::message_types {Content}
use init::transformers {ResultT}
use std::process {exec_cmd, process_id}

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same directory.
def test_dir : String := String.concat "/tmp/shuttle_search_test_dir_" (I64.to_string process_id)

def test_file_path : String := String.concat test_dir "/a.txt"

def setup_fixture : IO Unit := do {
    exec_cmd "mkdir" ["-p", test_dir];
    do { let _w <- Test.write_fixture (Path.path test_file_path) "needle in a haystack\nanother line"; return unit }
}

def grep_fixture_result : IO (Result String Content) :=
    let args : GrepArgs := { pattern := "needle", path := test_file_path } in
    ResultT.run (grep_run "g1" (GrepArgs.serialize_json args))

def content_is_ok_and_contains (c : Content) (needle : String) : Bool :=
    match c {
        Content.tool_result _ text is_error => Bool.not is_error && String.contains text needle,
        _ => false,
    }

#[test]
def test_grep_finds_match : IO Bool := do {
    setup_fixture;
    let r <- grep_fixture_result;
    return (match r {
        Result.ok c => content_is_ok_and_contains c "needle in a haystack",
        Result.err _ => false,
    })
}

def glob_fixture_result : IO (Result String Content) :=
    let args : GlobArgs := { pattern := "a.txt", path := test_dir } in
    ResultT.run (glob_run "gl1" (GlobArgs.serialize_json args))

#[test]
def test_glob_finds_file : IO Bool := do {
    setup_fixture;
    let r <- glob_fixture_result;
    return (match r {
        Result.ok c => content_is_ok_and_contains c "a.txt",
        Result.err _ => false,
    })
}
