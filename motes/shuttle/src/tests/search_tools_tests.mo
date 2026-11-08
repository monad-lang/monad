use std::test {Test.write_fixture}
use shuttle::tools::search {grep_run, glob_run, search_outcome}
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

/// No match is a result, not an error (the log review's F4: 110 empty
/// tool errors in one week of sessions).
#[test]
def test_grep_without_a_match_is_not_an_error : IO Bool := do {
    setup_fixture;
    let args : GrepArgs := { pattern := "zz_no_such_text_qq", path := test_dir };
    let r <- ResultT.run (grep_run "g2" (GrepArgs.serialize_json args));
    return (match r {
        Result.ok c => content_is_ok_and_contains c "no matches",
        Result.err _ => false,
    })
}

/// Outside a git work tree the fallback prunes `target*` build trees.
#[test]
def test_grep_skips_target_directories : IO Bool := do {
    setup_fixture;
    exec_cmd "mkdir" ["-p", String.concat test_dir "/target-rust"];
    do { let _w <- Test.write_fixture (Path.path (String.concat test_dir "/target-rust/x.txt")) "needle in the build"; return unit };
    let args : GrepArgs := { pattern := "needle", path := test_dir };
    let r <- ResultT.run (grep_run "g3" (GrepArgs.serialize_json args));
    return (match r {
        Result.ok c => Bool.and (content_is_ok_and_contains c "haystack") (Bool.not (content_is_ok_and_contains c "build")),
        Result.err _ => false,
    })
}

def outcome_error (c : Content) : Bool :=
    match c { Content.tool_result _ _ e => e, _ => false }

/// The end-of-search table: matches and "no match" succeed, a timeout and
/// an empty failure are errors, output with a non-zero rc is kept.
#[test]
def test_search_outcome_table : Bool :=
    Bool.not (outcome_error (search_outcome "i" 0 "a:1:x"))
        && Bool.not (outcome_error (search_outcome "i" 1 ""))
        && Bool.not (outcome_error (search_outcome "i" 2 "a:1:x\ngrep: b: Permission denied"))
        && outcome_error (search_outcome "i" 2 "")
        && outcome_error (search_outcome "i" 124 "")
