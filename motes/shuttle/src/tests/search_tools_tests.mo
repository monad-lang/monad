use std::test {Test.write_fixture}
use shuttle::tools::search {grep_run, glob_run, search_outcome, glob_script}
use shuttle::tools::search_args {GrepArgs, GlobArgs}
use shuttle::message_types {Content}
use init::transformers {ResultT}
use std::process {exec_cmd, process_id, Proc.capture}
use json::json {Json}
use std::map {Map, BTreeMap}

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

// ── glob and symlinks ───────────────────────────────────────────────────

/// A separate root: the cycle and the deep chains below must not change
/// what the grep/glob tests above see.
def links_dir : String := String.concat "/tmp/shuttle_glob_links_" (I64.to_string process_id)

#[partial]
def repeat_seg (n : I64) (seg : String) (acc : String) : String :=
    if I64.lt n 1 then acc else repeat_seg (n - 1) seg (String.concat acc seg)

def deep20 : String := String.concat (String.concat links_dir "/sub") (repeat_seg 20 "/d" "")
def deep30 : String := String.concat (String.concat links_dir "/sub") (repeat_seg 30 "/d" "")

def setup_links : IO Unit := do {
    let _ <- exec_cmd "mkdir" ["-p", String.concat links_dir "/sub"];
    let _ <- Test.write_fixture (Path.path (String.concat links_dir "/a.txt")) "a";
    let _ <- Test.write_fixture (Path.path (String.concat links_dir "/sub/b.txt")) "b";
    let _ <- exec_cmd "ln" ["-sf", "a.txt", String.concat links_dir "/link_file"];
    let _ <- exec_cmd "ln" ["-sf", "sub", String.concat links_dir "/link_dir"];
    let _ <- exec_cmd "ln" ["-sf", "nowhere", String.concat links_dir "/dangling"];
    let _ <- exec_cmd "ln" ["-sfn", ".", String.concat links_dir "/loop"];
    let _ <- exec_cmd "mkdir" ["-p", deep20];
    let _ <- exec_cmd "mkdir" ["-p", deep30];
    let _ <- Test.write_fixture (Path.path (String.concat deep20 "/in20.txt")) "d20";
    let _ <- Test.write_fixture (Path.path (String.concat deep30 "/in30.txt")) "d30";
    IO.pure unit
}

/// The `follow_links` argument is optional and read from the raw JSON,
/// so build the object here rather than extending `GlobArgs`.
def glob_in (pattern : String) (path : String) (follow : Bool) : IO (Result String Content) :=
    let j : Json := Json.make_object (Map.insert "pattern" (Json.make_str pattern)
        (Map.insert "path" (Json.make_str path)
            (Map.insert "follow_links" (Json.make_bool follow) BTreeMap.empty))) in
    ResultT.run (glob_run "gl" j)

def glob_text (r : Result String Content) : String :=
    match r {
        Result.ok c => match c { Content.tool_result _ text _ => text, _ => "" },
        Result.err _ => "ERR",
    }

#[test]
def test_glob_follows_a_symlinked_directory : IO Bool := do {
    setup_links;
    let r <- glob_in "b.txt" links_dir true;
    return (String.contains (glob_text r) "link_dir/b.txt")
}

#[test]
def test_glob_without_follow_skips_symlinks : IO Bool := do {
    setup_links;
    let r <- glob_in "b.txt" links_dir false;
    let t : String := glob_text r;
    return (Bool.and (String.contains t "sub/b.txt") (Bool.not (String.contains t "link_dir/b.txt")))
}

/// A link to its own ancestor must not hang the walk; the real file is
/// still found, and GNU find's loop warning (if it prints one) does not
/// turn the result into an error.
#[test]
def test_glob_survives_a_symlink_cycle : IO Bool := do {
    setup_links;
    let r <- glob_in "a.txt" links_dir true;
    return (match r {
        Result.ok c => match c {
            Content.tool_result _ text is_error => Bool.and (Bool.not is_error) (String.contains text "a.txt"),
            _ => false,
        },
        Result.err _ => false,
    })
}

/// The depth bound: 20 levels down is found at the default 24, 30 is not.
#[test]
def test_glob_bounds_the_walk_depth : IO Bool := do {
    setup_links;
    let near <- glob_in "in20.txt" links_dir true;
    let far <- glob_in "in30.txt" links_dir true;
    return (Bool.and (String.contains (glob_text near) "in20.txt") (Bool.not (String.contains (glob_text far) "in30.txt")))
}

/// Inside a work tree the git branch lists a symlinked directory as ONE
/// entry and never descends, so the script walks such an entry itself.
/// The tool's own git probe runs in the CALLER's cwd, so this drives the
/// script text from inside the fixture repo instead.
#[test]
def test_glob_script_walks_a_git_symlinked_directory : IO Bool := do {
    let git_dir : String := String.concat "/tmp/shuttle_glob_git_" (I64.to_string process_id);
    let script_path : String := String.concat git_dir "/glob_script.sh";
    let _ <- exec_cmd "mkdir" ["-p", String.concat git_dir "/sub"];
    let _ <- exec_cmd "git" ["init", "-q", git_dir];
    let _ <- Test.write_fixture (Path.path (String.concat git_dir "/a.txt")) "a";
    let _ <- Test.write_fixture (Path.path (String.concat git_dir "/sub/b.txt")) "b";
    let _ <- exec_cmd "ln" ["-sf", "sub", String.concat git_dir "/link_dir"];
    let _ <- Test.write_fixture (Path.path script_path) glob_script;
    let r <- Proc.capture "sh" ["-c", "cd -- \"$1\" && exec sh \"$2\" \"b.txt\" \"$1\" 1",
        "sh", git_dir, script_path];
    return (match r {
        Pair.pair rc out => Bool.and (I64.beq rc 0) (String.contains out "link_dir/b.txt"),
    })
}
