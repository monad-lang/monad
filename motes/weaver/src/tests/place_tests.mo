/// Session places: the repo answer from `git rev-parse` and repo matching.
use weaver::place {SessionPlace, Place.repo_answer, Place.same_repo, Place.moved_note}
use std::path {Path, Path.to_string}

def place_at (cwd : String) (repo : String) : SessionPlace :=
    let p : SessionPlace := { cwd := Path.path cwd, repo := Path.path repo } in
    p

#[test]
def test_repo_answer_trims_the_toplevel : Bool :=
    let r : Path := Place.repo_answer (Path.path "/src/a/sub") (Pair.pair 0 "/src/a\n") in
    String.beq (Path.to_string r) "/src/a"

#[test]
def test_repo_answer_falls_back_to_cwd : Bool :=
    let r : Path := Place.repo_answer (Path.path "/tmp/x") (Pair.pair 128 "fatal: not a git repository") in
    String.beq (Path.to_string r) "/tmp/x"

#[test]
def test_same_repo_matches_on_repo_not_cwd : Bool :=
    let here : SessionPlace := place_at "/src/a/sub" "/src/a" in
    Place.same_repo here (Option.some (place_at "/src/a" "/src/a"))
        && Bool.not (Place.same_repo here (Option.some (place_at "/src/b" "/src/b")))
        && Bool.not (Place.same_repo here Option.none)

#[test]
def test_moved_note_only_when_the_cwd_differs : Bool :=
    let here : Option SessionPlace := Option.some (place_at "/src/a" "/src/a") in
    let same : Bool := match Place.moved_note here (Option.some (place_at "/src/a" "/src/a")) { Option.none => true, Option.some _ => false } in
    let moved : Bool := match Place.moved_note here (Option.some (place_at "/src/a/sub" "/src/a")) {
        Option.some n => String.beq n "session started in /src/a/sub",
        Option.none => false,
    } in
    let legacy : Bool := match Place.moved_note here Option.none { Option.none => true, Option.some _ => false } in
    same && moved && legacy
