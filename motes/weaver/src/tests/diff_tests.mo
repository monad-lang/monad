/// `Diff` tests -- weaver.md Phase 5's parity half: the pure render
/// pinned cell by cell (identical, replace, insert, delete, new file),
/// plus the `lines` splitter's edge cases and the `for_input` mapping
/// from a pick's JSON to the diff's two sides.
use std::test {Test.write_fixture}
use weaver::diff {Diff.lines, Diff.render, Diff.for_input}
use json::json {Json, Json.make_str, Json.make_object}
use std::map {Map, BTreeMap}
use std::process {process_id}
use std::list {List.length}

def line_eq (a : List String) (b : List String) : Bool :=
    if Bool.not (List.length a == List.length b)
    then false
    else lines_eq a b

#[partial]
def lines_eq (a : List String) (b : List String) : Bool :=
    match a {
        List.empty => match b { List.empty => true, _ => false },
        List.cons x rest => match b {
            List.empty => false,
            List.cons y brest => x == y && lines_eq rest brest,
        },
    }

/// Trailing newline produces no phantom empty line; an empty string is
/// no lines at all.
#[test]
def test_lines_split : Bool :=
    line_eq (Diff.lines "a\nb\nc") ["a", "b", "c"]
        && line_eq (Diff.lines "a\nb\n") ["a", "b"]
        && line_eq (Diff.lines "a") ["a"]
        && line_eq (Diff.lines "") []

/// Identical inputs render as the empty string -- no block at all.
#[test]
def test_render_identical_is_empty : Bool :=
    Diff.render "a\nb" "a\nb" == ""
        && Diff.render "" "" == ""

/// The common prefix and suffix are trimmed; only the changed middle
/// shows, `- ` for old and `+ ` for new.
#[test]
def test_render_replace_trims_context : Bool :=
    Diff.render "a\nb\nc" "a\nX\nc" == "- b\n+ X"

/// A pure insertion: no old lines at all.
#[test]
def test_render_insert : Bool :=
    Diff.render "a\nc" "a\nb\nc" == "+ b"

/// A pure deletion: no new lines at all.
#[test]
def test_render_delete : Bool :=
    Diff.render "a\nb\nc" "a\nc" == "- b"

/// A new file's diff is all `+ ` lines.
#[test]
def test_render_new_file : Bool :=
    Diff.render "" "x\ny" == "+ x\n+ y"
        && Diff.render "x\ny" "" == "- x\n- y"

// ── for_input ──────────────────────────────────────────────────────────

def obj_field (key : String) (v : String) : BTreeMap String Json :=
    Map.insert key (Json.make_str v) BTreeMap.empty

/// `edit` carries both sides in its own input -- a pure mapping.
#[test]
def test_for_input_edit : IO Bool := do {
    let input : Json := Json.make_object
        (Map.insert "expected_content" (Json.make_str "old body")
            (obj_field "new_content" "new body"));
    let r <- Diff.for_input "edit" input;
    return (match r {
        Option.some pr => match pr {
            Pair.pair old new => old == "old body" && new == "new body",
        },
        Option.none => false,
    })
}

/// `write` reads the old side from disk: an existing file's current
/// content, an empty string for a file that is new or empty.
#[test]
def test_for_input_write : IO Bool := do {
    let target : String := String.concat "/tmp/weaver_diff_target_" (String.concat (I64.to_string process_id) ".txt");
    let _ <- do { let _w <- Test.write_fixture (Path.path target) "on disk\n"; return unit };
    let input : Json := Json.make_object
        (Map.insert "path" (Json.make_str target)
            (obj_field "content" "replacement"));
    let existing <- Diff.for_input "write" input;
    let _ <- do { let _w <- Test.write_fixture (Path.path target) ""; return unit };
    let fresh <- Diff.for_input "write" input;
    return (match existing {
        Option.some pr => match pr {
            Pair.pair old new => old == "on disk\n" && new == "replacement" && fresh_side fresh,
        },
        Option.none => false,
    })
}

def fresh_side (r : Option (Pair String String)) : Bool :=
    match r {
        Option.some pr => match pr {
            Pair.pair old new => String.is_empty old && new == "replacement",
        },
        Option.none => false,
    }

/// A non-mutation pick has no diff to show.
#[test]
def test_for_input_other_is_none : IO Bool := do {
    let r <- Diff.for_input "read" (Json.make_object (obj_field "path" "/tmp"));
    return (match r {
        Option.none => true,
        Option.some _ => false,
    })
}
