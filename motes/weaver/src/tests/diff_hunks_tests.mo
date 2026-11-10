/// `DiffHunks` -- weaver.md Phase 16's Myers hunks: headers, gutters,
/// insert/delete/replace, and the `+N -M` statistic.
use weaver::diff_hunks {DiffHunks.hunks, DiffHunks.render_text, DiffHunks.stat}
use std::list {List.length, List.intercalate}

def one_hunk (old : String) (new : String) : Bool :=
    match DiffHunks.hunks old new {
        Option.some hs => List.length hs == 1,
        Option.none => false,
    }

def text_of (old : String) (new : String) : String :=
    match DiffHunks.hunks old new {
        Option.some hs => DiffHunks.render_text hs,
        Option.none => "",
    }

#[test]
def test_identical_has_no_hunks : Bool :=
    match DiffHunks.hunks "a\nb\nc" "a\nb\nc" {
        Option.some hs => List.length hs == 0,
        Option.none => false,
    }

#[test]
def test_replace_has_one_hunk_with_context : Bool :=
    let t : String := text_of "a\nb\nc" "a\nX\nc" in
    one_hunk "a\nb\nc" "a\nX\nc"
        && String.contains t "@@ -1,3 +1,3 @@"
        && String.contains t "| b"
        && String.contains t "| X"
        && String.contains t "| c"

#[test]
def test_insert_has_a_new_line : Bool :=
    let t : String := text_of "a\nc" "a\nb\nc" in
    one_hunk "a\nc" "a\nb\nc"
        && String.contains t "@@ -1,2 +1,3 @@"
        && String.contains t "| b"

#[test]
def test_delete_has_an_old_line : Bool :=
    let t : String := text_of "a\nb\nc" "a\nc" in
    one_hunk "a\nb\nc" "a\nc"
        && String.contains t "@@ -1,3 +1,2 @@"
        && String.contains t "| b"

#[test]
def test_stat_counts_both_sides : Bool :=
    match DiffHunks.hunks "a\nb\nc" "a\nX\nc" {
        Option.some hs => match DiffHunks.stat hs {
            Pair.pair adds removes => I64.beq adds 1 && I64.beq removes 1,
        },
        Option.none => false,
    }

/// Two changes far apart are two hunks; close together they merge.
#[test]
def test_distant_changes_are_two_hunks : Bool :=
    let old : String := List.intercalate "\n" ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15"] in
    let new : String := List.intercalate "\n" ["X", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "Y"] in
    match DiffHunks.hunks old new {
        Option.some hs => List.length hs == 2,
        Option.none => false,
    }

#[test]
def test_close_changes_merge : Bool :=
    let t : String := text_of "a\nb\nc\nd" "a\nB\nC\nd" in
    match DiffHunks.hunks "a\nb\nc\nd" "a\nB\nC\nd" {
        Option.some hs => List.length hs == 1 && String.contains t "@@ -1,4 +1,4 @@",
        Option.none => false,
    }
