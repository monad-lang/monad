/// `DiffRows` -- weaver.md Phase 16's span rows for the approval dialog:
/// a header row per hunk, gutters, and paired remove/add lines highlighted.
use weaver::diff_hunks {DiffHunks.hunks}
use weaver::ui::diff_rows {DiffRows.of_hunks}
use tui::types {TextSegment}
use std::list {List.length}

def row_text (row : List TextSegment) : String :=
    String.concat_all (List.map (fn (s : TextSegment) => s.text) row)

def rows_of (old : String) (new : String) : List (List TextSegment) :=
    match DiffHunks.hunks old new {
        Option.some hs => DiffRows.of_hunks hs,
        Option.none => List.empty,
    }

#[test]
def test_a_replace_has_a_header_and_the_context_rows : Bool :=
    let rows : List (List TextSegment) := rows_of "a\nb\nc" "a\nX\nc" in
    I64.beq (List.length rows) 5
        && String.contains (row_text (head rows)) "@@ -1,3 +1,3 @@"
        && String.contains (row_text (nth rows 1)) "|   a"
        && String.contains (row_text (nth rows 2)) "| - b"
        && String.contains (row_text (nth rows 3)) "| + X"
        && String.contains (row_text (nth rows 4)) "|   c"

#[test]
def test_a_changed_pair_highlights_the_differing_middle : Bool :=
    let rows : List (List TextSegment) := rows_of "line two\n" "line two changed\n" in
    // header, remove, add
    String.contains (row_text (nth rows 1)) "line two"
        && String.contains (row_text (nth rows 2)) "line two changed"
        && I64.gt (List.length (nth rows 2)) 2

def head (xs : List (List TextSegment)) : List TextSegment :=
    match xs { List.cons x _ => x, List.empty => List.empty }

#[partial]
def nth (xs : List (List TextSegment)) (i : I64) : List TextSegment :=
    if I64.lt i 1 then head xs
    else match xs { List.empty => head xs, List.cons _ rest => nth rest (i - 1) }
