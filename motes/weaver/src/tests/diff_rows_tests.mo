/// `DiffRows` -- weaver.md Phase 16's span rows for the approval dialog:
/// a header row per hunk, gutters, and paired remove/add lines highlighted.
use weaver::diff_hunks {DiffHunks.hunks}
use weaver::ui::diff_rows {DiffRows.of_hunks}
use tui::types {TextSegment}

def row_text (row : List TextSegment) : String :=
    String.concat_all (List.map (fn (s : TextSegment) => s.text) row)

def rows_of (old : String) (new : String) : List (List TextSegment) :=
    match DiffHunks.hunks old new {
        Option.some hs => DiffRows.of_hunks true hs,
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

def row_plain (row : List TextSegment) : Bool :=
    plain_segments row

#[partial]
def plain_segments (row : List TextSegment) : Bool :=
    match row {
        List.empty => true,
        List.cons s rest =>
            let no_color : Bool := match s.style.fg { Option.none => true, Option.some _ => false } in
            Bool.and (Bool.and no_color (Bool.not s.style.reverse)) (plain_segments rest),
    }

/// `NO_COLOR`/`--no-color` must reach the span rows too.
#[test]
def test_colors_off_is_plain : Bool :=
    match DiffHunks.hunks "a\nb\nc" "a\nX\nc" {
        Option.some hs =>
            let rows : List (List TextSegment) := DiffRows.of_hunks false hs in
            plain_segments (nth rows 1)
                && plain_segments (nth rows 2)
                && plain_segments (nth rows 3),
        Option.none => false,
    }

/// A non-ASCII changed pair keeps its text (the byte probes would otherwise
/// slice mid-character and render an empty body).
#[test]
def test_non_ascii_pair_keeps_its_text : Bool :=
    let rows : List (List TextSegment) := rows_of "€5\n" "é5\n" in
    String.contains (row_text (nth rows 1)) "€5"
        && String.contains (row_text (nth rows 2)) "é5"

def head (xs : List (List TextSegment)) : List TextSegment :=
    match xs { List.cons x _ => x, List.empty => List.empty }

#[partial]
def nth (xs : List (List TextSegment)) (i : I64) : List TextSegment :=
    if I64.lt i 1 then head xs
    else match xs { List.empty => head xs, List.cons _ rest => nth rest (i - 1) }
