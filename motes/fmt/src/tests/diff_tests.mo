/// Tests for the `--diff` renderer, including the terminator-only cases that
/// a line-based diff would otherwise report as no change at all.

use fmt::diff {Diff.unified}

#[test]
def test_identical_text_has_no_diff : Bool :=
    String.beq (Diff.unified "x" "a\n" "a\n") ""

#[test]
def test_final_newline_only_is_reported : Bool :=
    let d : String := Diff.unified "x" "a" "a\n" in
    String.contains d "@@ -1,1 +1,1 @@" &&
    String.contains d "No newline at end of file" &&
    String.contains d "-a" &&
    String.contains d "+a"

#[test]
def test_crlf_only_is_reported : Bool :=
    String.contains (Diff.unified "x" "a\r\n" "a\n") "line terminator differs"

#[test]
def test_real_change_has_a_hunk : Bool :=
    let d : String := Diff.unified "x" "a\nb\n" "a\nc\n" in
    String.contains d "@@ -" && String.contains d "-b" && String.contains d "+c"
