// Scanner tests: line splitting, UTF-8 decoding, and the cursor's tab stops.
use lib::scan {
    Markdown.Cursor, Markdown.char_width, Markdown.codepoint_at, Markdown.is_blank,
    Markdown.leading_spaces, Markdown.split_lines, Markdown.utf8_of_codepoint,
}

def one (xs : List String) (i : I64) : String :=
    match List.get i xs {
        Option.some s => s,
        Option.none => "<missing>"
    }

def count (xs : List String) : I64 :=
    match xs {
        List.empty => 0i64,
        List.cons _ rest => I64.add 1i64 (count rest)
    }

// ─── split_lines ───

#[test]
def test_split_empty_is_no_lines : Bool :=
    I64.beq (count (Markdown.split_lines "")) 0i64

#[test]
def test_split_one_line : Bool :=
    I64.beq (count (Markdown.split_lines "abc")) 1i64

#[test]
def test_split_trailing_newline_adds_no_line : Bool :=
    let xs := Markdown.split_lines "a\nb\n" in
    Bool.and (I64.beq (count xs) 2i64)
        (Bool.and (String.beq (one xs 0i64) "a") (String.beq (one xs 1i64) "b"))

#[test]
def test_split_keeps_inner_blank_line : Bool :=
    let xs := Markdown.split_lines "a\n\nb" in
    Bool.and (I64.beq (count xs) 3i64)
        (Bool.and (String.beq (one xs 1i64) "") (String.beq (one xs 2i64) "b"))

#[test]
def test_split_strips_crlf : Bool :=
    let xs := Markdown.split_lines "a\r\nb\r\n" in
    Bool.and (String.beq (one xs 0i64) "a") (String.beq (one xs 1i64) "b")

#[test]
def test_split_strips_one_bom : Bool :=
    let xs := Markdown.split_lines "\u{feff}x" in
    Bool.and (I64.beq (count xs) 1i64) (String.beq (one xs 0i64) "x")

/// The BOM is only stripped at the very start, never mid-document.
#[test]
def test_split_keeps_later_bom : Bool :=
    let xs := Markdown.split_lines "a\n\u{feff}b" in
    String.beq (one xs 1i64) "\u{feff}b"

#[test]
def test_split_keeps_utf8_whole : Bool :=
    let xs := Markdown.split_lines "héllo\n世界" in
    Bool.and (String.beq (one xs 0i64) "héllo") (String.beq (one xs 1i64) "世界")

// ─── codepoints ───

#[test]
def test_codepoint_ascii : Bool :=
    match Markdown.codepoint_at "a" {
        Option.some c => U32.beq c 97u32,
        Option.none => false
    }

#[test]
def test_codepoint_two_byte : Bool :=
    match Markdown.codepoint_at "é" {
        Option.some c => U32.beq c 233u32,
        Option.none => false
    }

#[test]
def test_codepoint_three_byte : Bool :=
    match Markdown.codepoint_at "—" {
        Option.some c => U32.beq c 8212u32,
        Option.none => false
    }

#[test]
def test_codepoint_four_byte : Bool :=
    match Markdown.codepoint_at "😀" {
        Option.some c => U32.beq c 128512u32,
        Option.none => false
    }

#[test]
def test_codepoint_empty_is_none : Bool :=
    match Markdown.codepoint_at "" {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_char_width_steps_whole_characters : Bool :=
    Bool.and (I64.beq (Markdown.char_width "a") 1i64)
        (Bool.and (I64.beq (Markdown.char_width "é") 2i64)
            (Bool.and (I64.beq (Markdown.char_width "—") 3i64)
                (I64.beq (Markdown.char_width "😀") 4i64)))

#[test]
def test_utf8_round_trip : Bool :=
    Bool.and (String.beq (Markdown.utf8_of_codepoint 97i64) "a")
        (Bool.and (String.beq (Markdown.utf8_of_codepoint 233i64) "é")
            (Bool.and (String.beq (Markdown.utf8_of_codepoint 8212i64) "—")
                (String.beq (Markdown.utf8_of_codepoint 128512i64) "😀")))

/// Numeric references out of range, and surrogate halves, are U+FFFD.
#[test]
def test_utf8_of_codepoint_replaces_bad_values : Bool :=
    let replacement := "\u{fffd}" in
    Bool.and (String.beq (Markdown.utf8_of_codepoint 0i64) replacement)
        (Bool.and (String.beq (Markdown.utf8_of_codepoint 55296i64) replacement)
            (Bool.and (String.beq (Markdown.utf8_of_codepoint 1114112i64) replacement)
                (String.beq (Markdown.utf8_of_codepoint -1i64) replacement)))

// ─── blank lines and indentation ───

#[test]
def test_blank_lines : Bool :=
    Bool.and (Markdown.is_blank "")
        (Bool.and (Markdown.is_blank "  \t ")
            (Bool.not (Markdown.is_blank " x")))

#[test]
def test_leading_spaces : Bool :=
    Bool.and (I64.beq (Markdown.leading_spaces "   x") 3i64)
        (I64.beq (Markdown.leading_spaces "x") 0i64)

// ─── cursor and tab stops ───

#[test]
def test_cursor_tab_consumes_one_column_and_holds_the_rest : Bool :=
    let c := Markdown.Cursor.step (Markdown.Cursor.start "\tx") in
    Bool.and (I64.beq c.column 1i64) (I64.beq (I64.add c.column c.tabs) 4i64)

#[test]
def test_cursor_partial_tab_reads_as_spaces : Bool :=
    let c := Markdown.Cursor.step (Markdown.Cursor.start "\tx") in
    match Markdown.Cursor.peek c {
        Option.some b => U8.beq b 32u8,
        Option.none => false
    }

/// A tab at column 2 reaches column 4, so only two columns were consumed.
#[test]
def test_cursor_tab_width_depends_on_column : Bool :=
    let c := Markdown.Cursor.step_many 2i64 (Markdown.Cursor.start "  \tx") in
    let d := Markdown.Cursor.step c in
    I64.beq d.column 3i64

#[test]
def test_cursor_at_end : Bool :=
    Bool.and (Markdown.Cursor.at_end (Markdown.Cursor.start ""))
        (Bool.not (Markdown.Cursor.at_end (Markdown.Cursor.start "x")))

#[test]
def test_cursor_skip_spaces : Bool :=
    let c := Markdown.Cursor.skip_spaces (Markdown.Cursor.start "  x") in
    I64.beq c.column 2i64

#[test]
def test_cursor_blank : Bool :=
    Bool.and (Markdown.Cursor.blank (Markdown.Cursor.start " \t "))
        (Bool.not (Markdown.Cursor.blank (Markdown.Cursor.start " x")))
