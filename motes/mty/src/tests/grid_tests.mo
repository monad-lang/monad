// mty / tests / grid -- pure screen-model tests (no pty).
use lib::grid {Grid}

def pair_is (p : Pair I64 I64) (row : I64) (col : I64) : Bool :=
    match p {
        Pair.pair r c => I64.beq r row && I64.beq c col
    }

def find_is (g : Grid) (needle : String) (row : I64) (col : I64) : Bool :=
    match Grid.find g needle {
        Option.some p => pair_is p row col,
        Option.none => false
    }

def utf8_head : List U8 := [230u8, 151u8]
def utf8_tail : List U8 := [165u8]

#[test]
def test_plain_text_at_origin : Bool :=
    find_is (Grid.of_string 24 80 "hello") "hello" 0 0

#[test]
def test_csi_cursor_move : Bool :=
    find_is (Grid.of_string 24 80 "\u{1b}[3;5Hhi") "hi" 2 4

#[test]
def test_clear_and_rewrite : Bool :=
    find_is (Grid.of_string 24 80 "old\u{1b}[2J\u{1b}[1;1Hnew") "new" 0 0

#[test]
def test_crlf_rows : Bool :=
    find_is (Grid.of_string 24 80 "one\r\ntwo") "two" 1 0

#[test]
def test_wide_glyph_columns : Bool :=
    let g := Grid.of_string 24 80 "日本" in
    find_is g "日本" 0 0 && find_is g "本" 0 2

#[test]
def test_wide_continuation_is_one_cell : Bool :=
    find_is (Grid.of_string 24 80 "日X") "X" 0 2

#[test]
def test_incomplete_escape_is_carried : Bool :=
    match Grid.feed_from (Grid.empty 24 80) "\u{1b}[" 0 {
        Pair.pair _ consumed => I64.beq consumed 0
    }

#[test]
def test_incomplete_utf8_is_carried : Bool :=
    let head := String.from_list utf8_head in
    let tail := String.from_list utf8_tail in
    match Grid.feed_from (Grid.empty 24 80) head 0 {
        Pair.pair _ consumed =>
            let whole := String.concat head tail in
            match Grid.feed_from (Grid.empty 24 80) whole consumed {
                Pair.pair g done =>
                    I64.beq consumed 0 && I64.gt done 0 && find_is g "日" 0 0
            }
    }

#[test]
def test_sgr_is_ignored_but_text_lands : Bool :=
    find_is (Grid.of_string 24 80 "\u{1b}[7mhi\u{1b}[0m") "hi" 0 0
