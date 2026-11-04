// pty / tests / ansi -- pure stripping and colour tests (no pty).
use lib::ansi {Ansi.strip, Ansi.tight, Ansi.has_color}

#[test]
def test_strip_csi_sgr : Bool :=
    Ansi.strip "\u{1b}[1;31mhi\u{1b}[0m" == "hi"

#[test]
def test_strip_csi_cursor : Bool :=
    Ansi.strip "\u{1b}[2J\u{1b}[3;5Hok" == "ok"

#[test]
def test_strip_osc_bel : Bool :=
    Ansi.strip "a\u{1b}]52;c;YWJj\u{7}b" == "ab"

#[test]
def test_strip_osc_st : Bool :=
    Ansi.strip "a\u{1b}]52;c;YWJj\u{1b}\\b" == "ab"

#[test]
def test_tight_removes_whitespace : Bool :=
    Ansi.tight "a \n\tb\r c" == "abc"

#[test]
def test_tight_keeps_utf8 : Bool :=
    Ansi.tight "日 本" == "日本"

#[test]
def test_has_color_basic_fg : Bool :=
    Ansi.has_color "\u{1b}[36mhello\u{1b}[0m"

#[test]
def test_has_color_combined : Bool :=
    Ansi.has_color "\u{1b}[31;1mhi\u{1b}[0m"

#[test]
def test_has_color_background : Bool :=
    Ansi.has_color "\u{1b}[44mhi\u{1b}[0m"

#[test]
def test_has_color_ignores_dim : Bool :=
    Bool.not (Ansi.has_color "\u{1b}[2mhi\u{1b}[0m")

#[test]
def test_has_color_ignores_reverse_and_reset : Bool :=
    Bool.not (Ansi.has_color "\u{1b}[7mhi\u{1b}[0m")

#[test]
def test_has_color_plain_text : Bool :=
    Bool.not (Ansi.has_color "plain text")
