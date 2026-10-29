/// `String.contains` / `String.trim` after the scan was moved off `List U8`.
///
/// The scan steps by whole UTF-8 characters: `String.drop` returns `""` on a
/// mid-character offset, so a byte-at-a-time walk stopped at the first
/// non-ASCII byte. These pin the unicode cases that regressed.
use init::string {}

#[test]
def test_contains_ascii : Bool :=
    String.contains "hello world" "world"
        && Bool.not (String.contains "hello" "xyz")

#[test]
def test_contains_after_a_multibyte_character : Bool :=
    String.contains "héllo" "llo" && String.contains "abcédef" "def"

#[test]
def test_contains_a_multibyte_needle : Bool :=
    String.contains "naïve café" "café"

#[test]
def test_contains_an_empty_needle : Bool :=
    String.contains "anything" ""

#[test]
def test_contains_a_needle_longer_than_the_haystack : Bool :=
    Bool.not (String.contains "ab" "abcd")

#[test]
def test_trim_keeps_multibyte_text_intact : Bool :=
    String.beq (String.trim "  héllo  ") "héllo"

#[test]
def test_trim_still_handles_ascii : Bool :=
    String.beq (String.trim "\t  hi \n ") "hi"
