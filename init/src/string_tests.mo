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

#[test]
def test_byte_index_of_ascii : Bool :=
    match String.byte_index_of "hello world" "world" {
        Option.some i => I64.beq i 6i64,
        Option.none => false,
    }

#[test]
def test_byte_index_of_multibyte_prefix_counts_bytes : Bool :=
    // "é" is two bytes: the needle starts at byte 2.
    match String.byte_index_of "éllo" "llo" {
        Option.some i => I64.beq i 2i64,
        Option.none => false,
    }

#[test]
def test_byte_index_of_absent_and_empty : Bool :=
    (match String.byte_index_of "abc" "z" { Option.some _ => false, Option.none => true })
        && match String.byte_index_of "abc" "" {
            Option.some i => I64.beq i 0i64,
            Option.none => false,
        }

#[test]
def test_index_of_counts_codepoints : Bool :=
    // The same needle, one character in: "é" is a single codepoint.
    (match String.index_of "éllo" "llo" {
        Option.some i => I64.beq i 1i64,
        Option.none => false,
    })
        && (match String.index_of "hello world" "world" {
            Option.some i => I64.beq i 6i64,
            Option.none => false,
        })

#[test]
def test_index_of_absent_and_empty : Bool :=
    (match String.index_of "abc" "z" { Option.some _ => false, Option.none => true })
        && match String.index_of "abc" "" {
            Option.some i => I64.beq i 0i64,
            Option.none => false,
        }

#[test]
def test_index_of_multibyte_needle_prefix : Bool :=
    // Two codepoints before the match, though it is five bytes in.
    match String.index_of "aébc" "bc" {
        Option.some i => I64.beq i 2i64,
        Option.none => false,
    }

#[test]
def test_count_is_non_overlapping : Bool :=
    I64.beq (String.count "aaa" "aa") 1i64
        && I64.beq (String.count "a,b,c" ",") 2i64
        && I64.beq (String.count "abc" "z") 0i64
        && I64.beq (String.count "abc" "") 0i64

#[test]
def test_split_basic : Bool :=
    I64.beq (List.length (String.split "a,b,c" ",")) 3i64
        && (match List.get 0 (String.split "a,b,c" ",") {
            Option.some p => String.beq p "a",
            Option.none => false,
        })
        && (match List.get 2 (String.split "a,b,c" ",") {
            Option.some p => String.beq p "c",
            Option.none => false,
        })

#[test]
def test_split_keeps_empty_pieces : Bool :=
    let parts : List String := String.split "a," "," in
    I64.beq (List.length parts) 2i64
        && (match List.get 1 (Shared.get (Shared.of parts)) {
            Option.some p => String.is_empty p,
            Option.none => false,
        })

#[test]
def test_split_empty_separator_is_the_whole_string : Bool :=
    let parts : List String := String.split "abc" "" in
    I64.beq (List.length parts) 1i64
        && (match List.get 0 (Shared.get (Shared.of parts)) {
            Option.some p => String.beq p "abc",
            Option.none => false,
        })

#[test]
def test_split_multibyte_pieces : Bool :=
    I64.beq (List.length (String.split "héllo|wörld" "|")) 2i64
        && (match List.get 0 (String.split "héllo|wörld" "|") {
            Option.some p => String.beq p "héllo",
            Option.none => false,
        })
        && (match List.get 1 (String.split "héllo|wörld" "|") {
            Option.some p => String.beq p "wörld",
            Option.none => false,
        })
