/// Pure tests for the packed-payload helpers: no natives, so these run on
/// both backends without a nightly that carries the floor's wiring.

use std::list {List.length}
use sys::text {Text.parse_i64, Text.split_byte, Text.words}

def n_ok (r : Result String I64) : I64 :=
    match r {
        Result.ok v => v,
        Result.err _ => 0 - 1,
    }

/// A leading digit must never be read as a sign: `"33188"` parsed as
/// `-3188` when the check compared the DIGIT (`3`) instead of the byte.
#[test]
def test_parse_leading_digit : Bool :=
    I64.beq (n_ok (Text.parse_i64 "33188")) 33188 && I64.beq (n_ok (Text.parse_i64 "394")) 394

#[test]
def test_parse_negative : Bool :=
    I64.beq (n_ok (Text.parse_i64 "-3188")) (0 - 3188)

#[test]
def test_parse_rejects : Bool :=
    match Text.parse_i64 "12x" {
        Result.ok _ => false,
        Result.err _ => true,
    }

#[test]
def test_words_drops_empty : Bool :=
    I64.beq (List.length (Text.words "33188  394 1794084525 ")) 3

/// The NUL-separated list_dir payload uses the same splitter; a space
/// stands in here because Monad string literals have no `\0` escape.
#[test]
def test_split_byte_drops_empty : Bool :=
    I64.beq (List.length (Text.split_byte "a b " 32u8)) 2
