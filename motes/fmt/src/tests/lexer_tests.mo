/// Tokenizer tests. They pin the lexical boundaries the formatter relies on:
/// multi-character tokens stay whole, numbers and suffixes stay one token, and
/// comments/strings/raw strings are opaque.

use std::list {List.length}
use lib::lexer {Lex.lex, Lex.lines, Token}

#[partial]
def count (ts : List Token) : I64 :=
    match ts {
        List.empty => 0,
        List.cons _ rest => I64.add 1 (count rest),
    }

def token_count (src : String) : I64 :=
    match Lex.lex src {
        Result.ok ts => count ts,
        Result.err _ => -1,
    }

def first_token (src : String) : Option Token :=
    match Lex.lex src {
        Result.ok ts => match ts {
            List.empty => Option.none,
            List.cons t _ => Option.some t,
        },
        Result.err _ => Option.none,
    }

#[test]
def test_raw_string_is_one_token : Bool :=
    I64.beq (token_count "r#\"a b\"#") 1

#[test]
def test_plain_raw_string : Bool :=
    I64.beq (token_count "r\"a b\"") 1

#[test]
def test_int_suffix_is_one_token : Bool :=
    I64.beq (token_count "33u64") 1

#[test]
def test_float_suffix_is_one_token : Bool :=
    I64.beq (token_count "3.14f32") 1

#[test]
def test_hex_is_one_token : Bool :=
    I64.beq (token_count "0x1F") 1

/// `is_hex_byte` must stop at `F`/`f`, as `is_hex_alpha_byte` does: `G`/`g`
/// are not hex digits, so `0xFFg` is `0xFF` + `g`, not one number token.
#[test]
def test_hex_digit_class_ends_at_f : Bool :=
    I64.beq (token_count "0xFFg") 2 && I64.beq (token_count "0xG") 2

#[test]
def test_bare_dot_after_digits_is_part_of_number : Bool :=
    I64.beq (token_count "1.5") 1

#[test]
def test_char_literal_is_one_token : Bool :=
    I64.beq (token_count "'\\u{1F600}'") 1

#[test]
def test_negative_literal_is_split_for_the_renderer : Bool :=
    I64.beq (token_count "-1") 2

#[test]
def test_arrow_is_one_token : Bool :=
    I64.beq (token_count "a -> b") 3

#[test]
def test_bind_arrow_is_one_token : Bool :=
    I64.beq (token_count "x <- m") 3

#[test]
def test_colon_forms : Bool :=
    I64.beq (token_count "a :: b := c : d") 7

#[test]
def test_attribute_open_is_one_token : Bool :=
    I64.beq (token_count "#[test]") 3

#[test]
def test_mote_attribute_open_is_one_token : Bool :=
    I64.beq (token_count "#![mote]") 3

#[test]
def test_line_comment_is_trimmed : Bool :=
    match first_token "// hi   \n" {
        Option.none => false,
        Option.some t => String.beq t.text "// hi",
    }

#[test]
def test_block_comment_is_not_nested : Bool :=
    I64.beq (token_count "/* a /* not nested */ x") 2

#[test]
def test_lines_trailing_newline_has_no_empty_tail : Bool :=
    I64.beq (List.length (Lex.lines "a\n")) 1

#[test]
def test_lines_crlf : Bool :=
    let ls : List String := Lex.lines "a\r\nb\r\n" in
    match List.get 0 ls {
        Option.none => false,
        Option.some a => match List.get 1 ls {
            Option.none => false,
            Option.some b => String.beq a "a" && String.beq b "b" &&
                I64.beq (List.length ls) 2,
        },
    }

#[test]
def test_lambda_keyword_is_one_punct : Bool :=
    I64.beq (token_count "ꟛ x => x") 4
