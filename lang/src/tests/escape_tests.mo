/// Escape parity between the two compilers' string and char literals.
///
/// This file exists because these are exactly the literals the
/// self-hosted parser used to be unable to READ: `\u{XXXX}` and an
/// escaped whitespace run (a line continuation) were both "unknown
/// escape sequence" to `string_body_escape_char`
/// (`lib/parser/string.mo`), so a module containing one parsed under the
/// Rust host and failed to parse self-hosted -- which is not a test
/// failure but a `call to undefined symbol(s)` in a self-compile, at the
/// far end of the bootstrap. The escapes are written out verbatim here
/// for that reason: the file is a parse-level test as much as a
/// value-level one, and it cannot be checked by a compiler that has not
/// got the feature.
///
/// The REJECTION cases cannot be written that way -- a source-level
/// `\u{110000}` makes this file itself unparseable -- so they call
/// `string_parse`/`char_literal` on source text built at runtime
/// instead. That is the same entry point the escape decoding lives
/// behind, so they pin the boundary cases (`> 0x10FFFF`, the surrogate
/// range, more than six digits, a missing brace) rather than nothing.
///
/// The reference for every case is `core/src/parser/string.rs`:
/// `parse_unicode` is `delimited(char('{'), take_while_m_n(1, 6,
/// is_ascii_hexdigit), char('}'))` mapped through `char::from_u32`, so
/// `0xD800..=0xDFFF` and anything above the last scalar value are
/// rejected there too; `parse_escaped_whitespace` appears ONLY in
/// `parse_fragment`, the string path, so a char literal has no
/// continuation branch and `'\<newline>'` is an error in both compilers.
use lib::parser::string {char_literal, string_parse}
use lib::parser::core {ParseResult}
use lib::types {ParseTerm, ParseTermKind, ParseLiteral, char_to_string}

def nl : String := "\n"
def tab : String := "\t"
def cr : String := "\r"

/// The backslash, so a rejected escape can be built at runtime without
/// this file containing one.
def bs : String := "\\"

/// The source text of a string literal whose body is `body`.
def lit_src (body : String) : String :=
    String.concat "\"" (String.concat body "\"")

/// The source text of a char literal whose body is `body`.
def char_src (body : String) : String :=
    String.concat "'" (String.concat body "'")

/// `true` when `string_parse` REJECTS `src`.
def string_rejected (src : String) : Bool :=
    match string_parse src {
        ParseResult.fail _ => Bool.true,
        ParseResult.success _ _ => Bool.false,
    }

/// `true` when `char_literal` REJECTS `src`.
def char_rejected (src : String) : Bool :=
    match char_literal src {
        ParseResult.fail _ => Bool.true,
        ParseResult.success _ _ => Bool.false,
    }

/// The `String` a parsed string literal holds, or `<rejected>` for another
/// shape. The string-side twin of `char_value`, and what lets the fixed
/// escapes below be checked through the decoder rather than against
/// themselves.
def string_value (src : String) : String :=
    match string_parse src {
        ParseResult.fail _ => "<rejected>",
        ParseResult.success _ t =>
            match t.kind {
                ParseTermKind.lit l =>
                    match l {
                        ParseLiteral.str s => s,
                        _ => "<not-a-str>",
                    },
                _ => "<not-a-lit>",
            },
    }

/// The `Char` a parsed char literal holds, or `'?'` for another shape.
def char_value (src : String) : String :=
    match char_literal src {
        ParseResult.fail _ => "<rejected>",
        ParseResult.success _ t =>
            match t.kind {
                ParseTermKind.lit l =>
                    match l {
                        ParseLiteral.char c => char_to_string c,
                        _ => "<not-a-char>",
                    },
                _ => "<not-a-lit>",
            },
    }

// ─── `\u{...}`: values, and the four UTF-8 widths ───────────────────

#[test]
def test_unicode_escape_ascii : Bool :=
    String.beq "\u{41}" "A"

/// Upper-case hex digits are `is_ascii_hexdigit` too.
#[test]
def test_unicode_escape_upper_hex_digit : Bool :=
    String.beq "\u{4A}" "J"

/// Six digits is the maximum `take_while_m_n(1, 6, ...)` allows, and
/// leading zeros do not change the value.
#[test]
def test_unicode_escape_six_digits : Bool :=
    String.beq "\u{000041}" "A"

#[test]
def test_unicode_escape_one_byte_max : Bool :=
    I64.beq (String.length "\u{7F}") 1

/// The 2-byte range's own minimum is `0x80`, not `0xE9` -- this test
/// asserted a mid-range value under a `_min` name, so the boundary its
/// name claims went untested (`0x7F`/`0x7FF` above and below pin the two
/// ranges on either side; this pins this one's).
#[test]
def test_unicode_escape_two_byte_min : Bool :=
    Bool.and
        (I64.beq (String.length "\u{80}") 2)
        (I64.beq (String.length "\u{81}") 2)

/// ... and a mid-range 2-byte codepoint BY VALUE, which a length cannot
/// check: the decoded text has to be the character itself.
#[test]
def test_unicode_escape_two_byte_value : Bool :=
    String.beq "\u{00e9}" "é"

#[test]
def test_unicode_escape_two_byte_max : Bool :=
    I64.beq (String.length "\u{7FF}") 2

#[test]
def test_unicode_escape_three_byte_min : Bool :=
    I64.beq (String.length "\u{800}") 3

#[test]
def test_unicode_escape_three_byte_max : Bool :=
    I64.beq (String.length "\u{FFFF}") 3

#[test]
def test_unicode_escape_four_byte_min : Bool :=
    I64.beq (String.length "\u{10000}") 4

#[test]
def test_unicode_escape_four_byte_emoji : Bool :=
    String.beq "\u{1F600}" "😀"

/// `0x10FFFF` is the last scalar value, so it is accepted -- and the
/// decoder's own lead/continuation byte arithmetic has to reach four
/// bytes to produce it.
#[test]
def test_unicode_escape_max_scalar : Bool :=
    I64.beq (String.length "\u{10FFFF}") 4

/// An escape is not special-cased at the start of a run: the text on
/// either side survives.
#[test]
def test_unicode_escape_inside_a_run : Bool :=
    String.beq "x\u{41}y\u{00e9}z" "xAyéz"

#[test]
def test_unicode_escape_at_both_ends : Bool :=
    String.beq "\u{41}bc\u{42}" "AbcB"

/// `parse_escaped_char` tries `parse_unicode` FIRST, so a `\u{...}`
/// immediately after another escape still resolves.
#[test]
def test_unicode_escape_after_another_escape : Bool :=
    String.beq "\n\u{41}" "\nA"

/// A raw string is verbatim by definition -- the `\u` reaches no escape
/// handler at all.
#[test]
def test_raw_string_keeps_the_escape_verbatim : Bool :=
    String.beq r"\u{41}" "\\u{41}"

// ─── Escaped whitespace is a line continuation ──────────────────────

/// `parse_escaped_whitespace` consumes the backslash and the whole run
/// of whitespace after it, contributing nothing.
#[test]
def test_escaped_newline_is_a_line_continuation : Bool :=
    String.beq "a\
   b" "ab"

#[test]
def test_escaped_newline_twice : Bool :=
    String.beq "a\
b\
c" "abc"

#[test]
def test_escaped_whitespace_keeps_surrounding_text : Bool :=
    String.beq "ab\
  cd" "abcd"

#[test]
def test_escaped_tab_is_whitespace_too : Bool :=
    String.beq "a\	b" "ab"

/// `multispace1` is `[ \t\r\n]`, so a bare carriage return continues the
/// line as well.
#[test]
def test_escaped_cr_is_whitespace_too : Bool :=
    String.beq "a\b" "ab"

#[test]
def test_escape_still_resolves_after_a_continuation : Bool :=
    String.beq "a\
\n" "a\n"

#[test]
def test_line_continuation_before_a_unicode_escape : Bool :=
    String.beq "a\
\u{41}" "aA"

// ─── The nine fixed escapes are untouched by the two new branches ───
//
// These four go through `string_parse` on a source built at runtime, the
// same entry point the rejection cases below use. Comparing a written
// literal with itself -- which is what this block used to do, `String.beq
// "\"" "\""` being true whatever the decoder does, since both sides are
// the one token -- asserts only that the file parses. Here the decoded
// side is independent of the `nl`/`bs`/`tab` defs, so the assertion fails
// if EITHER the escape decoder or the lexer mangles the escape.

#[test]
def test_fixed_escape_newline : Bool :=
    String.beq (string_value (lit_src (String.concat bs "n"))) nl

#[test]
def test_fixed_escape_backslash : Bool :=
    String.beq (string_value (lit_src (String.concat bs bs))) bs

#[test]
def test_fixed_escape_quote : Bool :=
    String.beq (string_value (lit_src (String.concat bs "\""))) "\""

#[test]
def test_fixed_escape_tab : Bool :=
    String.beq (string_value (lit_src (String.concat bs "t"))) tab

// ─── The boundary cases, which can only be written programmatically ──

/// `char::from_u32` rejects anything above the last scalar value.
#[test]
def test_unicode_escape_rejects_above_max_scalar : Bool :=
    string_rejected (lit_src (String.concat bs "u{110000}"))

/// ... and the surrogate range, which is a `char` in Rust only through
/// `from_u32_unchecked`.
#[test]
def test_unicode_escape_rejects_surrogate_range : Bool :=
    Bool.and
        (string_rejected (lit_src (String.concat bs "u{D800}")))
        (string_rejected (lit_src (String.concat bs "u{DFFF}")))

/// `take_while_m_n(1, 6, ...)` needs at least one digit ...
#[test]
def test_unicode_escape_rejects_empty_digits : Bool :=
    string_rejected (lit_src (String.concat bs "u{}"))

/// ... and stops at six, so a seventh is a parse error rather than an
/// out-of-range codepoint.
#[test]
def test_unicode_escape_rejects_seven_digits : Bool :=
    string_rejected (lit_src (String.concat bs "u{1234567}"))

#[test]
def test_unicode_escape_rejects_non_hex_digit : Bool :=
    string_rejected (lit_src (String.concat bs "u{4g}"))

/// The `{` is not optional -- this is what separates the escape from the
/// fixed table, which would otherwise have to know about `u`.
#[test]
def test_unicode_escape_rejects_missing_brace : Bool :=
    Bool.and
        (string_rejected (lit_src (String.concat bs "u41")))
        (string_rejected (lit_src (String.concat bs "u{41")))

/// A letter that is neither `u` nor one of the nine is still unknown.
#[test]
def test_unknown_escape_is_rejected : Bool :=
    string_rejected (lit_src (String.concat bs "q"))

// ─── Char literals: `\u{...}` yes, escaped whitespace NO ────────────

#[test]
def test_char_literal_unicode_escape : Bool :=
    String.beq (char_value (char_src (String.concat bs "u{41}"))) "A"

/// The decoded codepoint is stored as its UTF-8 BYTES in the `Char`, so
/// a two-byte one round-trips.
#[test]
def test_char_literal_unicode_escape_multibyte : Bool :=
    String.beq (char_value (char_src (String.concat bs "u{00e9}"))) "é"

/// The char path's width ladder stops at two bytes above it; a three-byte
/// codepoint has to survive the same way (the payload is the codepoint's
/// UTF-8 bytes, so what is asserted is the text, not the length).
#[test]
def test_char_literal_unicode_escape_three_byte : Bool :=
    String.beq (char_value (char_src (String.concat bs "u{4E00}"))) "一"

/// This is the literal `pretty_tests.mo`'s
/// `test_show_literal_char_multibyte` cross-references by name -- it builds
/// its `Char` from a raw `λ` and says `'\u{03BB}'` decodes to the same one.
/// Nothing in this file covered `\u{03BB}` until this test, so the
/// cross-reference pointed at a case that did not exist.
#[test]
def test_char_literal_unicode_escape_lambda : Bool :=
    String.beq (char_value (char_src (String.concat bs "u{03BB}"))) "λ"

#[test]
def test_char_literal_fixed_escape : Bool :=
    Bool.and
        (String.beq (char_value (char_src (String.concat bs "n"))) nl)
        (String.beq (char_value (char_src (String.concat bs bs))) bs)

#[test]
def test_char_literal_plain : Bool :=
    String.beq (char_value (char_src "M")) "M"

/// `parse_char_literal` is `complete(delimited(char('\''),
/// alt((parse_escaped_char, anychar)), char('\'')))` -- there is no
/// `parse_escaped_whitespace` in that `alt`, so a continuation is NOT a
/// char-literal escape and must stay an error in both compilers.
#[test]
def test_char_literal_has_no_escaped_whitespace : Bool :=
    Bool.and
        (char_rejected (char_src (String.concat bs nl)))
        (char_rejected (char_src (String.concat bs tab)))

#[test]
def test_char_literal_unicode_escape_boundaries : Bool :=
    Bool.and
        (char_rejected (char_src (String.concat bs "u{110000}")))
        (char_rejected (char_src (String.concat bs "u{4g}")))
