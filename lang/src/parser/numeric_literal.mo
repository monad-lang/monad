/// Numeric LITERALS: digits plus an optional suffix, lowered to a
/// `ParseTerm`. The AST-producing half of what used to be one `number.mo`.
///
/// Split out so `number.mo` -- the digit scanner this file calls -- can stay
/// free of `lang::types` and be reused by a parser substrate that knows
/// nothing about terms. Everything here is the opposite: `NumSuffix`,
/// `ParseTerm` and `pt_lit` are the point.

use lang::types {NumSuffix, ParseTerm, flt, num, pt_lit}
use parsec::core {ParseResult, is_empty}
use parsec::number {
  char_to_digit, hex_number, number, parse_digits, parse_digits_char,
}
use parsec::char_preds {is_digit, is_digit_byte, is_digit_or_underscore_byte}
use parsec::combinators {tag, take_while_byte}

open ParseResult {fail, success}

// --- Numeric literal suffixes (`33u64`, `3.0f32`) ---
//
// Mirrors the Rust reference's `num_suffix_parser`/`float_suffix_parser`
// (rust/core/src/parser.rs): a suffix must immediately follow the digits with
// no intervening whitespace, and int literals accept all ten suffixes
// (`33f64` is a legal *integer-valued* literal tagged with an f64 suffix
// — the actual int-to-float conversion is a later concern, not the
// parser's) while float literals (written with a `.`) accept only
// `f32`/`f64`.

#[partial]
def int_suffix_parser (input : String) : ParseResult NumSuffix :=
	int_suffix_try_i8 (tag "i8" input) input

#[partial]
def int_suffix_try_i8 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.i8,
		fail _ => int_suffix_try_i16 (tag "i16" orig) orig
	}

#[partial]
def int_suffix_try_i16 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.i16,
		fail _ => int_suffix_try_i32 (tag "i32" orig) orig
	}

#[partial]
def int_suffix_try_i32 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.i32,
		fail _ => int_suffix_try_i64 (tag "i64" orig) orig
	}

#[partial]
def int_suffix_try_i64 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.i64,
		fail _ => int_suffix_try_u8 (tag "u8" orig) orig
	}

#[partial]
def int_suffix_try_u8 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.u8,
		fail _ => int_suffix_try_u16 (tag "u16" orig) orig
	}

#[partial]
def int_suffix_try_u16 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.u16,
		fail _ => int_suffix_try_u32 (tag "u32" orig) orig
	}

#[partial]
def int_suffix_try_u32 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.u32,
		fail _ => int_suffix_try_u64 (tag "u64" orig) orig
	}

#[partial]
def int_suffix_try_u64 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.u64,
		fail _ => int_suffix_try_f32 (tag "f32" orig) orig
	}

#[partial]
def int_suffix_try_f32 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.f32,
		fail _ => int_suffix_try_f64 (tag "f64" orig) orig
	}

#[partial]
def int_suffix_try_f64 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.f64,
		// No suffix present — defaults to i64, same shape as `vis_parser`
		// always succeeding with a default rather than failing.
		fail _ => success orig NumSuffix.i64
	}

#[partial]
def float_suffix_parser (input : String) : ParseResult NumSuffix :=
	float_suffix_try_f32 (tag "f32" input) input

#[partial]
def float_suffix_try_f32 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.f32,
		fail _ => float_suffix_try_f64 (tag "f64" orig) orig
	}

#[partial]
def float_suffix_try_f64 (r : ParseResult String) (orig : String) : ParseResult NumSuffix :=
	match r {
		success rem _ => success rem NumSuffix.f64,
		fail _ => success orig NumSuffix.f64
	}


// --- Combined numeric literal term (int or float, optional sign/suffix) ---
//
// Handles the full `[-]digits[.digits][suffix]` shape in one parser
// (previously the caller only ever built a bare `Literal.num n
// NumSuffix.i64`, so `33u64` silently mis-parsed as juxtaposed
// application (`app (lit 33) (var "u64")`) and `3.0` mis-parsed through
// the `.`-operator — both wrong ASTs rather than parse failures, the
// worst kind of bug since no `success`/`fail`-only test could catch it).
// The optional leading `-` doubles as this language's only unary-minus
// support (mirrors the Rust reference, which likewise has no general
// unary-negation operator — `num_literal`/`float_literal` both fold an
// optional `-` into the literal itself, rust/core/src/parser.rs) — safe from
// colliding with binary subtraction because this parser only ever runs
// in atom/prefix position (start of an expression, after `(`, `,`,
// `:=`, ...), and the `-` must be immediately followed by a digit with
// no whitespace, so `a - 1` (spaced, the universal style for the infix
// operator) never reaches here as anything but a `fail` that lets the
// caller's operator-parsing fall through correctly.
#[partial]
def numeric_literal (input : String) : ParseResult ParseTerm :=
	numeric_literal_sign (tag "-" input) input

#[partial]
def numeric_literal_sign (r : ParseResult String) (orig : String) : ParseResult ParseTerm :=
	match r {
		success rem _ => numeric_literal_digits rem true,
		fail _ => numeric_literal_digits orig false
	}

// Try a `0x`/`0X` hex prefix before falling back to decimal digits.
#[partial]
def numeric_literal_digits (input : String) (negative : Bool) : ParseResult ParseTerm :=
	numeric_literal_try_hex_lower (tag "0x" input) input negative


#[partial]
def numeric_literal_try_hex_lower (r : ParseResult String) (orig : String) (negative : Bool) : ParseResult ParseTerm :=
	match r {
		success rem _ => numeric_literal_hex_digits rem negative,
		fail _ => numeric_literal_try_hex_upper (tag "0X" orig) orig negative
	}


#[partial]
def numeric_literal_try_hex_upper (r : ParseResult String) (orig : String) (negative : Bool) : ParseResult ParseTerm :=
	match r {
		success rem _ => numeric_literal_hex_digits rem negative,
		fail _ => numeric_literal_decimal_digits orig negative
	}


// Decimal path (unchanged behavior) -- still feeds into the existing
// float-suffix/int-suffix machinery below (numeric_literal_digits_done /
// _try_dot / _frac / etc.).
#[partial]
def numeric_literal_decimal_digits (input : String) (negative : Bool) : ParseResult ParseTerm :=
	numeric_literal_digits_done (number input) negative input


// Hex path -- integers only, no float-dot try (no `0x1.8p3` hex floats).
#[partial]
def numeric_literal_hex_digits (input : String) (negative : Bool) : ParseResult ParseTerm :=
	numeric_literal_hex_digits_done (hex_number input) negative


#[partial]
def numeric_literal_hex_digits_done (r : ParseResult I64) (negative : Bool) : ParseResult ParseTerm :=
	match r {
		success rem n => numeric_literal_hex_int_suffix rem n negative,
		fail e => fail e
	}


#[partial]
def numeric_literal_hex_int_suffix (input : String) (n : I64) (negative : Bool) : ParseResult ParseTerm :=
	match int_suffix_parser input {
		success rem suffix =>
			let value : I64 := if negative then (0 - n) else n in
			success rem (pt_lit  (ParseLiteral.num value suffix)),
		fail e => fail e
	}

#[partial]
def numeric_literal_digits_done (r : ParseResult I64) (negative : Bool) (src : String) : ParseResult ParseTerm :=
	match r {
		success rem n => numeric_literal_try_dot rem n negative src,
		fail e => fail e
	}

/// The float literal's own text is taken from the SOURCE (`src`), not
/// rebuilt from the integer accumulator `n` -- which is what this used
/// to do (`I64.to_string n`), and which is wrong for any integer part
/// that doesn't fit in an `I64`: `100000000000000000000.0` has no
/// `I64` value, so `number` WRAPS (`parse_digits` is a plain
/// `acc * 10 + digit` fold) and the text came out as the wrapped
/// integer's digits, e.g. `7766279631452241920.0`. The literal's text is
/// what `Literal.flt` carries and what the backend parses into the
/// double (`F64.bits_of_string`), so that wrap silently became a
/// different constant -- measured self-hosted, where the same source
/// parses to the right double on the Rust host (whose parser keeps the
/// source text). Slicing the source cannot go wrong the same way: the
/// text IS the literal, whatever its magnitude.
///
/// `int_len` is what `number` consumed = the whole `src` minus what the
/// digits left behind (`rem`), and the sign is re-attached here because
/// the `-` was consumed a level up (see `numeric_literal_decimal_digits`
/// and its hex siblings).
#[partial]
def numeric_literal_try_dot (input : String) (n : I64) (negative : Bool) (src : String) : ParseResult ParseTerm :=
	match tag "." input {
		success rem _ =>
			let int_len : I64 := I64.sub (String.length src) (String.length input) in
			let sign_text : String := if negative then "-" else "" in
			let int_text : String := String.concat sign_text (strip_underscores (String.slice src 0 int_len) 0 "") in
			numeric_literal_frac (take_while_byte is_digit_byte rem) int_text,
		fail _ => numeric_literal_int_suffix input n negative
	}

/// `s` without its `_` digit-group separators, which the number lexer
/// accepts between digits (`is_digit_or_underscore_byte`) but no decimal
/// parser does -- `strtod` stops at one. (The integer path has the same
/// lexer extension and does not handle it: `parse_digits_char` sends
/// `_` through `char_to_digit`, whose fall-through answers 9. Left alone
/// here -- the float text is the only thing this file hands to a decimal
/// parser.)
#[partial]
def strip_underscores (s : String) (i : I64) (acc : String) : String :=
	if I64.beq i (String.length s)
	then acc
	else
		let ch : String := String.slice s i 1 in
		if String.beq "_" ch
		then strip_underscores s (I64.add i 1) acc
		else strip_underscores s (I64.add i 1) (String.concat acc ch)

#[partial]
def numeric_literal_frac (r : ParseResult String) (int_text : String) : ParseResult ParseTerm :=
	match r {
		success rem frac =>
			let text : String := String.concat (String.concat int_text ".") frac in
			numeric_literal_float_suffix rem text,
		fail e => fail e
	}

#[partial]
def numeric_literal_float_suffix (input : String) (text : String) : ParseResult ParseTerm :=
	match float_suffix_parser input {
		success rem suffix => success rem (pt_lit  (ParseLiteral.flt text suffix)),
		fail e => fail e
	}

#[partial]
def numeric_literal_int_suffix (input : String) (n : I64) (negative : Bool) : ParseResult ParseTerm :=
	match int_suffix_parser input {
		success rem suffix =>
			let value : I64 := if negative then (0 - n) else n in
			success rem (pt_lit  (ParseLiteral.num value suffix)),
		fail e => fail e
	}
