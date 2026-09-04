/// Number parsing functions for the self-hosted Monad parser.

use lang.types {NumSuffix, Term}
use lang.parser.core {ParseResult, custom, fail, is_empty, success}
use lang.parser.char_preds {is_digit, is_digit_byte, is_digit_or_underscore_byte, is_hex_digit_byte}
use lang.parser.combinators {tag, take_while_byte}

open ParseResult {fail, success}


// --- Number parser ---

#[partial]
def is_digit_or_underscore (c : String) : Bool :=
	if is_digit c then true
	else String.beq "_" c


#[partial]
def number (input : String) : ParseResult I64 :=
	number_body (take_while_byte is_digit_or_underscore_byte input)


#[partial]
def number_body (r : ParseResult String) : ParseResult I64 :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected number" rem)
			else number_parse out rem,
		fail e => fail e
	}


#[partial]
def number_parse (s : String) (rem : String) : ParseResult I64 :=
	if is_empty s
	then fail (ParseError.custom "empty number" rem)
	else if is_digit (String.slice s 0 1)
	then success rem (parse_digits s)
	else fail (ParseError.custom "number must start with digit" rem)


// --- Number parsing helpers ---

#[partial]
def char_to_digit (c : String) : I64 :=
	if String.beq "0" c then 0
	else if String.beq "1" c then 1
	else if String.beq "2" c then 2
	else if String.beq "3" c then 3
	else if String.beq "4" c then 4
	else if String.beq "5" c then 5
	else if String.beq "6" c then 6
	else if String.beq "7" c then 7
	else if String.beq "8" c then 8
	else 9


#[partial]
def parse_digits (s : String) : I64 :=
	parse_digits_loop s 0


#[partial]
def parse_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_digits_char (String.slice s 0 1) (String.drop 1 s) acc


#[partial]
def parse_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_digits_loop rest (I64.add (I64.mul acc 10) (char_to_digit ch))


// --- Hex number parser (`0xBADBEEF`, `0XFF`) ---
//
// No `_` digit-grouping — matches the Rust reference parser, which has
// no underscore-grouping support for any numeric literal.

#[partial]
def hex_number (input : String) : ParseResult I64 :=
	hex_number_body (take_while_byte is_hex_digit_byte input)


#[partial]
def hex_number_body (r : ParseResult String) : ParseResult I64 :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected hex digits" rem)
			else success rem (parse_hex_digits out),
		fail e => fail e
	}


// --- Hex number parsing helpers ---

#[partial]
def char_to_hex_digit (c : String) : I64 :=
	if is_digit c then char_to_digit c
	else char_to_hex_digit_alpha c


#[partial]
def char_to_hex_digit_alpha (c : String) : I64 :=
	if String.beq "a" c then 10
	else if String.beq "A" c then 10
	else if String.beq "b" c then 11
	else if String.beq "B" c then 11
	else if String.beq "c" c then 12
	else if String.beq "C" c then 12
	else if String.beq "d" c then 13
	else if String.beq "D" c then 13
	else if String.beq "e" c then 14
	else if String.beq "E" c then 14
	else 15 // "f" / "F" -- is_hex_digit already validated c


#[partial]
def parse_hex_digits (s : String) : I64 :=
	parse_hex_digits_loop s 0


#[partial]
def parse_hex_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_hex_digits_char (String.slice s 0 1) (String.drop 1 s) acc


#[partial]
def parse_hex_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_hex_digits_loop rest (I64.add (I64.mul acc 16) (char_to_hex_digit ch))


// --- Numeric literal suffixes (`33u64`, `3.0f32`) ---
//
// Mirrors the Rust reference's `num_suffix_parser`/`float_suffix_parser`
// (core/src/parser.rs): a suffix must immediately follow the digits with
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
// optional `-` into the literal itself, core/src/parser.rs) — safe from
// colliding with binary subtraction because this parser only ever runs
// in atom/prefix position (start of an expression, after `(`, `,`,
// `:=`, ...), and the `-` must be immediately followed by a digit with
// no whitespace, so `a - 1` (spaced, the universal style for the infix
// operator) never reaches here as anything but a `fail` that lets the
// caller's operator-parsing fall through correctly.
#[partial]
def numeric_literal (input : String) : ParseResult Term :=
	numeric_literal_sign (tag "-" input) input

#[partial]
def numeric_literal_sign (r : ParseResult String) (orig : String) : ParseResult Term :=
	match r {
		success rem _ => numeric_literal_digits rem true,
		fail _ => numeric_literal_digits orig false
	}

// Try a `0x`/`0X` hex prefix before falling back to decimal digits.
#[partial]
def numeric_literal_digits (input : String) (negative : Bool) : ParseResult Term :=
	numeric_literal_try_hex_lower (tag "0x" input) input negative


#[partial]
def numeric_literal_try_hex_lower (r : ParseResult String) (orig : String) (negative : Bool) : ParseResult Term :=
	match r {
		success rem _ => numeric_literal_hex_digits rem negative,
		fail _ => numeric_literal_try_hex_upper (tag "0X" orig) orig negative
	}


#[partial]
def numeric_literal_try_hex_upper (r : ParseResult String) (orig : String) (negative : Bool) : ParseResult Term :=
	match r {
		success rem _ => numeric_literal_hex_digits rem negative,
		fail _ => numeric_literal_decimal_digits orig negative
	}


// Decimal path (unchanged behavior) -- still feeds into the existing
// float-suffix/int-suffix machinery below (numeric_literal_digits_done /
// _try_dot / _frac / etc.).
#[partial]
def numeric_literal_decimal_digits (input : String) (negative : Bool) : ParseResult Term :=
	numeric_literal_digits_done (number input) negative


// Hex path -- integers only, no float-dot try (no `0x1.8p3` hex floats).
#[partial]
def numeric_literal_hex_digits (input : String) (negative : Bool) : ParseResult Term :=
	numeric_literal_hex_digits_done (hex_number input) negative


#[partial]
def numeric_literal_hex_digits_done (r : ParseResult I64) (negative : Bool) : ParseResult Term :=
	match r {
		success rem n => numeric_literal_hex_int_suffix rem n negative,
		fail e => fail e
	}


#[partial]
def numeric_literal_hex_int_suffix (input : String) (n : I64) (negative : Bool) : ParseResult Term :=
	match int_suffix_parser input {
		success rem suffix =>
			let value : I64 := if negative then I64.sub 0 n else n in
			success rem (Term.lit (Literal.num value suffix)),
		fail e => fail e
	}

#[partial]
def numeric_literal_digits_done (r : ParseResult I64) (negative : Bool) : ParseResult Term :=
	match r {
		success rem n => numeric_literal_try_dot rem n negative,
		fail e => fail e
	}

#[partial]
def numeric_literal_try_dot (input : String) (n : I64) (negative : Bool) : ParseResult Term :=
	match tag "." input {
		success rem _ => numeric_literal_frac (take_while_byte is_digit_byte rem) n negative,
		fail _ => numeric_literal_int_suffix input n negative
	}

#[partial]
def numeric_literal_frac (r : ParseResult String) (n : I64) (negative : Bool) : ParseResult Term :=
	match r {
		success rem frac =>
			let sign_text : String := if negative then "-" else "" in
			let int_text : String := String.concat sign_text (I64.to_string n) in
			let dot_text : String := String.concat int_text "." in
			let text : String := String.concat dot_text frac in
			numeric_literal_float_suffix rem text,
		fail e => fail e
	}

#[partial]
def numeric_literal_float_suffix (input : String) (text : String) : ParseResult Term :=
	match float_suffix_parser input {
		success rem suffix => success rem (Term.lit (Literal.flt text suffix)),
		fail e => fail e
	}

#[partial]
def numeric_literal_int_suffix (input : String) (n : I64) (negative : Bool) : ParseResult Term :=
	match int_suffix_parser input {
		success rem suffix =>
			let value : I64 := if negative then I64.sub 0 n else n in
			success rem (Term.lit (Literal.num value suffix)),
		fail e => fail e
	}
