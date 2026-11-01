/// Numeric LITERALS: digits plus an optional suffix, lowered to a
/// `ParseTerm`. The AST-producing half of what used to be one `number.mo`.
///
/// Split out so `number.mo` -- the digit scanner this file calls -- can stay
/// free of `lang::types` and be reused by a parser substrate that knows
/// nothing about terms. Everything here is the opposite: `NumSuffix`,
/// `ParseTerm` and `pt_lit` are the point.

use lang::types {NumSuffix, ParseTerm, flt, num, pt_lit}
use parsec::core {ParseResult, custom, is_empty}
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
// no intervening whitespace, and int literals accept all ten suffixes —
// but integer digits with an `f32`/`f64` suffix build a FLOAT literal
// (`33f64` is `33.0f64`; the digits' text is what `ParseLiteral.flt`
// carries, for the backend to parse) while float literals (written with
// a `.`) accept only `f32`/`f64`.

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


// --- Literal validation (Phase 0, mirrors rust/core/src/parser.rs) ---
//
// The canonical-payload gate: a literal is either in range for its
// suffix or a parse failure — never a silently masked, non-canonical
// payload. The Rust side bounds-checks exact parses (i64/u64::from_str,
// u64::from_str_radix); here the scanner folds `acc * 10 + digit` in
// wrapping I64 arithmetic (parsec/number.mo), so the bounds are
// recovered from the digit count:
// - up to 18 decimal digits can never wrap (10^18 < i64::MAX), so the
//   payload is the true value and the per-width check is exact;
// - 19 digits wrapped past i64::MAX iff the payload went negative
//   (positive literal) or past i64::MIN iff it went positive (negative
//   literal) — both detected on the payload's sign alone;
// - 20+ digits are rejected outright: only `u64` could theoretically
//   hold them, and a `u64` above i64::MAX is not writable self-hosted
//   until Phase 3's `U64.bits_of_string` native
//   (plans/implementations/true-numeric-types.md 0.3) — a clear error,
//   strictly better than the silent wrap-to-garbage of the old parser.

def unsigned_suffix (suffix : NumSuffix) : Bool :=
	match suffix {
		NumSuffix.u8 => true, NumSuffix.u16 => true, NumSuffix.u32 => true, NumSuffix.u64 => true,
		_ => false,
	}

def i64_lte (a b : I64) : Bool :=
	I64.lt a b || I64.beq a b

/// Same idiom as `core_eval.mo`'s `i64_min` — the literal
/// `-9223372036854775808` is not writable in expression position.
def i64_min : I64 :=
	I64.sub (I64.sub 0 9223372036854775807) 1

/// Per-width range check on a FINAL value (sign already folded in) —
/// the self-hosted twin of `int_fits_suffix` (rust/core/src/parser.rs).
def int_value_fits (v : I64) (suffix : NumSuffix) : Bool :=
	match suffix {
		NumSuffix.i8 => i64_lte (I64.sub 0 128) v && i64_lte v 127,
		NumSuffix.i16 => i64_lte (I64.sub 0 32768) v && i64_lte v 32767,
		NumSuffix.i32 => i64_lte (I64.sub 0 2147483648) v && i64_lte v 2147483647,
		NumSuffix.i64 => true,
		NumSuffix.u8 => i64_lte 0 v && i64_lte v 255,
		NumSuffix.u16 => i64_lte 0 v && i64_lte v 65535,
		NumSuffix.u32 => i64_lte 0 v && i64_lte v 4294967295,
		// Any payload is a valid u64 bit pattern; which payloads are
		// REACHABLE is the rejection gate's job, not this check's.
		NumSuffix.u64 => true,
		// Unreachable: integer digits with a float suffix route to
		// `ParseLiteral.flt` before validation runs.
		NumSuffix.f32 => true, NumSuffix.f64 => true,
	}

/// The decimal gate: `Option.some msg` rejects the literal with `msg`,
/// `Option.none` accepts it. `digit_len` counts the underscore-stripped
/// digits, sign excluded.
def int_literal_rejection (negative : Bool) (digit_len : I64) (value : I64) (suffix : NumSuffix) : Option String :=
	if negative && unsigned_suffix suffix
	then Option.some "negative literal cannot have an unsigned suffix"
	else if I64.gt digit_len 19
	then Option.some "integer literal too large"
	else if I64.beq digit_len 19 && int_payload_wrapped negative value
	then int_wrap_rejection suffix
	else if int_value_fits value suffix
	then Option.none
	else Option.some "integer literal out of range for its suffix"

/// 19 digits folded past the i64 boundary: a positive literal's payload
/// wrapped negative, a negative literal's wrapped positive.
def int_payload_wrapped (negative : Bool) (value : I64) : Bool :=
	if negative then I64.gt value 0 else I64.lt value 0

def int_wrap_rejection (suffix : NumSuffix) : Option String :=
	match suffix {
		NumSuffix.u64 => Option.some "u64 literal above i64::MAX is not writable self-hosted yet",
		_ => Option.some "integer literal out of range for its suffix",
	}

/// The hex gate, same shape as `int_literal_rejection`. `hex_len` counts
/// hex digits: more than 16 cannot fit any width (u64::MAX is 16 digits)
/// and the fold has already wrapped past the true value. `n` is the
/// folded magnitude — `n < 0` means the true magnitude is at least 2^63.
def hex_literal_rejection (negative : Bool) (hex_len : I64) (n : I64) (suffix : NumSuffix) : Option String :=
	if negative && unsigned_suffix suffix
	then Option.some "negative hex literal cannot have an unsigned suffix"
	else if I64.gt hex_len 16
	then Option.some "hex literal too large"
	else if hex_magnitude_fits negative n suffix
	then Option.none
	else Option.some "hex literal out of range for its suffix"

def hex_magnitude_fits (negative : Bool) (n : I64) (suffix : NumSuffix) : Bool :=
	if I64.lt n 0
	then
		// True magnitude >= 2^63: valid only as a positive u64 (the
		// payload is exactly the bit-reinterpretation the Rust side
		// computes) or as -0x8000000000000000 (i64::MIN).
		match suffix {
			NumSuffix.u64 => Bool.not negative,
			NumSuffix.i64 => negative && I64.beq n i64_min,
			_ => false,
		}
	else
		// n is the exact magnitude.
		match suffix {
			NumSuffix.i8 => i64_lte n (if negative then 128 else 127),
			NumSuffix.i16 => i64_lte n (if negative then 32768 else 32767),
			NumSuffix.i32 => i64_lte n (if negative then 2147483648 else 2147483647),
			NumSuffix.i64 => true,
			NumSuffix.u8 => i64_lte n 255,
			NumSuffix.u16 => i64_lte n 65535,
			NumSuffix.u32 => i64_lte n 4294967295,
			NumSuffix.u64 => true,
			// Unreachable: every f32/f64 character is a hex digit, so
			// the digit scan swallows the suffix before it could ever
			// be read as one (same as the Rust side).
			NumSuffix.f32 => false, NumSuffix.f64 => false,
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
	numeric_literal_hex_digits_done (hex_number input) negative input


#[partial]
def numeric_literal_hex_digits_done (r : ParseResult I64) (negative : Bool) (orig : String) : ParseResult ParseTerm :=
	match r {
		success rem n => numeric_literal_hex_int_suffix rem n negative orig,
		fail e => fail e
	}


#[partial]
def numeric_literal_hex_int_suffix (input : String) (n : I64) (negative : Bool) (orig : String) : ParseResult ParseTerm :=
	match int_suffix_parser input {
		success rem suffix =>
			let hex_len : I64 := I64.sub (String.length orig) (String.length input) in
			match hex_literal_rejection negative hex_len n suffix {
				Option.some msg => fail (ParseError.custom msg rem),
				Option.none =>
					let value : I64 := if negative then (0 - n) else n in
					success rem (pt_lit  (ParseLiteral.num value suffix)),
			},
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
		fail _ =>
			// Same slicing the dot branch does: the int path needs the
			// source text too (float-suffix routing carries it, and the
			// overflow gate counts its digits — the folded `n` alone
			// cannot tell a wrapped payload from a true one).
			let int_len : I64 := I64.sub (String.length src) (String.length input) in
			let sign_text : String := if negative then "-" else "" in
			let int_text : String := String.concat sign_text (strip_underscores (String.slice src 0 int_len) 0 "") in
			numeric_literal_int_suffix input n negative int_text
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
def numeric_literal_int_suffix (input : String) (n : I64) (negative : Bool) (int_text : String) : ParseResult ParseTerm :=
	match int_suffix_parser input {
		success rem suffix => numeric_literal_int_route rem n negative int_text suffix,
		fail e => fail e
	}

/// Integer digits with a float suffix are a FLOAT literal (`33f64` is
/// `33.0f64`), mirroring the Rust reference — a `Num` tagged with a
/// float suffix was unreadable by every float consumer. The digits'
/// source text (sign attached, underscores stripped) is exactly what
/// `ParseLiteral.flt` carries for the backend to parse.
#[partial]
def numeric_literal_int_route (rem : String) (n : I64) (negative : Bool) (int_text : String) (suffix : NumSuffix) : ParseResult ParseTerm :=
	match suffix {
		NumSuffix.f32 => success rem (pt_lit  (ParseLiteral.flt int_text NumSuffix.f32)),
		NumSuffix.f64 => success rem (pt_lit  (ParseLiteral.flt int_text NumSuffix.f64)),
		_ =>
			let value : I64 := if negative then (0 - n) else n in
			let digit_len : I64 := I64.sub (String.length int_text) (if negative then 1 else 0) in
			match int_literal_rejection negative digit_len value suffix {
				Option.some msg => fail (ParseError.custom msg rem),
				Option.none => success rem (pt_lit  (ParseLiteral.num value suffix)),
			},
	}
