/// Numeric SCANNING -- digits to an `I64`, decimal and hex. Nothing here
/// builds a term.
///
/// The AST-producing half (the `u64`/`f32` suffix parsers and
/// `numeric_literal`, which are what turn digits into a `ParseTerm`) lives in
/// `numeric_literal.mo` and imports this one. The cut is deliberate and
/// load-bearing: it is what lets a generic parser substrate reuse `number`
/// without depending on the compiler's AST, which `lang/src/toml.mo` and
/// `lang/src/json.mo` both do. Keep this file free of `lang::types`.

use lib::core {ParseResult, custom, is_empty}
use lib::char_preds {is_digit, is_digit_byte, is_digit_or_underscore_byte, is_hex_digit_byte}
use lib::combinators {tag, take_while_byte}

open ParseResult {fail, success}


// --- Number parser ---

#[partial]
def is_digit_or_underscore (c : String) : Bool :=
	if is_digit c then true
	else String.beq "_" c


#[partial]
pub def number (input : String) : ParseResult I64 :=
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
pub def char_to_digit (c : String) : I64 :=
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
pub def parse_digits (s : String) : I64 :=
	parse_digits_loop s 0


#[partial]
def parse_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_digits_char (String.slice s 0 1) (String.drop 1 s) acc


#[partial]
pub def parse_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_digits_loop rest (I64.add (I64.mul acc 10) (char_to_digit ch))


/// Decimal string -> I64, VALIDATED: `Option.none` for an empty string
/// or one containing anything other than an ASCII digit (no sign, no
/// separators -- same input domain as `parse_digits`, which assumes it).
///
/// Canonical home for callers that need to read a number back out of
/// plain text the compiler itself wrote -- the test runner's result
/// marker file (`lang/codegen/test_driver.mo`, parsed by
/// `cli/src/main.mo`) -- without inheriting the parser combinator's
/// `ParseResult` machinery: this is a plain `String` -> `Option I64`,
/// callable from anywhere `String.slice` is.
pub def parse_i64 (s : String) : Option I64 :=
	if is_empty s
	then Option.none
	else parse_i64_loop s 0

#[partial]
def parse_i64_loop (s : String) (acc : I64) : Option I64 :=
	if is_empty s
	then Option.some acc
	else
		let ch : String := String.slice s 0 1 in
		if is_digit ch
		then parse_i64_loop (String.drop 1 s) (I64.add (I64.mul acc 10) (char_to_digit ch))
		else Option.none


// --- Hex number parser (`0xBADBEEF`, `0XFF`) ---
//
// No `_` digit-grouping — matches the Rust reference parser, which has
// no underscore-grouping support for any numeric literal.

#[partial]
pub def hex_number (input : String) : ParseResult I64 :=
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
pub def char_to_hex_digit (c : String) : I64 :=
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
