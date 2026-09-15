/// Character predicate functions for the self-hosted Monad parser.

use lang.parser.core {kw_list, kw_member}
use std.list {length}

// --- Char predicates ---

#[partial]
def is_digit (c : String) : Bool :=
	if String.beq "0" c then true
	else if String.beq "1" c then true
	else if String.beq "2" c then true
	else if String.beq "3" c then true
	else if String.beq "4" c then true
	else if String.beq "5" c then true
	else if String.beq "6" c then true
	else if String.beq "7" c then true
	else if String.beq "8" c then true
	else String.beq "9" c


#[partial]
def is_alpha_lower (c : String) : Bool :=
	if String.beq "a" c then true
	else if String.beq "b" c then true
	else if String.beq "c" c then true
	else if String.beq "d" c then true
	else if String.beq "e" c then true
	else if String.beq "f" c then true
	else if String.beq "g" c then true
	else if String.beq "h" c then true
	else if String.beq "i" c then true
	else if String.beq "j" c then true
	else if String.beq "k" c then true
	else if String.beq "l" c then true
	else if String.beq "m" c then true
	else false


#[partial]
def is_alpha_lower2 (c : String) : Bool :=
	if String.beq "n" c then true
	else if String.beq "o" c then true
	else if String.beq "p" c then true
	else if String.beq "q" c then true
	else if String.beq "r" c then true
	else if String.beq "s" c then true
	else if String.beq "t" c then true
	else if String.beq "u" c then true
	else if String.beq "v" c then true
	else if String.beq "w" c then true
	else if String.beq "x" c then true
	else if String.beq "y" c then true
	else String.beq "z" c


#[partial]
def is_alpha_upper (c : String) : Bool :=
	if String.beq "A" c then true
	else if String.beq "B" c then true
	else if String.beq "C" c then true
	else if String.beq "D" c then true
	else if String.beq "E" c then true
	else if String.beq "F" c then true
	else if String.beq "G" c then true
	else if String.beq "H" c then true
	else if String.beq "I" c then true
	else if String.beq "J" c then true
	else if String.beq "K" c then true
	else if String.beq "L" c then true
	else if String.beq "M" c then true
	else false


#[partial]
def is_alpha_upper2 (c : String) : Bool :=
	if String.beq "N" c then true
	else if String.beq "O" c then true
	else if String.beq "P" c then true
	else if String.beq "Q" c then true
	else if String.beq "R" c then true
	else if String.beq "S" c then true
	else if String.beq "T" c then true
	else if String.beq "U" c then true
	else if String.beq "V" c then true
	else if String.beq "W" c then true
	else if String.beq "X" c then true
	else if String.beq "Y" c then true
	else String.beq "Z" c


#[partial]
def is_alpha (c : String) : Bool :=
	if is_alpha_lower c then true
	else if is_alpha_lower2 c then true
	else if is_alpha_upper c then true
	else is_alpha_upper2 c


#[partial]
def is_alphanumeric (c : String) : Bool :=
	if is_digit c then true
	else is_alpha c


#[partial]
def is_ident_char (c : String) : Bool :=
	if is_alphanumeric c then true
	else String.beq "_" c


#[partial]
def is_space (c : String) : Bool :=
	if String.beq " " c then true
	else if String.beq "\t" c then true
	else if String.beq "\n" c then true
	else String.beq "\r" c


// --- Hex digit predicate ---

#[partial]
def is_hex_alpha (c : String) : Bool :=
	if String.beq "a" c then true
	else if String.beq "A" c then true
	else if String.beq "b" c then true
	else if String.beq "B" c then true
	else if String.beq "c" c then true
	else if String.beq "C" c then true
	else if String.beq "d" c then true
	else if String.beq "D" c then true
	else if String.beq "e" c then true
	else if String.beq "E" c then true
	else if String.beq "f" c then true
	else String.beq "F" c


#[partial]
def is_hex_digit (c : String) : Bool :=
	if is_digit c then true
	else is_hex_alpha c


// --- Keyword check ---

#[partial]
def is_keyword (s : String) : Bool :=
	kw_member s kw_list


// --- String prefix check ---

def is_prefix (pre : String) (s : String) : Bool :=
	pre == (String.slice s 0 (String.length pre))


// --- Identifier start check ---

#[partial]
def ident_start (c : String) : Bool :=
	if is_alpha c then true
	else String.beq "_" c


// --- Byte-wise siblings -------------------------------------------
//
// The predicates above take a one-character `String`, which is what
// `take_while` (`lang/parser/combinators.mo`) hands them -- and
// producing that string costs a `String.slice` ALLOCATION per input
// character, on top of the `String.beq` chain each predicate then walks.
// Measured in `bench/parser_take_while.mo`: ~3.75us per character for
// `is_space` and roughly double that for `is_ident_char`, whose chain is
// deeper (`is_alphanumeric` -> `is_alpha` -> four helpers).
//
// These siblings take the raw `U8` instead, so `take_while_byte` can
// scan a byte index with `String.get` (already a native returning `U8`)
// and slice exactly once at the token boundary. Comparisons become
// numeric `U8.lt`/`U8.beq` range checks rather than string equality.
//
// Byte-wise is CORRECT for these classes precisely because they are all
// ASCII: a UTF-8 lead byte (>= 0xC0) and a continuation byte (0x80-0xBF)
// both fail every one of them, so a scan stops at the first byte of a
// multi-byte character rather than splitting it. A predicate that must
// ACCEPT non-ASCII cannot use this path and must keep the
// `utf8_char_width`-based `take_while`.
//
// The `String`-taking versions above are kept, not replaced: `take_while`
// remains the general combinator, and `lang/json.mo`/`lang/toml.mo` and
// the string-literal scanner use predicates of their own.

/// Raw byte at `i`, or 0 when out of range. `take_while_byte_at` only
/// calls this after its own bounds check, so the fallback is unreachable
/// there; it exists to keep this total and to keep the scan loop a plain
/// `if`/`else` chain (see `take_while_byte_at`'s own note on why the
/// loop must stay self-tail-recursive without an intervening `match`).
#[partial]
def byte_at (s : String) (i : I64) : U8 :=
	match String.get s i {
		Option.some b => b,
		Option.none => 0u8
	}


/// `' '`, `'\t'`, `'\n'`, `'\r'` -- byte-wise `is_space`.
#[partial]
def is_space_byte (c : U8) : Bool :=
	if U8.beq c 32u8 then true
	else if U8.beq c 10u8 then true
	else if U8.beq c 9u8 then true
	else U8.beq c 13u8


/// `'0'`..`'9'` (48..57) -- byte-wise `is_digit`, a range check instead
/// of that function's ten-way `String.beq` chain.
#[partial]
def is_digit_byte (c : U8) : Bool :=
	if U8.lt c 48u8 then false
	else Bool.not (U8.gt c 57u8)


/// `'A'`..`'Z'` (65..90) or `'a'`..`'z'` (97..122) -- byte-wise
/// `is_alpha`, two range checks instead of four helper chains.
#[partial]
def is_alpha_byte (c : U8) : Bool :=
	if U8.lt c 65u8 then false
	else if Bool.not (U8.gt c 90u8) then true
	else if U8.lt c 97u8 then false
	else Bool.not (U8.gt c 122u8)


#[partial]
def is_alphanumeric_byte (c : U8) : Bool :=
	if is_digit_byte c then true
	else is_alpha_byte c


/// Byte-wise `is_ident_char`: alphanumeric or `'_'` (95).
#[partial]
def is_ident_char_byte (c : U8) : Bool :=
	if is_alphanumeric_byte c then true
	else U8.beq c 95u8


/// `'a'`..`'f'` (97..102) or `'A'`..`'F'` (65..70) -- byte-wise
/// `is_hex_alpha`.
#[partial]
def is_hex_alpha_byte (c : U8) : Bool :=
	if U8.lt c 65u8 then false
	else if Bool.not (U8.gt c 70u8) then true
	else if U8.lt c 97u8 then false
	else Bool.not (U8.gt c 102u8)


/// Byte-wise `is_hex_digit`.
#[partial]
def is_hex_digit_byte (c : U8) : Bool :=
	if is_digit_byte c then true
	else is_hex_alpha_byte c


/// Byte-wise `is_digit_or_underscore` (`lang/parser/number.mo`'s own
/// predicate, byte form kept here beside its siblings).
#[partial]
def is_digit_or_underscore_byte (c : U8) : Bool :=
	if is_digit_byte c then true
	else U8.beq c 95u8
