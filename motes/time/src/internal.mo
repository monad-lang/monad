/// Package-private helpers shared by the `time` modules: floor arithmetic
/// (the prelude has no `I64` modulo and `I64.div` truncates toward zero),
/// zero-padding for formatting, and the fixed-width digit scanners ISO-8601
/// needs.
///
/// Nothing in this file is `pub`; `lib.mo` re-exports only the public API.

use parsec::core {ParseError, ParseResult}
use parsec::combinators {tag}
open ParseResult {fail, success}

/// Floor division for a possibly-negative dividend; requires `b > 0`.
def i64_floor_div (a b : I64) : I64 :=
    let q := a / b in
    let r := a - q * b in
    if r < 0 then q - 1 else q

/// Floor modulo for a possibly-negative dividend; requires `b > 0`.
def i64_floor_mod (a b : I64) : I64 :=
    let r := a - (a / b) * b in
    if r < 0 then r + b else r

/// Non-negative modulo; requires `a >= 0` and `b > 0`. Kept distinct from
/// `i64_floor_mod` so `Date.is_leap_year` never reads as if it needed floor
/// semantics for an input it can never see.
def i64_mod_pos (a b : I64) : I64 :=
    let r := a - (a / b) * b in
    if r < 0 then r + b else r

/// Left-pad `n` to `width` digits. Callers only pass values that fit
/// (`pad2` for date/time fields, `pad4` for years, `pad9` for nanoseconds).
def pad_zeros (n : I64) (width : I64) : String :=
    let s := I64.to_string n in
    String.concat (String.repeat "0" (width - String.length s)) s

def pad2 (n : I64) : String := pad_zeros n 2

def pad4 (n : I64) : String := pad_zeros n 4

def pad9 (n : I64) : String := pad_zeros n 9

/// Drop trailing `0`s from a fixed-width digit string, never below one
/// digit. `Show Time` uses this so `.123` prints three digits, not nine,
/// while `.1` and `.123456789` both still round-trip.
#[partial]
def trim_trailing_zeros (s : String) : String :=
    let n := String.length s in
    if n > 1 && String.slice s (n - 1) 1 == "0"
    then trim_trailing_zeros (String.slice s 0 (n - 1))
    else s

def is_digit_char (c : String) : Bool :=
    if c == "0" then true
    else if c == "1" then true
    else if c == "2" then true
    else if c == "3" then true
    else if c == "4" then true
    else if c == "5" then true
    else if c == "6" then true
    else if c == "7" then true
    else if c == "8" then true
    else c == "9"

def char_to_digit (c : String) : I64 :=
    if c == "0" then 0
    else if c == "1" then 1
    else if c == "2" then 2
    else if c == "3" then 3
    else if c == "4" then 4
    else if c == "5" then 5
    else if c == "6" then 6
    else if c == "7" then 7
    else if c == "8" then 8
    else 9

/// 10^e for the small non-negative exponents the fraction scanner uses.
#[partial]
def pow10 (e : I64) : I64 :=
    if e == 0 then 1 else 10 * pow10 (e - 1)

/// Consume exactly `n` decimal digits. Fails without over-consuming if
/// fewer than `n` digits are available or a non-digit appears first.
#[partial]
def take_n_digits (n : I64) (input : String) : ParseResult I64 :=
    take_n_digits_go n input 0

#[partial]
def take_n_digits_go (remaining : I64) (input : String) (acc : I64) : ParseResult I64 :=
    if remaining == 0
    then success input acc
    else if String.is_empty input
    then fail (ParseError.custom "expected digit" input)
    else
        let ch := String.slice input 0 1 in
        if is_digit_char ch
        then take_n_digits_go (remaining - 1) (String.drop 1 input) (acc * 10 + char_to_digit ch)
        else fail (ParseError.custom "expected digit" input)

/// Accumulate a run of fractional-second digits. The i-th digit is placed at
/// `10^(8-i)`; anything past the ninth is consumed but not accumulated, so
/// any digit count parses and `.123` means 123000000 nanoseconds.
#[partial]
def fraction_digits_go (input : String) (index : I64) (acc : I64) : ParseResult I64 :=
    if String.is_empty input
    then success input acc
    else
        let ch := String.slice input 0 1 in
        if is_digit_char ch
        then
            let next :=
                if index < 9
                then acc + char_to_digit ch * pow10 (8 - index)
                else acc
            in
            fraction_digits_go (String.drop 1 input) (index + 1) next
        else success input acc

/// `"." digits+` -> nanoseconds. Fails on a bare `.` (no digits), leaving the
/// caller's remainder intact.
def parse_fraction (input : String) : ParseResult I64 :=
    match tag "." input {
        success rem _ =>
            if String.is_empty rem
            then fail (ParseError.custom "expected digit after '.'" rem)
            else
                let ch := String.slice rem 0 1 in
                if is_digit_char ch
                then fraction_digits_go rem 0 0
                else fail (ParseError.custom "expected digit after '.'" rem),
        fail e => fail e
    }
