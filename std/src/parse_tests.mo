/// Tests for `std::parse` -- the pure-Monad number scanner.
///
/// A separate file because a `#[test]` inside a module re-exported by
/// `std/src/lib.mo` is undiscoverable (AGENTS.md's testing section); this
/// file is not re-exported.
use init::number {}
use std::parse {Parse.i64, Parse.f64}

def parse_test_i64_is (s : String) (want : I64) : Bool :=
    match Parse.i64 s {
        Option.some n => I64.beq n want,
        Option.none => false,
    }

def parse_test_i64_none (s : String) : Bool :=
    match Parse.i64 s {
        Option.some _ => false,
        Option.none => true,
    }

def parse_test_f64_is (s : String) (want : String) : Bool :=
    match Parse.f64 s {
        Option.some v => String.beq (F64.to_string v) want,
        Option.none => false,
    }

def parse_test_f64_none (s : String) : Bool :=
    match Parse.f64 s {
        Option.some _ => false,
        Option.none => true,
    }

// ─── Integers ───

#[test]
def test_parse_i64_zero : Bool :=
    parse_test_i64_is "0" 0i64

#[test]
def test_parse_i64_plain : Bool :=
    parse_test_i64_is "42" 42i64

#[test]
def test_parse_i64_negative : Bool :=
    parse_test_i64_is "-7" (I64.neg 7i64)

#[test]
def test_parse_i64_explicit_plus : Bool :=
    parse_test_i64_is "+7" 7i64

#[test]
def test_parse_i64_max : Bool :=
    parse_test_i64_is "9223372036854775807" 9223372036854775807i64

/// Overflow is `none`, not a wrapped value.
#[test]
def test_parse_i64_overflow_positive : Bool :=
    parse_test_i64_none "9223372036854775808"

/// The magnitude overflows before the sign applies, so even the true I64
/// minimum is refused rather than wrapped.
#[test]
def test_parse_i64_overflow_negative : Bool :=
    parse_test_i64_none "-9223372036854775808"

#[test]
def test_parse_i64_empty : Bool :=
    parse_test_i64_none ""

#[test]
def test_parse_i64_bare_sign : Bool :=
    parse_test_i64_none "-" && parse_test_i64_none "+"

#[test]
def test_parse_i64_trailing_text : Bool :=
    parse_test_i64_none "1a"

#[test]
def test_parse_i64_no_trimming : Bool :=
    parse_test_i64_none " 1" && parse_test_i64_none "1 "

#[test]
def test_parse_i64_rejects_other_radixes : Bool :=
    parse_test_i64_none "0x10" && parse_test_i64_none "0o10"

// ─── Floats ───

#[test]
def test_parse_f64_simple : Bool :=
    parse_test_f64_is "3.14" "3.14"

#[test]
def test_parse_f64_leading_zero_fraction : Bool :=
    parse_test_f64_is "0.5" "0.5"

#[test]
def test_parse_f64_leading_dot : Bool :=
    parse_test_f64_is ".5" "0.5"

#[test]
def test_parse_f64_trailing_dot : Bool :=
    parse_test_f64_is "1." "1"

#[test]
def test_parse_f64_exponent : Bool :=
    parse_test_f64_is "1e3" "1000"

#[test]
def test_parse_f64_negative_exponent : Bool :=
    parse_test_f64_is "1.5e-2" "0.015"

#[test]
def test_parse_f64_signed_exponent : Bool :=
    parse_test_f64_is "-2.5E+1" "-25"

#[test]
def test_parse_f64_accepts_integer_text : Bool :=
    parse_test_f64_is "42" "42"

#[test]
def test_parse_f64_signed_leading_dot : Bool :=
    parse_test_f64_is "+.5" "0.5"

#[test]
def test_parse_f64_rejects_empty : Bool :=
    parse_test_f64_none ""

#[test]
def test_parse_f64_rejects_bare_dot : Bool :=
    parse_test_f64_none "."

#[test]
def test_parse_f64_rejects_empty_exponent : Bool :=
    parse_test_f64_none "1e" && parse_test_f64_none "1e+"

#[test]
def test_parse_f64_rejects_two_dots : Bool :=
    parse_test_f64_none "1.2.3"

#[test]
def test_parse_f64_rejects_text : Bool :=
    parse_test_f64_none "abc" && parse_test_f64_none "1a"

#[test]
def test_parse_f64_rejects_non_finite_spellings : Bool :=
    parse_test_f64_none ".inf" && parse_test_f64_none ".nan"
