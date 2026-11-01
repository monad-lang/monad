/// Numeric literal validation parity between the two compilers' PARSERS.
///
/// Phase 0 of true-numeric-types (plans/implementations/) made every
/// integer literal either in range for its suffix or a parse failure —
/// the canonical-payload gate — in BOTH `rust/core/src/parser.rs`
/// (`num_literal`/`hex_literal`) and its self-hosted twin
/// (`lib/parser/numeric_literal.mo`). These tests exercise the
/// SELF-HOSTED parser functions directly (interpreted by whichever host
/// runs `monad test`), so they pin the Monad-level gate logic, not the
/// Rust parser — whose own boundary cases live in
/// `rust/core/src/parser/test/numbers.rs`.
///
/// A decimal `u64` above i64::MAX parses on both sides now: the Rust
/// parser bit-reinterprets a real u64 parse, and the self-hosted
/// parser's wrapping digit fold is ALREADY the exact u64 bit pattern
/// (mod 2^64), with only the range decided separately — by digit
/// count, since 10^19 < u64::MAX and a 20-digit text fits only up to
/// `u64::MAX` (the last true parser divergence, lifted in Phase 3.4;
/// see `int_overflow_rejection`).
/// HEX `u64` always worked this way — the fold's wrapped payload IS
/// the bit reinterpretation, so `0xFFFFFFFFFFFFFFFFu64` and its
/// decimal spelling agree.
///
/// Integer digits with an `f32`/`f64` suffix build a FLOAT literal on
/// both sides (`33f64` is `33.0f64`); the self-hosted `ParseLiteral.flt`
/// carries the source text, so these tests compare TEXT, not a parsed
/// double (the backend owns text -> bits, including f32 rounding).
use lib::parser::numeric_literal {numeric_literal}
use lib::types {NumSuffix, ParseLiteral, ParseTerm, ParseTermKind}
use parsec::core {ParseResult}

def suffix_name (s : NumSuffix) : String :=
    match s {
        NumSuffix.i8 => "i8", NumSuffix.i16 => "i16", NumSuffix.i32 => "i32", NumSuffix.i64 => "i64",
        NumSuffix.u8 => "u8", NumSuffix.u16 => "u16", NumSuffix.u32 => "u32", NumSuffix.u64 => "u64",
        NumSuffix.f32 => "f32", NumSuffix.f64 => "f64",
    }

/// `true` when `numeric_literal` REJECTS `src` (any fail, including the
/// range/overflow gates).
def rejected (src : String) : Bool :=
    match numeric_literal src {
        ParseResult.fail _ => Bool.true,
        ParseResult.success _ _ => Bool.false,
    }

/// The shape a literal parses to: `num <value> <suffix>`,
/// `flt <text> <suffix>`, or `<rejected>`/`<other>` markers for
/// mismatched shapes.
def literal_shape (src : String) : String :=
    match numeric_literal src {
        ParseResult.fail _ => "<rejected>",
        ParseResult.success _ t =>
            match t.kind {
                ParseTermKind.lit l =>
                    match l {
                        ParseLiteral.num v suffix =>
                            String.concat "num " (String.concat (I64.to_string v) (String.concat " " (suffix_name suffix))),
                        ParseLiteral.flt text suffix =>
                            String.concat "flt " (String.concat text (String.concat " " (suffix_name suffix))),
                        _ => "<other>",
                    },
                _ => "<not-a-lit>",
            },
    }

// ─── Range validation: boundaries parse, one-past rejects ───────────

#[test]
def test_width_boundaries_parse : Bool :=
    String.beq (literal_shape "100u8") "num 100 u8"
        && String.beq (literal_shape "127i8") "num 127 i8"
        && String.beq (literal_shape "-128i8") "num -128 i8"
        && String.beq (literal_shape "65535u16") "num 65535 u16"
        && String.beq (literal_shape "4294967295u32") "num 4294967295 u32"
        && String.beq (literal_shape "0xFFu8") "num 255 u8"
        && String.beq (literal_shape "0x7Fi8") "num 127 i8"
        && String.beq (literal_shape "-0x80i8") "num -128 i8"
        && String.beq (literal_shape "-0x10") "num -16 i64"
        && String.beq (literal_shape "-9223372036854775808") "num -9223372036854775808 i64"

#[test]
def test_out_of_range_rejected : Bool :=
    rejected "300u8"
        && rejected "128i8"
        && rejected "-129i8"
        && rejected "65536u16"
        && rejected "2147483648i32"
        && rejected "0x100u8"
        && rejected "0x80i8"
        && rejected "0x10000u16"
        && rejected "9223372036854775808"
        && rejected "9223372036854775808i64"
        // 2^63 as a bare positive hex or decimal wraps the fold; the
        // gate must not mistake the wrapped payload for a value.
        && rejected "0x8000000000000000"
        // 17 hex digits cannot fit any width.
        && rejected "0x1FFFFFFFFFFFFFFFFu64"

#[test]
def test_i64_min_hex_boundary : Bool :=
    // -2^63 is writable hex (the fold keeps the exact payload), and
    // the negative-i64 gate accepts exactly it.
    String.beq (literal_shape "-0x8000000000000000") "num -9223372036854775808 i64"
        && rejected "-0x8000000000000001"

#[test]
def test_negative_unsigned_rejected : Bool :=
    rejected "-1u8"
        && rejected "-1u64"
        && rejected "-0u8"
        && rejected "-0x1u8"
        && rejected "-0xFFu32"
        && String.beq (literal_shape "-5i32") "num -5 i32"

#[test]
def test_u64_full_range : Bool :=
    // Hex u64 above i64::MAX: the wrapped payload is exactly the
    // bit-reinterpretation the Rust parser computes for the same
    // literal, so it parses on both sides.
    String.beq (literal_shape "0xFFFFFFFFFFFFFFFFu64") "num -1 u64"
        && String.beq (literal_shape "0x8000000000000000u64") "num -9223372036854775808 u64"
        // Decimal u64 above i64::MAX: the wrapping fold is already the
        // exact bit pattern, so the decimal and hex spellings of the
        // same value agree (19 digits folded past i64::MAX, then the
        // 20-digit boundary, then u64::MAX itself).
        && String.beq (literal_shape "9223372036854775808u64") "num -9223372036854775808 u64"
        && String.beq (literal_shape "18446744073709551615u64") "num -1 u64"
        // Leading zeros do not fake a digit count: 21 characters, 19
        // true digits, an ordinary in-range value.
        && String.beq (literal_shape "009223372036854775807u64") "num 9223372036854775807 u64"
        // One past u64::MAX, in 19 and 20 digits, still rejects.
        && rejected "18446744073709551616u64"
        && rejected "118446744073709551615u64"
        // At or below i64::MAX, decimal u64 parses fine.
        && String.beq (literal_shape "9223372036854775807u64") "num 9223372036854775807 u64"

#[test]
def test_leading_zeros_are_not_significant : Bool :=
    // The Rust parser's exact parses (`str::parse`, `from_str_radix`)
    // accept zero padding at any length; the overflow gates bound on the
    // SIGNIFICANT digit count, so a zero-padded literal parses to the
    // same payload as its unpadded spelling at every width.
    String.beq (literal_shape "00000000000000000042") "num 42 i64"
        && String.beq (literal_shape "000000000000000000000") "num 0 i64"
        && String.beq (literal_shape "0000000000000000000255u8") "num 255 u8"
        && String.beq (literal_shape "-00000000000000000000009223372036854775808") "num -9223372036854775808 i64"
        && String.beq (literal_shape "0x00000000000000001") "num 1 i64"
        && String.beq (literal_shape "0x0000FFFFFFFFFFFFFFFFu64") "num -1 u64"
        // Padding does not hide a real overflow either.
        && rejected "0009223372036854775808"
        && rejected "0x00001FFFFFFFFFFFFFFFFu64"

// ─── Integer digits with a float suffix are a FLOAT literal ─────────

#[test]
def test_int_digits_float_suffix_routes_to_flt : Bool :=
    String.beq (literal_shape "33f64") "flt 33 f64"
        && String.beq (literal_shape "33f32") "flt 33 f32"
        && String.beq (literal_shape "-5f64") "flt -5 f64"

#[test]
def test_dotted_float_literals_carry_text : Bool :=
    String.beq (literal_shape "0.5f32") "flt 0.5 f32"
        && String.beq (literal_shape "0.1f64") "flt 0.1 f64"
        && String.beq (literal_shape "3.14") "flt 3.14 f64"
