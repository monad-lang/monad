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
/// One deliberate divergence is pinned here too: a DECIMAL `u64` above
/// i64::MAX is rejected self-hosted ("not writable yet") because the
/// wrapping digit fold cannot recover the true magnitude, while the
/// Rust parser bit-reinterprets a real u64 parse. HEX `u64` needs no
/// such exception — the fold's wrapped payload IS the bit
/// reinterpretation, so `0xFFFFFFFFFFFFFFFFu64` parses on both sides
/// (plan 0.3; lifted when Phase 3's `U64.bits_of_string` native lands).
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
def test_u64_full_range_hex_only : Bool :=
    // Hex u64 above i64::MAX: the wrapped payload is exactly the
    // bit-reinterpretation the Rust parser computes for the same
    // literal, so it parses on both sides.
    String.beq (literal_shape "0xFFFFFFFFFFFFFFFFu64") "num -1 u64"
        && String.beq (literal_shape "0x8000000000000000u64") "num -9223372036854775808 u64"
        // Decimal u64 above i64::MAX: rejected self-hosted until
        // Phase 3 (the plan's one recorded parser divergence).
        && rejected "9223372036854775808u64"
        && rejected "18446744073709551615u64"
        && rejected "18446744073709551616u64"
        // At or below i64::MAX, decimal u64 parses fine.
        && String.beq (literal_shape "9223372036854775807u64") "num 9223372036854775807 u64"

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
