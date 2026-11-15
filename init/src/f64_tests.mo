/// `F64` end to end: the decimal literals, the arithmetic, the
/// comparisons and the two conversions, on BOTH backends.
///
/// Every assertion here is a cross-check, not a restatement: this file
/// runs under the self-hosted runner (compiled code, `runtime.c`'s F64
/// section) and under `monad-rs test` (the Rust evaluator,
/// `rust/core/src/core_native.rs`), so a test that passes is two independent
/// implementations agreeing on the same literal -- which is the whole
/// hazard this family carries, since an `F64` is a bit pattern here and
/// the two sides parse and print it with different libraries (`strtod`
/// plus a shortest-round-trip printer in C, `f64::from_str` plus Rust's
/// own Display on the host).
///
/// The exactness of the assertions is the point: `1.0 / 3.0` is not a
/// third, and `F64.to_string` of it is Rust's "0.3333333333333333", not
/// a rounded "0.3333". A test that only asserted approximate equality
/// would pass just as well on a backend that parsed the literal to the
/// wrong double.
///
/// `+` used to be deliberately absent: `infix (+)` is `HAdd.add`
/// (`init/src/prelude.mo`), which for years had no per-type instance
/// at all -- the generic `[Add A] HAdd A A A` forwarding bridge is
/// unkeyable by the checker's concrete-head instance table, so `+`
/// only ever resolved through `init/src/lib.mo`'s `infix (+) :=
/// I64.add` override, and `1.0 + 2.0` was "type mismatch: `F64` vs.
/// `I64`". With the per-type `HAdd F64 F64 F64` instance
/// (`init/src/number.mo`) and the override gone, `+` is exercised
/// here like `*` is; `h_ops_tests.mo` pins the full operator story.

/// The literal's own VALUE, through the parser: 0x40091EB851EB851F is the
/// double nearest 3.14. Pinned as bits because that is exactly what the
/// backend stores, and it is where a wrong decimal parse would show up
/// (the old `Literal.flt` lowering emitted a constant 0 here, which is
/// also why this is asserted rather than assumed).
#[test]
def test_f64_literal_bits_are_the_nearest_double : Bool :=
    I64.beq (F64.bits_of_string "3.14") 4614253070214989087

/// `+` through the retargeted infix: `HAdd F64 F64 F64`'s instance
/// body is the same native `F64.add` the member test above calls.
#[test]
def test_f64_addition_of_literals : Bool :=
    let sum : F64 := 1.0 + 2.0 in
    let expected : F64 := 3.0 in
    F64.beq sum expected

#[test]
def test_f64_multiplication_of_literals : Bool :=
    let product : F64 := 5.0 * 2.0 in
    let expected : F64 := 10.0 in
    F64.beq product expected

/// IEEE-754 rounding, not decimal arithmetic: `1.0 / 3.0` is the nearest
/// double to a third, and the 16-digit expansion below is what Rust's
/// Display prints for it. This pins that the backend really divides
/// doubles rather than, say, integers with a decimal point tacked on.
#[test]
def test_f64_division_is_ieee754 : Bool :=
    F64.to_string (1.0 / 3.0) == "0.3333333333333333"

#[test]
def test_f64_to_string_of_an_integral_value_has_no_decimal_point : Bool :=
    F64.to_string 100.0 == "100"

#[test]
def test_f64_to_string_of_a_fraction : Bool :=
    F64.to_string 0.5 == "0.5"

#[test]
def test_f64_to_string_of_a_negative_value : Bool :=
    F64.to_string (0.0 - 2.5) == "-2.5"

/// No exponent form: Rust's Display spells a large magnitude out in
/// full, and this backend has to match it character for character.
#[test]
def test_f64_to_string_never_uses_exponent_notation : Bool :=
    F64.to_string 100000000000000000000.0 == "100000000000000000000"

/// A NaN is unequal to itself in both implementations, because both use
/// the hardware comparison rather than a bit-pattern equality.
#[test]
def test_f64_nan_is_not_equal_to_itself : Bool :=
    Bool.not (F64.beq (0.0 / 0.0) (0.0 / 0.0))

#[test]
def test_f64_division_by_zero_is_infinite : Bool :=
    F64.to_string (1.0 / 0.0) == "inf"

#[test]
def test_f64_ordering : Bool :=
    F64.lt 1.0 2.0 && F64.gt 2.0 1.0 && F64.beq 2.0 2.0

/// The same comparisons through the class instances, so the `BOrd`/`BEq`
/// dictionaries are exercised and not only the bare natives.
#[test]
def test_f64_ordering_through_the_instances : Bool :=
    let a : F64 := 1.5 in
    let b : F64 := 2.5 in
    BOrd.lt a b && BOrd.gt b a && BEq.beq a a && Bool.not (BEq.beq a b)

// ─── the bit-pattern pair ────────────────────────────────────────────
//
// `F64.to_bits`/`F64.of_bits` and `F32.to_bits`/`F32.of_bits`
// (`implementations/float-bit-conversions.md`). The patterns below are the
// IEEE-754 values from that plan's own vector table, and every one is
// asserted EXACTLY rather than through `F64.beq`: an approximation would
// pass on a backend that returned a near neighbour, which is the whole
// failure mode a bit-pattern accessor exists to exclude.
//
// The `F32` half is where the trap is. An `F32` payload is the f32-ROUNDED
// value held in a double, so `to_bits` has to narrow through `float` and
// read that pattern -- a raw read of the payload's low four bytes returns
// `1.0f32` as `0x00000000` rather than `0x3F800000`. `test_f32_to_bits_is_
// not_the_payload_low_half` pins the difference, so the two implementations
// cannot both make the same mistake and agree.

/// `1.0` -> `0x3FF0000000000000`.
#[test]
def test_f64_to_bits_of_one : Bool :=
    I64.beq (F64.to_bits 1.0) 0x3FF0000000000000

/// `-0.0` is not `0.0`: the sign bit is the high bit, and the two compare
/// EQUAL, so only the bit pattern can tell them apart -- which is exactly
/// what this accessor is for.
///
/// Two things are load-bearing in the spelling:
///
/// * `neg_zero` is the NEGATIVE ZERO VALUE, written `0.0 / (0.0 - 1.0)`.
///   `0.0 - 0.0` is `+0.0` under IEEE, so the obvious spelling silently
///   tests the wrong thing (it passed as `0` and failed against the sign-bit
///   pattern -- the failure this test was written to catch caught the TEST).
///   There is no `-0.0` literal form and no `F64.neg` native yet.
/// * The PATTERN is `I64.not 0x7FFF...` rather than `0x8000000000000000`,
///   which does not fit in an `I64` literal (the parser rejects it:
///   `unknown declaration`). Complementing the largest positive word is the
///   same bit and reads as "the sign bit alone".
#[test]
def test_f64_to_bits_distinguishes_negative_zero : Bool :=
    let neg_zero : F64 := 0.0 / (0.0 - 1.0) in
    I64.beq (F64.to_bits neg_zero) (I64.not 0x7FFFFFFFFFFFFFFFi64)
        && I64.beq (F64.to_bits 0.0) 0i64
        && F64.beq neg_zero 0.0

/// `1.0 / 0.0` is `+inf`.
#[test]
def test_f64_to_bits_of_positive_infinity : Bool :=
    I64.beq (F64.to_bits (1.0 / 0.0)) 0x7FF0000000000000

/// The smallest positive denormal, whose pattern is the single low bit.
#[test]
def test_f64_to_bits_of_the_smallest_denormal : Bool :=
    I64.beq (F64.to_bits (F64.of_bits 1i64)) 1i64

/// The round trip is total: `of_bits (to_bits x)` is `x` bit for bit, on
/// ordinary values, on both zeroes, and on the exponent edge cases.
#[test]
def test_f64_bits_round_trip : Bool :=
    I64.beq (F64.to_bits (F64.of_bits (F64.to_bits 3.14))) (F64.to_bits 3.14)
        && I64.beq (F64.to_bits (F64.of_bits 0i64)) 0i64
        && I64.beq (F64.to_bits (F64.of_bits (I64.not 0x7FFFFFFFFFFFFFFFi64))) (I64.not 0x7FFFFFFFFFFFFFFFi64)
        && I64.beq (F64.to_bits (F64.of_bits 0x7FF0000000000000i64)) 0x7FF0000000000000i64

/// `+inf` comes back as `+inf` through the pair. Compared against the value
/// `1.0 / 0.0` builds directly rather than against a large literal -- the
/// backend has no exponent form (`1.0e308` is `unknown variable 'e308'`), and
/// `F64.gt inf x` for any finite `x` is the property that matters anyway.
#[test]
def test_f64_of_bits_infinity_is_infinite : Bool :=
    F64.beq (F64.of_bits 0x7FF0000000000000i64) (1.0 / 0.0)
        && F64.gt (F64.of_bits 0x7FF0000000000000i64) (1.0 / 0.000000001)

/// `F32.to_bits 1.0` from the plan's vector table is `0x3F800000`. A literal
/// reaches `F32` through `F64.to_f32`, so the rounding is explicit.
#[test]
def test_f32_to_bits_of_one : Bool :=
    let one : F32 := F64.to_f32 1.0 in
    U32.beq (F32.to_bits one) 0x3F800000u32

/// `-0.0f32` keeps its sign bit. Same `+0.0` trap as the F64 test above:
/// the operand must really be a negative zero.
#[test]
def test_f32_to_bits_distinguishes_negative_zero : Bool :=
    let negz : F32 := F64.to_f32 (0.0 / (0.0 - 1.0)) in
    let zero : F32 := F64.to_f32 0.0 in
    U32.beq (F32.to_bits negz) 0x80000000u32
        && U32.beq (F32.to_bits zero) 0x00000000u32

/// `+inf` as an `F32`.
#[test]
def test_f32_to_bits_of_positive_infinity : Bool :=
    let inf_ : F32 := F64.to_f32 (1.0 / 0.0) in
    U32.beq (F32.to_bits inf_) 0x7F800000u32

/// The smallest positive `F32` denormal: pattern `1`.
#[test]
def test_f32_to_bits_of_the_smallest_denormal : Bool :=
    U32.beq (F32.to_bits (F32.of_bits 1u32)) 1u32

/// `of_bits (to_bits x)` restores the f32 value, so the pair is an inverse
/// on canonical patterns.
#[test]
def test_f32_bits_round_trip : Bool :=
    let x : F32 := F64.to_f32 3.5 in
    let y : F32 := F32.of_bits (F32.to_bits x) in
    F32.beq x y

/// The trap, pinned as a NEGATIVE: the f32 pattern is not the low half of the
/// payload double. `1.0f32`'s payload is `1.0` (`0x3FF0000000000000`), whose
/// low 32 bits are zero -- so a backend that read the payload would answer
/// `0` here, and this test is what makes that a failure rather than an
/// agreeing pair of implementations.
#[test]
def test_f32_to_bits_is_not_the_payload_low_half : Bool :=
    let one : F32 := F64.to_f32 1.0 in
    let pattern := F32.to_bits one in
    U32.beq pattern 0x3F800000u32
        && Bool.not (U32.beq pattern 0x00000000u32)

/// `F32.to_bits` and `F64.to_bits` agree about the value: the f32 pattern
/// widened to a double is the `F32.to_f64` of the same value.
#[test]
def test_f32_bits_and_f64_bits_agree_on_a_round_tripped_value : Bool :=
    let one : F32 := F64.to_f32 1.0 in
    F64.beq (F32.to_f64 (F32.of_bits (F32.to_bits one))) (F64.of_bits (F64.to_bits 1.0))
