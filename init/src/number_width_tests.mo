/// Width-correct arithmetic end to end, for every integer width and the
/// f32 chain, on both backends.
///
/// Phase 1 of true-numeric-types: the reference interpreter used to
/// compute every integer op on the raw unmasked i64 payload and tag the
/// result `I64` (only `U32` was width-correct, because SHA-256 forced
/// it), and `F32` arithmetic computed in f64. These assertions pin the
/// fixed semantics -- each one is chosen to DISCRIMINATE, so it fails on
/// the old behavior rather than passing by symmetry:
///
///   * every wraparound answer (100+100 = -56 in i8) is wrong in 64-bit
///     arithmetic, so a masked two's-complement result is the only way
///     to pass;
///   * `U64.lt i64::MAX u64::MAX` is false under signed compare (the
///     old generic path) and true under unsigned -- and both literals
///     are now writable, since Phase 0 made `0xFFFFFFFFFFFFFFFFu64`
///     parse (hex folds to the exact bit reinterpretation);
///   * `U64.mod u64::MAX 10` is 5 unsigned and -1 signed;
///   * `0.1f32 + 0.2f32 == 0.3f32` holds in f32 but NOT in f64 (the
///     f64 sum is 0.30000000000000004), so it pins f32 computation
///     specifically, and the `F64` twin below pins that f64 was not
///     "fixed" by rounding through f32;
///   * `F32.to_string 0.1f32` is "0.1" only when the payload is printed
///     as an f32 -- the raw f64 payload prints as "0.10000000149011612";
///   * `x / 0 == 0` for every width, the ledger's unified convention --
///     `u32_div` used to hard-error.
///
/// Calls are direct members (`I8.add`, not `+`): `infix (+)` is
/// `HAdd.add`, whose forwarding instance both checkers currently resolve
/// to the `I64` instance for every other carrier (see `f64_tests.mo`'s
/// header for that pre-existing resolution gap). `==`/`<` are fine --
/// `BEq`/`BOrd` have concrete per-width instances.
///
/// Cross-checked like `number_tests.mo` and `f64_tests.mo`: the file
/// runs under `monad-rs test` (the Rust evaluator) and, once Phase 2
/// wires the missing evaluator arms, under the self-hosted runner too.
#[test]
def test_i8_add_wraps : Bool := I8.add 100i8 100i8 == -56i8

#[test]
def test_i8_add_boundary_wraps_to_min : Bool := I8.add 127i8 1i8 == -128i8

#[test]
def test_i8_mul_wraps_to_zero : Bool := I8.mul 16i8 16i8 == 0i8

#[test]
def test_i8_sub_wraps : Bool := I8.sub -128i8 1i8 == 127i8

#[test]
def test_i8_lt_is_signed : Bool := I8.lt (I8.add 100i8 100i8) 0i8

#[test]
def test_i8_div_by_zero_is_zero : Bool := I8.div 5i8 0i8 == 0i8

#[test]
def test_i16_mul_wraps_negative : Bool := I16.mul 200i16 200i16 == -25536i16

#[test]
def test_i32_add_boundary_wraps_to_min : Bool := I32.add 2147483647i32 1i32 == -2147483648i32

#[test]
def test_u8_add_wraps : Bool := U8.add 200u8 100u8 == 44u8

#[test]
def test_u8_mul_wraps_to_zero : Bool := U8.mul 16u8 16u8 == 0u8

#[test]
def test_u8_div_by_zero_is_zero : Bool := U8.div 5u8 0u8 == 0u8

#[test]
def test_u16_mul_wraps : Bool := U16.mul 300u16 300u16 == 24464u16

#[test]
def test_u32_add_wraps_to_zero : Bool := U32.add 4294967295u32 1u32 == 0u32

#[test]
def test_u32_div_by_zero_is_zero : Bool := U32.div 7u32 0u32 == 0u32

#[test]
def test_u32_eq_after_wrap : Bool :=
    U32.beq 4294967295u32 (U32.add 4294967294u32 1u32)

#[test]
def test_u64_lt_is_unsigned_above_i63 : Bool :=
    U64.lt 9223372036854775807u64 0xFFFFFFFFFFFFFFFFu64

#[test]
def test_u64_gt_is_unsigned_above_i63 : Bool :=
    U64.gt 0xFFFFFFFFFFFFFFFFu64 9223372036854775807u64

#[test]
def test_u64_div_is_unsigned_at_max : Bool :=
    U64.div 0xFFFFFFFFFFFFFFFFu64 2u64 == 0x7FFFFFFFFFFFFFFFu64

#[test]
def test_u64_mod_is_unsigned_at_max : Bool :=
    U64.mod 0xFFFFFFFFFFFFFFFFu64 10u64 == 5u64

#[test]
def test_u64_div_by_zero_is_zero : Bool := U64.div 5u64 0u64 == 0u64

#[test]
def test_f32_add_computes_in_f32 : Bool := F32.add 0.1f32 0.2f32 == 0.3f32

#[test]
def test_f32_sub_exact : Bool := F32.sub 0.5f32 0.25f32 == 0.25f32

#[test]
def test_f32_mul_exact : Bool := F32.mul 0.5f32 0.5f32 == 0.25f32

#[test]
def test_f32_to_string_prints_f32 : Bool := F32.to_string 0.1f32 == "0.1"

#[test]
def test_f64_sum_is_not_f32_rounded : Bool :=
    Bool.not (F64.add 0.1 0.2 == 0.3)

#[test]
def test_f64_to_string_prints_f64 : Bool :=
    F64.to_string (F64.div 1.0 3.0) == "0.3333333333333333"
