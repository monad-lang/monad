/// The heterogeneous operator classes (`HAdd`, `HSub`, `HMul`, `HDiv`)
/// end to end: direct class calls and the `+`/`-`/`*`/`/` operators, on
/// both backends.
///
/// Every operator dispatches through its heterogeneous class
/// (`infix (+) := HAdd.add`), and every SYMMETRIC use resolves through
/// the class's one bridge, `instance [Add A] HAdd A A A`
/// (`init/src/prelude.mo`), to the homogeneous instance a type declares
/// (`Add U8`, `init/src/number.mo`). No type declares `HAdd T T T`.
///
/// The Rust checker keys instances on `(class, first argument's head)`,
/// and a bridge has no head, so it registers bridges under their own key
/// (`core_check::bridge_instance_key`) and falls back to one only when
/// the direct lookup misses. Selecting the bridge ties the call's params
/// together (`A A A`), so a bare literal operand retags to the other
/// operand's width, and the `[Add A]` dictionary comes from the type's
/// registered instance, or from the enclosing def's own `[Add A]` when
/// the type is still abstract (`test_generic_add_*` below).

#[test]
def test_hsub_i64_direct : Bool := HSub.sub 300 300 == 0

#[test]
def test_hsub_u8_direct : Bool := HSub.sub 5u8 3u8 == 2u8

#[test]
def test_hsub_f64_direct : Bool := HSub.sub 0.5 0.25 == 0.25

#[test]
def test_hsub_f32_direct : Bool := HSub.sub 0.5f32 0.25f32 == 0.25f32

#[test]
def test_hdiv_i64_direct : Bool := HDiv.div 1000 8 == 125

#[test]
def test_hdiv_u8_direct : Bool := HDiv.div 7u8 2u8 == 3u8

#[test]
def test_hdiv_f64_direct : Bool := HDiv.div 0.75 0.25 == 3.0

#[test]
def test_hadd_f64_direct : Bool := HAdd.add 0.25 0.5 == 0.75

#[test]
def test_hadd_f32_direct : Bool := HAdd.add 0.5f32 0.25f32 == 0.75f32

/// The operators, which is what the corpus runs through a million
/// times a day: `+` and `-` on `I64`, through the retargeted infixes.
#[test]
def test_infix_add_i64 : Bool :=
    let r : I64 := 5 + 3 in
    r == 8

#[test]
def test_infix_sub_i64 : Bool :=
    let r : I64 := 10 - 4 in
    r == 6

#[test]
def test_infix_div_i64 : Bool :=
    let r : I64 := 10 / 4 in
    r == 2

#[test]
def test_infix_mul_i64 : Bool :=
    let r : I64 := 6 * 7 in
    r == 42

/// `+` on `F64`: the regression for `init/src/lib.mo`'s removed
/// `infix (+) := I64.add` override, which used to shadow the prelude's
/// `infix (+) := HAdd.add` and make every non-`I64` `+` a type error.
#[test]
def test_infix_add_f64 : Bool :=
    let r : F64 := 1.0 + 2.0 in
    r == 3.0

#[test]
def test_infix_sub_f64 : Bool :=
    let r : F64 := 0.5 - 0.25 in
    r == 0.25

#[test]
def test_infix_mul_f64 : Bool :=
    let r : F64 := 0.5 * 4.0 in
    r == 2.0

#[test]
def test_infix_div_f64 : Bool :=
    let r : F64 := 0.75 / 0.25 in
    r == 3.0

/// A width other than `I64`/`F64` through the retargeted infix, on the
/// type where the old bridge-era `+` was most visibly broken.
#[test]
def test_infix_add_u8 : Bool :=
    let r : U8 := 250u8 + 5u8 in
    r == 255u8

#[test]
def test_infix_sub_u8 : Bool :=
    let r : U8 := 200u8 - 150u8 in
    r == 50u8

/// Both operands BARE: nothing pins the instance until the annotation
/// does. The checker reads the instance off the result position (`C :=
/// U8`, and `Add U8` exists, so the bridge `HAdd A A A` takes `A := U8`),
/// retags both literals, and the wraparound proves the arithmetic itself ran at the
/// width -- 260 in `U8` is 4, not the `I64` answer 260. The Rust
/// reference threads the same evidence before it processes any argument
/// (`try_resolve_class_method_inner`'s pre-argument peek); these pin that
/// the two checkers agree on the shape.
#[test]
def test_infix_add_u8_bare_operands : Bool :=
    let r : U8 := 250 + 10 in
    r == 4u8

#[test]
def test_infix_sub_u8_bare_operands : Bool :=
    let r : U8 := 4 - 10 in
    r == 250u8

/// The mixed case: the second operand's own suffix is NOT enough (the
/// right operand is checked first, so the bare left one defaults to `I64`
/// before any suffix is seen); the annotation carries the left one too.
#[test]
def test_infix_add_u8_bare_left_operand : Bool :=
    let r : U8 := 5 + 1u8 in
    r == 6u8

/// A bare INT operand against a float width: the instance evidence hands
/// it `F64`, and the literal retag re-spells the digits as a float
/// payload (the same route `42 : F64` takes), not an `I64` truncation.
#[test]
def test_infix_add_f64_bare_int_operand : Bool :=
    let r : F64 := 42 + 0.5 in
    r == 42.5

/// A def constrained on `[Add A]` must still take `Add I64` for its own
/// `I64` addition, not the bound `[Add A]` dictionary: with `A := U8`,
/// the bound dictionary would wrap 200 + 100 to 44.
def generic_with_i64 [Add A] (x : A) (n : I64) : I64 := n + 100

#[test]
def test_generic_def_concrete_add_ignores_bound_dict : Bool :=
    generic_with_i64 1u8 200 == 300
