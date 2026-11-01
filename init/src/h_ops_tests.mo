/// The heterogeneous operator classes (`HAdd`, `HSub`, `HDiv`, `HMul`)
/// end to end: direct class calls and the `+`/`-`/`*`/`/` operators, on
/// both backends.
///
/// `HSub`/`HDiv` are new (`init/src/prelude.mo`), `HAdd`'s per-type
/// instances are new (`init/src/number.mo`), and `infix (-)`/`infix (/)`
/// are retargeted from the homogeneous `Sub.sub`/`Div.div` to
/// `HSub.sub`/`HDiv.div` (the prelude's `infix (+) := HAdd.add` becomes
/// effective everywhere once `init/src/lib.mo`'s historical
/// `infix (+) := I64.add` override is gone). This is `HMul`'s exact,
/// corpus-proven pattern: the operator dispatches through the
/// heterogeneous class, and the class's per-type instances carry the
/// bodies.
///
/// Why DIRECT per-type instances, not bridges through the homogeneous
/// classes: the checker's instance table
/// (`rust/core/src/core_check_module.rs`'s `collect_known_instances`)
/// keys each instance on `(class, first-type-argument's head path)` and
/// deliberately SKIPS variable-headed instances (a variable has no
/// path). The prelude's historical `instance [Add A] HAdd A A A` bridge
/// therefore never entered the table, `[HAdd T T T]` had no candidate
/// at all, and a generic-fn `+` call died at eval with `unresolved
/// global: HAdd.add` -- that bridge pair never resolved a single call.
/// A per-type `instance HAdd I64 I64 I64` is keyed `(HAdd, I64)` like
/// any other, which is the whole fix.
///
/// Why no GENUINELY heterogeneous instance here (say `HSub I64 U8 I64`):
/// the table keeps ONE slot per `(class, head)` key -- `Map::insert`,
/// last one wins -- and this file's own instance would be inserted
/// last, capturing every `[HSub I64 ...]` lookup in the file and
/// routing `I64 - I64` calls through a `U8`-truncating body
/// (`HSub.sub 300 300` would evaluate to `256`, not `0`). A user mote
/// that owns its `(class, head)` slot can still declare one; what this
/// file pins is the homogeneous dispatch the corpus's operators need,
/// plus the `300 300` assertion that would catch any such capture the
/// moment one lands in this load.
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
/// U8` keeps `HAdd U8 U8 U8`, discards `HAdd I64 I64 I64`), retags both
/// literals, and the wraparound proves the arithmetic itself ran at the
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
