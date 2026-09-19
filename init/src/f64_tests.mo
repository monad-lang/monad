/// `F64` end to end: the decimal literals, the arithmetic, the
/// comparisons and the two conversions, on BOTH backends.
///
/// Every assertion here is a cross-check, not a restatement: this file
/// runs under the self-hosted runner (compiled code, `runtime.c`'s F64
/// section) and under `monad-rs test` (the Rust evaluator,
/// `core/src/core_native.rs`), so a test that passes is two independent
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
/// `+` is deliberately absent: `infix (+)` is `HAdd.add`
/// (`init/src/prelude.mo`), whose only instance for `F64` is the generic
/// `[Add A] HAdd A A A` forwarding instance, and BOTH checkers resolve
/// that to the `I64` instance -- "type mismatch: `F64` vs. `I64`" -- so
/// `1.0 + 2.0` does not check today even though `1.0 * 2.0` (a concrete
/// `HMul F64 F64 F64`), `1.0 - 2.0` and `1.0 / 2.0` all do. That is a
/// pre-existing instance-resolution gap in the `HAdd`/`Add` forwarding
/// pair, not a float one (the same shape is the `__Dict_Add_A`
/// self-recursion the registry records for `init/src/tests.mo`), and it
/// is left visible here rather than worked around: the operators this
/// file can exercise are exactly the ones both backends resolve.

/// The literal's own VALUE, through the parser: 0x40091EB851EB851F is the
/// double nearest 3.14. Pinned as bits because that is exactly what the
/// backend stores, and it is where a wrong decimal parse would show up
/// (the old `Literal.flt` lowering emitted a constant 0 here, which is
/// also why this is asserted rather than assumed).
#[test]
def test_f64_literal_bits_are_the_nearest_double : Bool :=
    I64.beq (F64.bits_of_string "3.14") 4614253070214989087

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
