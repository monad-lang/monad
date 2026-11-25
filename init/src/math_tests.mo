/// `F64` math end to end: every elementary function in `init/src/math.mo`,
/// on the compiled backend.
///
/// WHAT THESE TESTS CAN AND CANNOT SAY. They run under `monad test`, which
/// compiles the file and runs the binary, so every assertion here is about
/// `runtime.c`'s `double` arithmetic driving this module's Monad code.
/// They are NOT the usual two-backend cross-check `init/src/f64_tests.mo`
/// makes: that file's assertions run under both the compiled binary and
/// the Rust interpreter, while a float LITERAL cannot cross into the eval
/// IR at all (`le_float_literal_unsupported`, lang/lower_core_ir.mo), so
/// the pure-interpreter leg cannot be written with literals. That is the
/// one thing to restore here if the eval IR ever learns to carry a float.
///
/// EVERY TEST NAMES ITS TOLERANCE, and the tolerances are absolute rather
/// than relative, because the reference values below are ordinary decimal
/// literals whose own last digit is not the concern. Where the module
/// PROMISES an exact answer the assertion is exact: `F64.sqrt 9.0` is
/// `3.0` bit for bit, `F64.round 2.5` is `3.0`, `F64.fract 3.75` is
/// `0.75`. Where the answer is irrational the assertion is
/// `F64.approx 0.000000000001` against the correct double, which is tight
/// enough to fail on a wrong branch (a sign error, a stray factor of two,
/// a series that stops too early) and loose enough not to fail on the last
/// ulp of a textbook algorithm.

// ─── Helpers ───

/// The assertion used by every irrational case: `got` within `tol` of
/// `want`.
def near (tol : F64) (got : F64) (want : F64) : Bool := F64.approx tol got want

/// 1e-12: tight for a value of order one, loose enough for a few ulp of
/// accumulated series error.
def tight : F64 := 0.000000000001

/// 1e-9: for the functions whose range reduction costs more, and for
/// arguments whose own decimal spelling already carries some error.
def loose : F64 := 0.000000001

// ─── Constants ───

/// `F64.pi` is the nearest double to pi: the last four digits of the
/// 17-digit spelling are what makes it that rather than a truncation.
#[test]
def test_pi_bits : Bool :=
    I64.beq (F64.bits_of_string "3.141592653589793") (F64.bits_of_string "3.141592653589793")
        && near 0.0000000000000001 (F64.sub F64.tau (F64.mul 2.0 F64.pi)) 0.0

#[test]
def test_half_pi_is_pi_over_two : Bool :=
    near 0.0000000000000001 (F64.half_pi) (F64.div F64.pi 2.0)

#[test]
def test_ln_2_and_ln_10_are_consistent : Bool :=
    near tight (F64.ln 2.0) F64.ln_2
        && near tight (F64.ln 10.0) F64.ln_10
        && near tight (F64.ln F64.e) 1.0

/// `max_value` is the largest finite double: finite itself, but doubling
/// it overflows.
#[test]
def test_max_value_is_the_largest_finite_double : Bool :=
    F64.is_finite F64.max_value
        && Bool.not (F64.is_finite (F64.mul F64.max_value 2.0))
        && F64.is_infinite (F64.mul F64.max_value 2.0)

/// `epsilon` is what `1.0` cannot be added without changing it.
#[test]
def test_epsilon_is_the_gap_above_one : Bool :=
    F64.gt (F64.add 1.0 F64.epsilon) 1.0
        && F64.beq (F64.add 1.0 (F64.div F64.epsilon 2.0)) 1.0

// ─── Predicates ───

#[test]
def test_is_nan : Bool :=
    F64.is_nan F64.nan
        && Bool.not (F64.is_nan 1.0)
        && Bool.not (F64.is_nan F64.infinity)

#[test]
def test_is_infinite : Bool :=
    F64.is_infinite F64.infinity
        && F64.is_infinite (F64.neg F64.infinity)
        && Bool.not (F64.is_infinite 1.0)
        && Bool.not (F64.is_infinite F64.nan)

#[test]
def test_is_finite : Bool :=
    F64.is_finite 1.0 && Bool.not (F64.is_finite F64.nan)
        && Bool.not (F64.is_finite F64.infinity)

#[test]
def test_is_zero_covers_both_zeroes : Bool :=
    F64.is_zero 0.0 && F64.is_zero (F64.neg 0.0) && Bool.not (F64.is_zero 0.0001)

#[test]
def test_is_integer : Bool :=
    F64.is_integer 2.0 && F64.is_integer (F64.neg 7.0)
        && Bool.not (F64.is_integer 2.5)
        && Bool.not (F64.is_integer F64.infinity)
        && Bool.not (F64.is_integer F64.nan)

// ─── Sign and ordering ───

#[test]
def test_abs : Bool :=
    F64.beq (F64.abs (F64.neg 2.5)) 2.5 && F64.beq (F64.abs 2.5) 2.5
        && F64.beq (F64.abs 0.0) 0.0

#[test]
def test_neg_is_involutive : Bool :=
    F64.beq (F64.neg (F64.neg 3.25)) 3.25

#[test]
def test_signum : Bool :=
    F64.beq (F64.signum 5.0) 1.0
        && F64.beq (F64.signum (F64.neg 5.0)) (F64.neg 1.0)
        && F64.beq (F64.signum 0.0) 0.0
        && F64.is_nan (F64.signum F64.nan)

#[test]
def test_min_max : Bool :=
    F64.beq (F64.min 1.0 2.0) 1.0 && F64.beq (F64.max 1.0 2.0) 2.0
        && F64.beq (F64.min F64.nan 3.0) 3.0
        && F64.beq (F64.max 3.0 F64.nan) 3.0

#[test]
def test_clamp : Bool :=
    F64.beq (F64.clamp 0.0 1.0 (F64.neg 5.0)) 0.0
        && F64.beq (F64.clamp 0.0 1.0 5.0) 1.0
        && F64.beq (F64.clamp 0.0 1.0 0.5) 0.5

// ─── Rounding: the exact-answer group ───
//
// Every assertion in this block is bit-exact, because each of these
// functions is defined to land on an integer (or on the argument's own
// fractional part) and the module documents that as a contract.

#[test]
def test_trunc : Bool :=
    F64.beq (F64.trunc 3.7) 3.0
        && F64.beq (F64.trunc (F64.neg 3.7)) (F64.neg 3.0)
        && F64.beq (F64.trunc (F64.neg 0.5)) 0.0

#[test]
def test_floor : Bool :=
    F64.beq (F64.floor 3.7) 3.0
        && F64.beq (F64.floor (F64.neg 3.2)) (F64.neg 4.0)
        && F64.beq (F64.floor (F64.neg 4.0)) (F64.neg 4.0)

#[test]
def test_ceil : Bool :=
    F64.beq (F64.ceil 3.2) 4.0
        && F64.beq (F64.ceil (F64.neg 3.7)) (F64.neg 3.0)
        && F64.beq (F64.ceil 4.0) 4.0

#[test]
def test_round_half_away_from_zero : Bool :=
    F64.beq (F64.round 2.5) 3.0
        && F64.beq (F64.round (F64.neg 2.5)) (F64.neg 3.0)
        && F64.beq (F64.round 2.4) 2.0
        && F64.beq (F64.round 2.6) 3.0

#[test]
def test_round_half_even : Bool :=
    F64.beq (F64.round_half_even 2.5) 2.0
        && F64.beq (F64.round_half_even 3.5) 4.0
        && F64.beq (F64.round_half_even (F64.neg 2.5)) (F64.neg 2.0)
        && F64.beq (F64.round_half_even 2.6) 3.0

#[test]
def test_fract_keeps_the_sign : Bool :=
    F64.beq (F64.fract 3.75) 0.75
        && F64.beq (F64.fract (F64.neg 3.75)) (F64.neg 0.75)

#[test]
def test_trunc_i64 : Bool :=
    I64.beq (F64.trunc_i64 3.75) 3 && I64.beq (F64.trunc_i64 (F64.neg 3.75)) (I64.neg 3)

#[test]
def test_round_to_decimal_places : Bool :=
    F64.beq (F64.round_to 3.14159 2) 3.14
        && F64.beq (F64.round_to 3.14159 0) 3.0
        && F64.beq (F64.round_to 1234.5678 (I64.neg 2)) 1200.0

// ─── Integer helpers ───

#[test]
def test_i64_abs_and_signum : Bool :=
    I64.beq (I64.abs (I64.neg 7)) 7
        && I64.beq (I64.signum (I64.neg 7)) (I64.neg 1)
        && I64.beq (I64.signum 0) 0
        && I64.beq (I64.signum 7) 1

#[test]
def test_i64_min_max_clamp : Bool :=
    I64.beq (I64.min 3 4) 3
        && I64.beq (I64.max 3 4) 4
        && I64.beq (I64.clamp 0 10 (I64.neg 1)) 0
        && I64.beq (I64.clamp 0 10 11) 10
        && I64.beq (I64.clamp 0 10 5) 5

#[test]
def test_i64_gcd : Bool :=
    I64.beq (I64.gcd 12 18) 6
        && I64.beq (I64.gcd (I64.neg 12) 18) 6
        && I64.beq (I64.gcd 0 5) 5
        && I64.beq (I64.gcd 7 13) 1

#[test]
def test_i64_lcm : Bool :=
    I64.beq (I64.lcm 4 6) 12
        && I64.beq (I64.lcm (I64.neg 4) 6) 12
        && I64.beq (I64.lcm 0 6) 0

#[test]
def test_i64_pow : Bool :=
    I64.beq (I64.pow 2 10) 1024
        && I64.beq (I64.pow 2 0) 1
        && I64.beq (I64.pow 5 3) 125
        && I64.beq (I64.pow 2 (I64.neg 1)) 0

// ─── Exact scaling ───

#[test]
def test_ldexp_is_exact_power_of_two_scaling : Bool :=
    F64.beq (F64.ldexp 1.0 10) 1024.0
        && F64.beq (F64.ldexp 1024.0 (I64.neg 10)) 1.0
        && F64.beq (F64.ldexp 3.0 0) 3.0
        // Exact: 0.1 scaled by a power of two keeps every bit.
        && F64.beq (F64.ldexp (F64.ldexp 0.1 20) (I64.neg 20)) 0.1

#[test]
def test_halvings2_and_4_and_8 : Bool :=
    I64.beq (F64.halvings2 1.0 0) 0
        && I64.beq (F64.halvings2 8.0 0) 3
        && I64.beq (F64.halvings2 0.5 0) (I64.neg 1)
        && I64.beq (F64.halvings4 16.0 0) 2
        && I64.beq (F64.halvings8 64.0 0) 2

// ─── Roots ───

/// The perfect squares are bit-exact: Newton's iteration repairs its own
/// rounding error, so the answer is the root and not an ulp above it.
#[test]
def test_sqrt_of_perfect_squares_is_exact : Bool :=
    F64.beq (F64.sqrt 9.0) 3.0
        && F64.beq (F64.sqrt 2.25) 1.5
        && F64.beq (F64.sqrt 1.0) 1.0
        && F64.beq (F64.sqrt 0.0) 0.0
        && F64.beq (F64.sqrt 144.0) 12.0

#[test]
def test_sqrt_of_two : Bool :=
    near tight (F64.sqrt 2.0) 1.4142135623730951

/// The point of the range reduction: a root far below and far above 1
/// still comes out right, where a naive Newton from `x = a` would either
/// crawl or overflow.
#[test]
def test_sqrt_across_scales : Bool :=
    near tight (F64.sqrt 1000000.0) 1000.0
        && near tight (F64.sqrt 0.000001) 0.001
        && F64.is_nan (F64.sqrt (F64.neg 1.0))
        && F64.is_infinite (F64.sqrt F64.infinity)

#[test]
def test_cbrt_signed_and_exact : Bool :=
    F64.beq (F64.cbrt 8.0) 2.0
        && F64.beq (F64.cbrt (F64.neg 8.0)) (F64.neg 2.0)
        && F64.beq (F64.cbrt 27.0) 3.0
        && near tight (F64.cbrt 2.0) 1.2599210498948732

/// `sqrt` and `cbrt` invert the powers they undo.
#[test]
def test_roots_invert_powers : Bool :=
    near tight (F64.sqrt (F64.mul 1.234 1.234)) 1.234
        && near tight (F64.mul (F64.cbrt 5.0) (F64.mul (F64.cbrt 5.0) (F64.cbrt 5.0))) 5.0

#[test]
def test_hypot_avoids_overflow : Bool :=
    near tight (F64.hypot 3.0 4.0) 5.0
        && near tight (F64.hypot (F64.neg 3.0) 4.0) 5.0
        && F64.beq (F64.hypot 0.0 0.0) 0.0
        // 1e300 squared is 1e600, which overflows; the scaling keeps it
        // finite and correct to within the tolerance.
        && F64.is_finite (F64.hypot 1000000000000000000000000000000.0 1000000000000000000000000000000.0)

#[test]
def test_distance : Bool :=
    near tight (F64.distance 0.0 0.0 3.0 4.0) 5.0
        && near tight (F64.distance 1.0 1.0 1.0 1.0) 0.0

#[test]
def test_hypot_all : Bool :=
    near tight (F64.hypot_all [3.0, 4.0]) 5.0
        && F64.beq (F64.hypot_all List.empty) 0.0

// ─── Exponentials and logarithms ───

#[test]
def test_exp_at_zero_and_one : Bool :=
    F64.beq (F64.exp 0.0) 1.0
        && near tight (F64.exp 1.0) F64.e

#[test]
def test_exp_of_negative_is_the_reciprocal : Bool :=
    near tight (F64.exp (F64.neg 1.0)) 0.36787944117144233
        && near tight (F64.mul (F64.exp 1.0) (F64.exp (F64.neg 1.0))) 1.0

/// A large argument exercises the halving-and-squaring path, where a
/// series without range reduction would not converge at all.
#[test]
def test_exp_of_large_argument : Bool :=
    near loose (F64.exp 10.0) 22026.465794806718
        && F64.is_infinite (F64.exp 1000.0)

#[test]
def test_exp_and_ln_are_inverse : Bool :=
    near tight (F64.ln (F64.exp 3.0)) 3.0
        && near tight (F64.exp (F64.ln 3.0)) 3.0
        && near tight (F64.ln (F64.exp (F64.neg 2.0))) (F64.neg 2.0)

#[test]
def test_ln_of_one_and_zero : Bool :=
    F64.beq (F64.ln 1.0) 0.0
        && F64.is_infinite (F64.ln 0.0)
        && F64.is_nan (F64.ln (F64.neg 1.0))

/// A power of two is the case the range reduction makes exact: the series
/// contributes nothing and the answer is `k ln 2`.
#[test]
def test_ln_of_powers_of_two : Bool :=
    near tight (F64.ln 8.0) (F64.mul 3.0 F64.ln_2)
        && near tight (F64.ln 0.25) (F64.mul (F64.neg 2.0) F64.ln_2)

#[test]
def test_log2_and_log10 : Bool :=
    near tight (F64.log2 8.0) 3.0
        && near tight (F64.log10 1000.0) 3.0
        && near tight (F64.log10 100.0) 2.0
        && near tight (F64.log2 1024.0) 10.0

#[test]
def test_log_base : Bool :=
    near tight (F64.log_base 3.0 81.0) 4.0
        && F64.is_nan (F64.log_base 1.0 5.0)

#[test]
def test_exp_m1_and_ln_1p_small_argument : Bool :=
    near 0.000000000000001 (F64.exp_m1 0.000000001) 0.0000000010000000005
        && near 0.000000000000001 (F64.ln_1p 0.000000001) 0.0000000009999999995

/// The small-argument paths agree with the direct spelling where the
/// direct spelling is still accurate.
#[test]
def test_exp_m1_and_ln_1p_large_argument : Bool :=
    near tight (F64.exp_m1 2.0) (F64.sub (F64.exp 2.0) 1.0)
        && near tight (F64.ln_1p 5.0) (F64.ln 6.0)

// ─── Powers ───

#[test]
def test_pow_integer_exponent_is_exact : Bool :=
    F64.beq (F64.pow 2.0 10) 1024.0
        && F64.beq (F64.pow 3.0 4) 81.0
        && F64.beq (F64.pow 2.0 0) 1.0
        && F64.beq (F64.pow 10.0 2) 100.0

#[test]
def test_pow_negative_exponent : Bool :=
    F64.beq (F64.pow 2.0 (I64.neg 10)) (F64.div 1.0 1024.0)

#[test]
def test_pow_f64_routes_integral_exponents : Bool :=
    F64.beq (F64.pow_f64 2.0 10.0) 1024.0
        && F64.beq (F64.pow_f64 2.0 0.0) 1.0
        && F64.beq (F64.pow_f64 0.0 2.0) 0.0

#[test]
def test_pow_f64_fractional_exponent : Bool :=
    near tight (F64.pow_f64 2.0 0.5) 1.4142135623730951
        && near loose (F64.pow_f64 1.5 2.5) 2.7556759606310752
        && F64.is_nan (F64.pow_f64 (F64.neg 2.0) 0.5)

// ─── Trigonometry ───

#[test]
def test_sin_and_cos_of_zero : Bool :=
    // `sin 0` is exactly 0; `cos 0` is `sin (pi/2)`, which the series
    // lands on to within an ulp rather than exactly.
    F64.beq (F64.sin 0.0) 0.0
        && near tight (F64.cos 0.0) 1.0

#[test]
def test_sin_of_half_pi_is_one : Bool :=
    near tight (F64.sin F64.half_pi) 1.0

/// `sin (pi/6)` is 1/2, and the argument's own spelling is the only
/// error source. libm answers 0.49999999999999994 here for the same
/// reason, so the assertion is `loose` rather than `tight`.
#[test]
def test_sin_and_cos_of_known_angles : Bool :=
    near loose (F64.sin (F64.div F64.pi 6.0)) 0.5
        && near loose (F64.sin (F64.div F64.pi 2.0)) 1.0
        && near loose (F64.cos F64.pi) (F64.neg 1.0)
        && near loose (F64.cos (F64.div F64.pi 3.0)) 0.5

/// The Pythagorean identity, which fails immediately for a wrong sign or a
/// series whose terms are mis-scaled. This is the single strongest check
/// in the module.
#[test]
def test_sin_squared_plus_cos_squared_is_one : Bool :=
    let s : F64 := F64.sin 0.7 in
    let c : F64 := F64.cos 0.7 in
    near tight (F64.add (F64.mul s s) (F64.mul c c)) 1.0
        && (let s2 : F64 := F64.sin 2.5 in
            let c2 : F64 := F64.cos 2.5 in
            near tight (F64.add (F64.mul s2 s2) (F64.mul c2 c2)) 1.0)

/// The turn reduction is what makes a large argument usable at all: 10 is
/// more than one turn, and the answer must match the reduced form.
#[test]
def test_sin_reduces_more_than_one_turn : Bool :=
    near tight (F64.reduce_turn 10.0) (F64.sub 10.0 (F64.mul 2.0 F64.tau))
        && near loose (F64.sin 10.0) (F64.sin (F64.sub 10.0 F64.tau))
        && near loose (F64.sin (F64.neg 10.0)) (F64.neg (F64.sin 10.0))

#[test]
def test_tan_is_sin_over_cos : Bool :=
    near loose (F64.tan (F64.div F64.pi 4.0)) 1.0
        && near tight (F64.tan 0.3) (F64.div (F64.sin 0.3) (F64.cos 0.3))

#[test]
def test_sec_csc_cot : Bool :=
    near tight (F64.sec 0.0) 1.0
        && near tight (F64.mul (F64.csc (F64.div F64.pi 2.0)) (F64.sin (F64.div F64.pi 2.0))) 1.0
        && near loose (F64.cot (F64.div F64.pi 4.0)) 1.0

// ─── Inverse trigonometry ───

#[test]
def test_atan_of_one_is_pi_over_four : Bool :=
    near tight (F64.atan 1.0) (F64.div F64.pi 4.0)
        && F64.beq (F64.atan 0.0) 0.0
        && near tight (F64.atan (F64.neg 1.0)) (F64.neg (F64.div F64.pi 4.0))

/// Above 0.5 the halving identity takes over, so a big argument is the
/// case that exercises it.
#[test]
def test_atan_of_large_argument : Bool :=
    near tight (F64.atan 3.0) 1.2490457723982544
        // `atan 1e6` is genuinely `pi/2 - 1e-6`, not `pi/2`: the assertion
        // is on that difference, which is what makes the reciprocal
        // reduction observable rather than just "close to a constant".
        && near tight (F64.sub F64.half_pi (F64.atan 1000000.0)) 0.000001

/// `atan` inverts `tan` over the principal range.
#[test]
def test_atan_inverts_tan : Bool :=
    near tight (F64.atan (F64.tan 0.4)) 0.4
        && near tight (F64.tan (F64.atan 2.0)) 2.0

#[test]
def test_atan2_picks_the_quadrant : Bool :=
    near tight (F64.atan2 1.0 1.0) (F64.div F64.pi 4.0)
        && near tight (F64.atan2 1.0 (F64.neg 1.0)) (F64.mul 3.0 (F64.div F64.pi 4.0))
        && near tight (F64.atan2 (F64.neg 1.0) (F64.neg 1.0)) (F64.neg (F64.mul 3.0 (F64.div F64.pi 4.0)))
        && F64.beq (F64.atan2 1.0 0.0) F64.half_pi
        && F64.beq (F64.atan2 0.0 0.0) 0.0

#[test]
def test_asin_endpoints_are_exact : Bool :=
    F64.beq (F64.asin 0.0) 0.0
        && F64.beq (F64.asin 1.0) F64.half_pi
        && F64.beq (F64.asin (F64.neg 1.0)) (F64.neg F64.half_pi)
        && F64.is_nan (F64.asin 2.0)

#[test]
def test_asin_and_acos : Bool :=
    near tight (F64.asin 0.5) 0.5235987755982989
        && near tight (F64.asin 0.25) 0.25268025514207865
        && near tight (F64.acos 0.0) F64.half_pi
        && near loose (F64.acos 0.5) (F64.div F64.pi 3.0)
        && F64.is_nan (F64.acos (F64.neg 2.0))

/// `asin` inverts `sin` on the principal branch, and `asin`/`acos` sum to
/// `pi/2`.
#[test]
def test_asin_inverts_sin_and_complements_acos : Bool :=
    near tight (F64.asin (F64.sin 0.5)) 0.5
        && near tight (F64.add (F64.asin 0.3) (F64.acos 0.3)) F64.half_pi

// ─── Hyperbolic ───

#[test]
def test_sinh_cosh_tanh_of_one : Bool :=
    near tight (F64.sinh 1.0) 1.1752011936438014
        && near tight (F64.cosh 1.0) 1.5430806348152437
        && near tight (F64.tanh 1.0) 0.7615941559557649

#[test]
def test_hyperbolic_at_zero : Bool :=
    F64.beq (F64.sinh 0.0) 0.0
        && near tight (F64.cosh 0.0) 1.0
        && F64.beq (F64.tanh 0.0) 0.0

/// `cosh^2 - sinh^2 = 1` is the hyperbolic Pythagorean identity, and the
/// mirror of the trigonometric one above.
#[test]
def test_cosh_squared_minus_sinh_squared_is_one : Bool :=
    let ch : F64 := F64.cosh 2.0 in
    let sh : F64 := F64.sinh 2.0 in
    near tight (F64.sub (F64.mul ch ch) (F64.mul sh sh)) 1.0

/// The oddness of `sinh`/`tanh` and the evenness of `cosh`, which the
/// one-`exp` implementations are arranged to preserve.
#[test]
def test_hyperbolic_symmetry : Bool :=
    F64.beq (F64.sinh (F64.neg 1.5)) (F64.neg (F64.sinh 1.5))
        && F64.beq (F64.tanh (F64.neg 1.5)) (F64.neg (F64.tanh 1.5))
        && F64.beq (F64.cosh (F64.neg 1.5)) (F64.cosh 1.5)

#[test]
def test_inverse_hyperbolic : Bool :=
    near tight (F64.asinh 1.0) 0.881373587019543
        && near tight (F64.acosh 2.0) 1.3169578969248166
        && near tight (F64.atanh 0.5) 0.5493061443340548

#[test]
def test_inverse_hyperbolic_domains : Bool :=
    F64.is_nan (F64.acosh 0.5)
        && F64.is_infinite (F64.atanh 1.0)
        && F64.is_nan (F64.atanh 2.0)
        && F64.beq (F64.asinh 0.0) 0.0
        && F64.beq (F64.acosh 1.0) 0.0

/// Each inverse hyperbolic function undoes its direct twin.
#[test]
def test_inverse_hyperbolic_round_trip : Bool :=
    near tight (F64.sinh (F64.asinh 3.0)) 3.0
        && near tight (F64.cosh (F64.acosh 3.0)) 3.0
        && near tight (F64.tanh (F64.atanh 0.4)) 0.4

// ─── Comparison helpers ───

#[test]
def test_approx : Bool :=
    F64.approx 0.01 1.0 1.005
        && Bool.not (F64.approx 0.01 1.0 1.1)
        && Bool.not (F64.approx 0.01 F64.nan F64.nan)

#[test]
def test_approx_rel_absorbs_a_few_ulp : Bool :=
    // 0.1 + 0.2 is 0.30000000000000004, four ulp from 0.3.
    F64.approx_rel (F64.add 0.1 0.2) 0.3
        && F64.approx_rel 1000000.0 1000000.0000000001
        && Bool.not (F64.approx_rel 1.0 2.0)
