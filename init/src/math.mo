// Math module -- elementary numerical functions.
//
// `init/src/lib.mo` re-exports this module, so everything declared here is
// AMBIENT: `F64.sin x` and `F64.sqrt x` need no import.
//
// WHAT THIS MODULE IS: the float half of the numeric tower.
// `init/src/number.mo` owns the arithmetic and the conversions -- `add`,
// `sub`, `mul`, `div`, `beq`, `lt`, `gt`, `to_string`, `to_i64`, `to_f64`
// -- and this module builds the elementary functions on top of them.
//
// PORTABLE BY CONSTRUCTION. Every function here is pure Monad over those
// arithmetic natives: no new `#[native]` is declared, and nothing is
// `#[extern "c"]`. That is deliberate, and it buys two things:
//
//   * Every target has them. A libm binding would need
//     `[link] libs = ["m"]` -- a property of the PACKAGE, so every program
//     depending on `std` would link `-lm` on native only -- and the web
//     profile is freestanding. `f64_of_string` is already gated there
//     (`web_only_natives`, codegen/src/natives.mo) precisely because it
//     needs `strtod`, and libm's transcendentals would be gated the same
//     way. This module works on native, wasi and web alike.
//   * `monad eval` and the Rust host can run them. A new native needs four
//     wiring touchpoints plus a positional id in `lang/core_eval.mo`'s
//     `native_specs`, and until all of them exist the interpreter answers
//     "unknown native" for it.
//
// NO NEW NATIVES, so `F64.bits_of_string` and friends stay the only
// float-to-value bridges in the tree. Note that this module deliberately
// does not call `F64.bits_of_string` either: it is `web_only_natives`-gated,
// and a pure-Monad constant should not drag a C `strtod` dependency into
// the web profile.
//
// NO DECIMAL EXPONENT LITERALS. The lexer reads `1.0e-9` as `1.0`, then the
// identifier `e`, then `-9`; there is no exponent form. Every constant
// below is either short positional decimal or built by arithmetic.
//
// ACCURACY. These are the textbook algorithms -- Taylor series, range
// reduction and Newton iteration -- in ordinary double arithmetic, NOT
// correctly-rounded libm replacements. Relative error is on the order of a
// few ulp (roughly 1e-15) over each function's documented domain.
// `init/src/math_tests.mo` asserts each one at an explicit tolerance rather
// than bit-exactly; where an exact answer is part of the contract
// (`F64.sqrt 9.0` is exactly `3.0`, `F64.round 2.5` is exactly `3.0`,
// `F64.fract 3.75` is exactly `0.75`), the implementation is arranged so
// the result IS exact and the test asserts bits.
//
// DOMAIN. Each function documents what it does outside its domain. The
// convention is C's where C has one (`F64.ln` of a negative is NaN,
// `F64.sqrt` of a negative is NaN) and a pinned value otherwise. Nothing
// here returns `Result`: a numerical function that answers NaN is more
// useful than one that refuses, and `F64.is_nan` is how you ask.

// ─── Constants ─────────────────────────────────────────────────────

/// The ratio of a circle's circumference to its diameter.
pub def F64.pi : F64 := 3.141592653589793

/// A full turn, `2 * F64.pi`.
pub def F64.tau : F64 := 6.283185307179586

/// Euler's number, the base of `F64.exp` and `F64.ln`.
pub def F64.e : F64 := 2.718281828459045

/// Half a turn, `F64.pi / 2`.
pub def F64.half_pi : F64 := 1.5707963267948966

/// The natural logarithm of 2, the constant every range reduction scales
/// its count by.
pub def F64.ln_2 : F64 := 0.6931471805599453

/// The natural logarithm of 10, for `F64.log10`.
pub def F64.ln_10 : F64 := 2.302585092994046

/// The difference between 1.0 and the next representable double: 2^-52.
///
/// This is the tolerance to reach for when comparing two computed
/// floats; `F64.approx_rel` is that comparison already spelled out.
pub def F64.epsilon : F64 := 0.0000000000000002220446049250313

/// The largest finite double, `(2 - 2^-52) * 2^1023`.
///
/// Built rather than written out: 1.7976931348623157e308 has no exponent
/// form (module header), and spelled positionally it is 309 digits, which
/// overflows the lexer's integer accumulator. Both factors are exactly
/// representable, so the product is the last value before infinity --
/// pinned by `test_max_value_is_the_largest_finite_double`, which checks
/// that `F64.max_value` is finite while twice it is not.
pub def F64.max_value : F64 := F64.mul 1.9999999999999998 (F64.pow 2.0 1023)

/// Positive infinity, as IEEE-754 spells it: a positive number over zero.
pub def F64.infinity : F64 := F64.div 1.0 0.0

/// Not-a-number, as IEEE-754 spells it: zero over zero.
pub def F64.nan : F64 := F64.div 0.0 0.0

// ─── Predicates ────────────────────────────────────────────────────
//
// These come first because everything else uses them. They are plain
// comparisons over `F64.beq`/`F64.lt`/`F64.gt`, which cost one native call
// each -- there is no bit-level predicate native, and this module adds
// none.

/// NaN is the only value not equal to itself.
pub def F64.is_nan (a : F64) : Bool := Bool.not (F64.beq a a)

/// True for `+inf` and `-inf`. `inf - inf` is NaN and `finite - finite`
/// never is, so the subtraction carries the whole test -- but a NaN
/// operand subtracts to NaN as well, which is why the `F64.beq a a`
/// conjunct (false for NaN alone) is what excludes it.
pub def F64.is_infinite (a : F64) : Bool :=
    Bool.and (F64.beq a a) (F64.is_nan (F64.sub a a))

/// True for every finite value; NaN and both infinities are excluded.
pub def F64.is_finite (a : F64) : Bool :=
    Bool.not (Bool.or (F64.is_nan a) (F64.is_infinite a))

/// `+0.0` or `-0.0`. A value test rather than a sign-bit test, because
/// `-0.0 == 0.0` in IEEE arithmetic and that is the answer callers want.
pub def F64.is_zero (a : F64) : Bool := F64.beq a 0.0

/// Whether `a` is a whole number. `F64.is_integer 2.0` and
/// `F64.is_integer (-7.0)` are both true; infinities and NaN are false.
pub def F64.is_integer (a : F64) : Bool :=
    if F64.is_finite a then F64.beq a (F64.trunc a) else false

// ─── Ordering and sign ─────────────────────────────────────────────

/// Absolute value. `-0.0` becomes `0.0`; NaN stays NaN.
pub def F64.abs (a : F64) : F64 := if F64.lt a 0.0 then F64.sub 0.0 a else a

/// Arithmetic negation. Spelled as a subtraction because the language has
/// no unary-minus operator, only a negative LITERAL.
pub def F64.neg (a : F64) : F64 := F64.sub 0.0 a

/// -1.0, 0.0 or 1.0 in the sign of `a`. Rust's `f64::signum` answers 1.0
/// for `+0.0` and -1.0 for `-0.0`; this module cannot see a zero's sign,
/// so both answer 0.0. NaN answers NaN.
pub def F64.signum (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.gt a 0.0 then 1.0
    else if F64.lt a 0.0 then F64.sub 0.0 1.0
    else 0.0

/// The smaller of two values. A NaN operand answers the other one, so a
/// NaN never silently wins or loses a comparison chain.
pub def F64.min (a b : F64) : F64 :=
    if F64.is_nan a then b
    else if F64.is_nan b then a
    else if F64.lt a b then a
    else b

/// The larger of two values, with the same NaN rule as `F64.min`.
pub def F64.max (a b : F64) : F64 :=
    if F64.is_nan a then b
    else if F64.is_nan b then a
    else if F64.gt a b then a
    else b

/// `a` confined to `[lo, hi]`. A `lo` above `hi` answers `lo`.
pub def F64.clamp (lo : F64) (hi : F64) (a : F64) : F64 :=
    if F64.lt a lo then lo else if F64.gt a hi then hi else a

// ─── Rounding ──────────────────────────────────────────────────────
//
// The integer-rounding functions share one trick: `F64.to_i64` truncates
// toward zero, and `I64.to_f64` gives the exact double back -- while the
// value fits an I64. `F64.trunc` therefore guards the magnitude first
// (2^53 is where doubles stop having fractional parts at all, and it is
// comfortably inside I64's range), so the saturation `F64.to_i64` applies
// beyond I64's range can never be observed as a wrong answer.

/// The largest magnitude at which every double is a whole number: 2^53.
pub def F64.integer_limit : F64 := 9007199254740992.0

/// Truncate toward zero: the integer part, keeping the sign of `a`. An
/// infinity or NaN is returned unchanged, as is any magnitude too large to
/// have a fractional part.
pub def F64.trunc (a : F64) : F64 :=
    if F64.is_finite a then
        if F64.gt (F64.abs a) F64.integer_limit then a
        else I64.to_f64 (F64.to_i64 a)
    else a

/// Largest integer less than or equal to `a`.
pub def F64.floor (a : F64) : F64 :=
    let t : F64 := F64.trunc a in
    if F64.gt t a then F64.sub t 1.0 else t

/// Smallest integer greater than or equal to `a`.
pub def F64.ceil (a : F64) : F64 :=
    let t : F64 := F64.trunc a in
    if F64.lt t a then F64.add t 1.0 else t

/// The integer part of `a` as an `I64`, truncated toward zero. An alias of
/// `F64.to_i64` under this module's naming, for call sites that read at
/// this level.
pub def F64.trunc_i64 (a : F64) : I64 := F64.to_i64 a

/// Nearest integer, ties away from zero -- the schoolbook rule.
/// `F64.round 2.5` is exactly `3.0` and `F64.round (-2.5)` is exactly
/// `-3.0`.
pub def F64.round (a : F64) : F64 :=
    let t : F64 := F64.trunc a in
    let frac : F64 := F64.abs (F64.sub a t) in
    if F64.lt frac 0.5 then t
    else if F64.lt a 0.0 then F64.sub t 1.0
    else F64.add t 1.0

/// Nearest integer with ties to even (banker's rounding), which is what
/// IEEE arithmetic and most financial code expect: `2.5` is `2.0` and
/// `3.5` is `4.0`. Evenness is the low bit of the truncated value.
pub def F64.round_half_even (a : F64) : F64 :=
    let t : F64 := F64.trunc a in
    let frac : F64 := F64.abs (F64.sub a t) in
    if F64.lt frac 0.5 then t
    else if F64.gt frac 0.5 then (if F64.lt a 0.0 then F64.sub t 1.0 else F64.add t 1.0)
    else
        let n : I64 := F64.to_i64 t in
        if I64.beq (I64.rem n 2) 0 then t
        else if F64.lt a 0.0 then F64.sub t 1.0
        else F64.add t 1.0

/// The fractional part, `a - trunc a`, keeping the sign of `a`:
/// `F64.fract (-3.75)` is `-0.75`.
pub def F64.fract (a : F64) : F64 := F64.sub a (F64.trunc a)

/// `x` rounded to `digits` decimal places, ties away from zero. A negative
/// `digits` rounds to tens, hundreds and so on.
pub def F64.round_to (x : F64) (digits : I64) : F64 :=
    let scale : F64 := F64.pow 10.0 digits in
    if F64.is_zero scale then x else F64.div (F64.round (F64.mul x scale)) scale

// ─── Exact scaling ─────────────────────────────────────────────────
//
// Multiplying by a power of two only moves the exponent, so every scaling
// here is exact and every range reduction below is free of error of its
// own. The halving counters are the inverse question: how many steps of a
// given base take `a` into that base's first bucket.

/// `a * 2^k` for integer `k`, exactly.
#[terminating]
pub def F64.ldexp (a : F64) (k : I64) : F64 :=
    if I64.beq k 0 then a
    else if I64.gt k 0 then F64.ldexp (F64.mul a 2.0) (I64.sub k 1)
    else F64.ldexp (F64.mul a 0.5) (I64.add k 1)

/// The `k` for which `a / 2^k` lands in `[1, 2)`. `a` must be positive and
/// finite.
#[terminating]
pub def F64.halvings2 (a : F64) (k : I64) : I64 :=
    if F64.lt a 1.0 then F64.halvings2 (F64.mul a 2.0) (I64.sub k 1)
    else if F64.lt a 2.0 then k
    else F64.halvings2 (F64.mul a 0.5) (I64.add k 1)

/// The `k` for which `a / 4^k` lands in `[1, 4)`. The even base is what
/// lets `F64.sqrt` halve the count and stay exact.
#[terminating]
pub def F64.halvings4 (a : F64) (k : I64) : I64 :=
    if F64.lt a 1.0 then F64.halvings4 (F64.mul a 4.0) (I64.sub k 1)
    else if F64.lt a 4.0 then k
    else F64.halvings4 (F64.div a 4.0) (I64.add k 1)

/// The `k` for which `a / 8^k` lands in `[1, 8)`. The cube root needs a
/// base that is a cube, so that scaling the result back is exact.
#[terminating]
pub def F64.halvings8 (a : F64) (k : I64) : I64 :=
    if F64.lt a 1.0 then F64.halvings8 (F64.mul a 8.0) (I64.sub k 1)
    else if F64.lt a 8.0 then k
    else F64.halvings8 (F64.div a 8.0) (I64.add k 1)

// ─── Roots ─────────────────────────────────────────────────────────

/// Square root. `F64.sqrt 0.0` is `0.0`, a negative argument is NaN, and
/// the root of a perfect square is exact.
///
/// Newton's iteration, `x <- (x + a/x)/2`, is self-correcting (a rounding
/// error in one step is repaired by the next), which is why a perfect
/// square lands exactly on its root rather than an ulp away from it.
pub def F64.sqrt (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.lt a 0.0 then F64.nan
    else if F64.is_infinite a then a
    else if F64.is_zero a then a
    else
        // Reduce into [1, 4), take the root there, then scale by 2^k --
        // exact, so the error is entirely the iteration's.
        let k : I64 := F64.halvings4 a 0 in
        let m : F64 := F64.ldexp a (I64.sub 0 (I64.mul k 2)) in
        let seed : F64 := if F64.lt m 2.0 then 1.5 else 2.25 in
        F64.ldexp (F64.newton_root m seed 0) k

/// Newton steps for `sqrt m`, `m` in `[1, 4)`, from a seed within a factor
/// of two of the root. The iteration is quadratic, so six steps reach an
/// ulp; the two extra polish the fixed point, which is what turns "within
/// an ulp" into "exactly right" for a perfect square.
#[terminating]
def F64.newton_root (m : F64) (x : F64) (n : I64) : F64 :=
    if I64.beq n 8 then x
    else F64.newton_root m (F64.mul (F64.add x (F64.div m x)) 0.5) (I64.add n 1)

/// Cube root, defined for negative arguments: `F64.cbrt (-8.0)` is exactly
/// `-2.0`. The sign is lifted first because Newton's iteration for a cube
/// root does not converge for a negative radicand.
pub def F64.cbrt (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.is_zero a then a
    else if F64.is_infinite a then a
    else if F64.lt a 0.0 then F64.sub 0.0 (F64.cbrt_pos (F64.sub 0.0 a))
    else F64.cbrt_pos a

/// Cube root of a positive value, reduced into `[1, 8)` by a base that is
/// itself a cube so the result scales back exactly.
def F64.cbrt_pos (a : F64) : F64 :=
    let k : I64 := F64.halvings8 a 0 in
    let m : F64 := F64.ldexp a (I64.sub 0 (I64.mul k 3)) in
    F64.ldexp (F64.newton_cbrt m (F64.seed_cbrt m) 0) k

/// A starting point for the cube-root iteration, for `m` in `[1, 8)`.
/// Each branch is within a factor of two of the true root.
def F64.seed_cbrt (m : F64) : F64 :=
    if F64.lt m 2.0 then 1.25
    else if F64.lt m 4.0 then 1.75
    else 3.0

/// Cubically-convergent Newton steps for `cbrt m`: `x <- (2x + m/x^2)/3`.
#[terminating]
def F64.newton_cbrt (m : F64) (x : F64) (n : I64) : F64 :=
    if I64.beq n 12 then x
    else
        let two_x : F64 := F64.mul 2.0 x in
        let next : F64 := F64.div (F64.add two_x (F64.div m (F64.mul x x))) 3.0 in
        F64.newton_cbrt m next (I64.add n 1)

/// `sqrt (x*x + y*y)` without intermediate overflow: the larger leg is
/// factored out first, so a pair of huge coordinates stays finite where
/// squaring them naively would overflow to infinity.
pub def F64.hypot (x y : F64) : F64 :=
    let ax : F64 := F64.abs x in
    let ay : F64 := F64.abs y in
    let big : F64 := F64.max ax ay in
    let small : F64 := F64.min ax ay in
    if F64.is_nan big then F64.nan
    else if F64.is_zero big then 0.0
    else if F64.is_infinite big then big
    else
        let r : F64 := F64.div small big in
        F64.mul big (F64.sqrt (F64.add 1.0 (F64.mul r r)))

/// Distance between two points on a plane.
pub def F64.distance (x1 : F64) (y1 : F64) (x2 : F64) (y2 : F64) : F64 :=
    F64.hypot (F64.sub x2 x1) (F64.sub y2 y1)

/// `sqrt` of the sum of squares of a list, accumulating without
/// intermediate overflow.
pub def F64.hypot_all (xs : List F64) : F64 := F64.hypot_all_go xs 0.0

#[partial]
def F64.hypot_all_go (xs : List F64) (acc : F64) : F64 :=
    match xs {
        List.empty => acc,
        List.cons hd tl => F64.hypot_all_go tl (F64.hypot acc hd),
    }

// ─── Integer helpers ───────────────────────────────────────────────

/// Absolute value. `I64.min` has no positive counterpart, so it answers
/// itself rather than wrapping to a negative.
pub def I64.abs (a : I64) : I64 := if I64.lt a 0 then I64.sub 0 a else a

/// -1, 0 or 1.
pub def I64.signum (a : I64) : I64 :=
    if I64.gt a 0 then 1 else if I64.lt a 0 then I64.sub 0 1 else 0

/// The smaller of two integers.
pub def I64.min (a b : I64) : I64 := if I64.lt a b then a else b

/// The larger of two integers.
pub def I64.max (a b : I64) : I64 := if I64.gt a b then a else b

/// `a` confined to `[lo, hi]`.
pub def I64.clamp (lo : I64) (hi : I64) (a : I64) : I64 :=
    if I64.lt a lo then lo else if I64.gt a hi then hi else a

/// Greatest common divisor, always non-negative: `I64.gcd a 0` is
/// `I64.abs a`, and `I64.gcd 0 0` is 0.
#[terminating]
pub def I64.gcd (a : I64) (b : I64) : I64 :=
    if I64.beq b 0 then I64.abs a else I64.gcd b (I64.rem a b)

/// Least common multiple, `|a| / gcd a b * |b|`. Zero when either operand
/// is zero, rather than the division by zero the raw formula would do.
pub def I64.lcm (a : I64) (b : I64) : I64 :=
    if I64.beq a 0 then 0
    else if I64.beq b 0 then 0
    else I64.abs (I64.mul (I64.div a (I64.gcd a b)) b)

/// Integer exponentiation by squaring. A negative exponent answers 0,
/// since there is no rational result to give; `I64.pow a 0` is 1 for every
/// `a`, zero included.
#[terminating]
pub def I64.pow (base : I64) (n : I64) : I64 :=
    if I64.lt n 0 then 0 else I64.pow_go base n 1

/// The squaring loop of `I64.pow`.
#[terminating]
def I64.pow_go (base : I64) (n : I64) (acc : I64) : I64 :=
    if I64.beq n 0 then acc
    else if I64.beq (I64.rem n 2) 0 then I64.pow_go (I64.mul base base) (I64.div n 2) acc
    else I64.pow_go (I64.mul base base) (I64.div n 2) (I64.mul acc base)

// ─── Exponentials ──────────────────────────────────────────────────

/// `e ** a`.
///
/// The argument is halved until it is below 1 (`a = m * 2^k`, an exact
/// halving), the Taylor series is evaluated at `m`, and the result is
/// squared `k` times -- `(e^m)^(2^k)` is `e^a`. Above `709.78` the true
/// value exceeds the double range and the answer is infinity; a negative
/// argument is `1 / exp (-a)`.
pub def F64.exp (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.lt a 0.0 then F64.div 1.0 (F64.exp_pos (F64.sub 0.0 a))
    else F64.exp_pos a

/// `e ** a` for a non-negative `a`: the halving, the series and the
/// squaring that `F64.exp` documents. Split out of it because the negative
/// branch would otherwise recurse on `0.0 - a`, an argument the
/// termination checker cannot see shrinking.
pub def F64.exp_pos (a : F64) : F64 :=
    if F64.gt a 709.782712893384 then F64.infinity
    else
        let k : I64 := F64.halvings_exp a 0 in
        let m : F64 := F64.ldexp a (I64.sub 0 k) in
        F64.square_n (F64.exp_series m 0 20 1.0 1.0) k

/// How many halvings take positive `a` below 1.
#[terminating]
def F64.halvings_exp (a : F64) (k : I64) : I64 :=
    if F64.lt a 1.0 then k else F64.halvings_exp (F64.mul a 0.5) (I64.add k 1)

/// The Taylor series for `e ^ m`. `acc` is the running sum, `term` the
/// term just added and `i` its index, so one step is `term <- term * m /
/// (i+1)` -- one multiply and one divide, with no factorial of its own.
#[terminating]
def F64.exp_series (m : F64) (i : I64) (n : I64) (acc : F64) (term : F64) : F64 :=
    if I64.beq i n then acc
    else
        let next : F64 := F64.div (F64.mul term m) (I64.to_f64 (I64.add i 1)) in
        F64.exp_series m (I64.add i 1) n (F64.add acc next) next

/// `x` squared `k` times, a `k` below 1 meaning "unchanged".
#[terminating]
pub def F64.square_n (x : F64) (k : I64) : F64 :=
    if I64.lt k 1 then x else F64.square_n (F64.mul x x) (I64.sub k 1)

/// `e ** a - 1`, accurate for a small `a` where `F64.exp a - 1` would lose
/// every significant digit to the subtraction.
pub def F64.exp_m1 (a : F64) : F64 :=
    if F64.lt (F64.abs a) 0.000001 then
        let a2 : F64 := F64.mul a a in
        F64.add (F64.add a (F64.mul a2 0.5)) (F64.div (F64.mul a2 a) 6.0)
    else F64.sub (F64.exp a) 1.0

// ─── Logarithms ────────────────────────────────────────────────────

/// Natural logarithm. `F64.ln 1.0` is exactly `0.0`, `F64.ln 0.0` is
/// `-inf`, and a negative argument is NaN.
///
/// The argument is scaled into `[1, 2)` by powers of two (`ln (m 2^k)` is
/// `ln m + k ln 2`) and the series is `2 atanh ((m-1)/(m+1))`, whose
/// argument stays below 1/3 there and so converges in a handful of terms.
pub def F64.ln (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.lt a 0.0 then F64.nan
    else if F64.is_zero a then F64.neg F64.infinity
    else if F64.is_infinite a then a
    else
        let k : I64 := F64.halvings2 a 0 in
        let m : F64 := F64.ldexp a (I64.sub 0 k) in
        // `m` is in [1, 2). At exactly 1 the series is 0 and the answer is
        // just `k ln 2`, which is what makes `ln` of a power of two exact
        // to the constant's own precision.
        let z : F64 := F64.div (F64.sub m 1.0) (F64.add m 1.0) in
        let series : F64 := F64.ln_series z (F64.mul z z) 0 32 z z in
        F64.add (F64.mul 2.0 series) (F64.mul (I64.to_f64 k) F64.ln_2)

/// The `atanh` series, `sum z^(2i+1)/(2i+1)`: `term` is `z^(2i+1)`, `acc`
/// already includes it, and each step multiplies by `zsq` and divides by
/// the next odd index.
#[terminating]
def F64.ln_series (z : F64) (zsq : F64) (i : I64) (n : I64) (acc : F64) (term : F64) : F64 :=
    if I64.beq i n then acc
    else
        let next : F64 := F64.mul term zsq in
        let idx : F64 := I64.to_f64 (I64.add (I64.mul i 2) 3) in
        F64.ln_series z zsq (I64.add i 1) n (F64.add acc (F64.div next idx)) next

/// Base-2 logarithm. Exact for a power of two, to the precision of
/// `F64.ln_2`.
pub def F64.log2 (a : F64) : F64 := F64.div (F64.ln a) F64.ln_2

/// Base-10 logarithm.
pub def F64.log10 (a : F64) : F64 := F64.div (F64.ln a) F64.ln_10

/// Logarithm of `a` in `base`. A base of 1.0 has no logarithm, so it
/// answers NaN rather than an infinity.
pub def F64.log_base (base : F64) (a : F64) : F64 :=
    if F64.beq base 1.0 then F64.nan else F64.div (F64.ln a) (F64.ln base)

/// `ln (1 + a)`, accurate for a small `a` where computing `1 + a` first
/// would round the argument away.
pub def F64.ln_1p (a : F64) : F64 :=
    if F64.lt (F64.abs a) 0.000001 then
        let a2 : F64 := F64.mul a a in
        F64.add (F64.sub a (F64.mul a2 0.5)) (F64.div (F64.mul a2 a) 3.0)
    else F64.ln (F64.add 1.0 a)

// ─── Powers ────────────────────────────────────────────────────────

/// `base ** n` for an INTEGER exponent: exactly rounded, because it is
/// repeated squaring rather than a transcendental. A negative exponent
/// answers `1 / base^|n|`.
pub def F64.pow (base : F64) (n : I64) : F64 :=
    if I64.lt n 0 then F64.div 1.0 (F64.pow_go base (I64.sub 0 n) 1.0)
    else F64.pow_go base n 1.0

/// The squaring loop of `F64.pow`.
#[terminating]
def F64.pow_go (base : F64) (n : I64) (acc : F64) : F64 :=
    if I64.beq n 0 then acc
    else if I64.beq (I64.rem n 2) 0 then F64.pow_go (F64.mul base base) (I64.div n 2) acc
    else F64.pow_go (F64.mul base base) (I64.div n 2) (F64.mul acc base)

/// `base ** exponent` for a possibly-fractional exponent, as
/// `exp (exponent * ln base)`.
///
/// A negative base has no real power for a non-integral exponent, so it
/// answers NaN; use `F64.pow` when the base may be negative and the
/// exponent is an integer. An integral exponent here is routed to
/// `F64.pow`, so `F64.pow_f64 2.0 10.0` is exactly 1024.
pub def F64.pow_f64 (base : F64) (exponent : F64) : F64 :=
    if F64.is_nan base then base
    else if F64.is_nan exponent then exponent
    else if F64.is_zero exponent then 1.0
    else if F64.is_zero base then (if F64.lt exponent 0.0 then F64.infinity else 0.0)
    else if F64.lt base 0.0 then F64.nan
    else if F64.is_integer exponent then F64.pow base (F64.to_i64 exponent)
    else F64.exp (F64.mul exponent (F64.ln base))

// ─── Trigonometry ──────────────────────────────────────────────────
//
// Sine reduces to one turn and then uses the Taylor series that is
// fastest near zero; cosine is `sin (a + pi/2)` rather than a second
// recurrence to keep in step with the first, at the cost documented at its
// own definition. The inverse functions are built on `atan`.

/// `a` with whole turns removed, landing in `[-pi, pi)`. The reduction is
/// one multiply-subtract against `F64.round (a / tau)`, so it stays O(1)
/// and is accurate wherever `a / tau` is itself exact.
pub def F64.reduce_turn (a : F64) : F64 :=
    let q : F64 := F64.round (F64.div a F64.tau) in
    F64.sub a (F64.mul q F64.tau)

/// Sine, by its Taylor series after the turn reduction. 24 terms hold a
/// relative error below 1e-16 across `[-pi, pi)`.
pub def F64.sin (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.is_infinite a then F64.nan
    else
        let m : F64 := F64.reduce_turn a in
        F64.sin_series m (F64.mul m m) 0 24 m m

/// The sine series, `sum (-1)^i m^(2i+1)/(2i+1)!`. `term` is the previous
/// term (starting at `m`, i.e. `i = 0`), `acc` the running sum, and one
/// step is the classic recurrence `-term * m^2 / ((2i+2)(2i+3))`.
#[terminating]
def F64.sin_series (m : F64) (msq : F64) (i : I64) (n : I64) (acc : F64) (term : F64) : F64 :=
    if I64.beq i n then acc
    else
        // The odd-indexed divisors: from term_i = m^(2i+1)/(2i+1)! the
        // next is term_i * m^2 / ((2i+2)(2i+3)). Using (i+2)(i+3) here
        // would make the series converge to the wrong value.
        let i2 : F64 := I64.to_f64 (I64.add (I64.mul i 2) 2) in
        let next : F64 :=
            F64.neg (F64.div (F64.mul term msq)
                (F64.mul i2 (F64.add i2 1.0))) in
        F64.sin_series m msq (I64.add i 1) n (F64.add acc next) next

/// Cosine, as `sin (a + pi/2)`.
///
/// One series instead of two recurrences. The cost is that a zero of `cos`
/// comes out at an ulp rather than exactly 0.0 -- equally true of a
/// dedicated series, because `pi/2` is not representable either.
pub def F64.cos (a : F64) : F64 :=
    if F64.is_nan a then a
    else F64.sin (F64.add a F64.half_pi)

/// Tangent, `sin a / cos a`. Near an odd multiple of `pi/2` the true value
/// is unbounded and the quotient answers a very large finite number rather
/// than an infinity, because `pi/2` is not exactly representable.
pub def F64.tan (a : F64) : F64 := F64.div (F64.sin a) (F64.cos a)

/// `1 / cos a`.
pub def F64.sec (a : F64) : F64 := F64.div 1.0 (F64.cos a)

/// `1 / sin a`.
pub def F64.csc (a : F64) : F64 := F64.div 1.0 (F64.sin a)

/// `cos a / sin a`.
pub def F64.cot (a : F64) : F64 := F64.div (F64.cos a) (F64.sin a)

// ─── Inverse trigonometry ──────────────────────────────────────────

/// Arctangent, in `(-pi/2, pi/2)`.
pub def F64.atan (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.lt a 0.0 then F64.sub 0.0 (F64.atan_pos (F64.sub 0.0 a))
    else F64.atan_pos a

/// Arctangent of a non-negative argument, in three regimes so each is
/// reached in a step or two: below 0.5 the series directly; above 1 the
/// reciprocal identity `atan a = pi/2 - atan (1/a)`; and in between the
/// halving identity `atan a = 2 atan (a / (1 + sqrt (1 + a^2)))`, which
/// takes `[0.5, 1]` straight down to at most 1/3.
#[terminating]
def F64.atan_pos (a : F64) : F64 :=
    if F64.lt a 0.5 then F64.atan_series a (F64.mul a a) 0 40 a a
    // `atan a = pi/2 - atan (1/a)` above 1. The halving identity below
    // would work here too but barely moves a large argument (1e6 becomes
    // 0.9999995), so the reciprocal is what actually converges.
    else if F64.gt a 1.0 then F64.sub F64.half_pi (F64.atan_pos (F64.div 1.0 a))
    // In [0.5, 1] one halving brings the argument to at most 1/3, where
    // the series converges in a handful of terms.
    else
        let denom : F64 := F64.add 1.0 (F64.sqrt (F64.add 1.0 (F64.mul a a))) in
        F64.mul 2.0 (F64.atan_pos (F64.div a denom))

/// `sum (-1)^i z^(2i+1)/(2i+1)`, alternating in place: the sign follows
/// the index's parity, so no carried sign is needed.
#[terminating]
def F64.atan_series (z : F64) (zsq : F64) (i : I64) (n : I64) (acc : F64) (term : F64) : F64 :=
    if I64.beq i n then acc
    else if F64.is_zero term then acc
    else
        let next : F64 := F64.mul term zsq in
        let idx : F64 := I64.to_f64 (I64.add (I64.mul i 2) 3) in
        let contribution : F64 := F64.div next idx in
        let signed : F64 :=
            if I64.beq (I64.rem i 2) 0 then F64.neg contribution else contribution in
        F64.atan_series z zsq (I64.add i 1) n (F64.add acc signed) next

/// Arctangent of `y/x`, using the signs of both to pick the quadrant:
/// `F64.atan2 1.0 (-1.0)` is `3 pi / 4`, where `F64.atan (y / x)` alone
/// would answer `-pi / 4`. This is the function to reach for when
/// converting Cartesian coordinates to polar.
pub def F64.atan2 (y : F64) (x : F64) : F64 :=
    if F64.is_nan x then x
    else if F64.is_nan y then y
    else if F64.gt x 0.0 then F64.atan (F64.div y x)
    else if F64.lt x 0.0 then
        if F64.lt y 0.0 then F64.sub (F64.atan (F64.div y x)) F64.pi
        else F64.add (F64.atan (F64.div y x)) F64.pi
    else if F64.gt y 0.0 then F64.half_pi
    else if F64.lt y 0.0 then F64.neg F64.half_pi
    else 0.0

/// Arcsine, in `[-pi/2, pi/2]`. An argument outside `[-1, 1]` is NaN, and
/// both endpoints are exact.
pub def F64.asin (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.gt a 1.0 then F64.nan
    else if F64.lt a (F64.sub 0.0 1.0) then F64.nan
    else if F64.beq a 1.0 then F64.half_pi
    else if F64.beq a (F64.sub 0.0 1.0) then F64.neg F64.half_pi
    // `asin a = atan (a / sqrt (1 - a^2))`. The endpoints would divide by
    // zero here, which is why they are answered above.
    else F64.atan (F64.div a (F64.sqrt (F64.sub 1.0 (F64.mul a a))))

/// Arccosine, in `[0, pi]`, as `pi/2 - asin a`, so it is exact where
/// `F64.asin` is.
pub def F64.acos (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.gt a 1.0 then F64.nan
    else if F64.lt a (F64.sub 0.0 1.0) then F64.nan
    else F64.sub F64.half_pi (F64.asin a)

// ─── Hyperbolic ────────────────────────────────────────────────────

/// `(e^a - e^-a) / 2`. Both exponentials come from one `F64.exp` call
/// (the second is its reciprocal), so the result is odd to the last bit:
/// `F64.sinh (-a)` is exactly `-(F64.sinh a)`.
pub def F64.sinh (a : F64) : F64 :=
    let ea : F64 := F64.exp a in
    F64.mul (F64.sub ea (F64.div 1.0 ea)) 0.5

/// `(e^a + e^-a) / 2`, always at least 1.
pub def F64.cosh (a : F64) : F64 :=
    let ea : F64 := F64.exp a in
    F64.mul (F64.add ea (F64.div 1.0 ea)) 0.5

/// `sinh a / cosh a`, computed as `(t - 1/t) / (t + 1/t)` with `t = e^a`,
/// so it neither overflows for a large argument nor loses the oddness
/// relation `F64.tanh (-a) = -(F64.tanh a)`.
pub def F64.tanh (a : F64) : F64 :=
    let ea : F64 := F64.exp a in
    let inv : F64 := F64.div 1.0 ea in
    F64.div (F64.sub ea inv) (F64.add ea inv)

/// Inverse hyperbolic sine, `ln (a + sqrt (a^2 + 1))`. The spelling stays
/// stable for negative arguments too, where `a + sqrt (a^2 + 1)` is still
/// positive.
pub def F64.asinh (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.gt (F64.abs a) 1000000000.0 then
        // `sqrt (a^2 + 1)` would overflow here, and `ln (2 |a|)` is the
        // limit to within an ulp.
        F64.add (F64.ln (F64.abs a)) F64.ln_2
    else F64.ln (F64.add a (F64.sqrt (F64.add (F64.mul a a) 1.0)))

/// Inverse hyperbolic cosine, `ln (a + sqrt (a^2 - 1))`, defined for
/// `a >= 1`. Below 1 the answer would be complex, so it is NaN.
pub def F64.acosh (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.lt a 1.0 then F64.nan
    else F64.ln (F64.add a (F64.sqrt (F64.sub (F64.mul a a) 1.0)))

/// Inverse hyperbolic tangent, `0.5 * ln ((1 + a) / (1 - a))`, defined on
/// the open interval `(-1, 1)`. The endpoints are the infinities the
/// formula tends to; outside them it is NaN.
pub def F64.atanh (a : F64) : F64 :=
    if F64.is_nan a then a
    else if F64.beq a 1.0 then F64.infinity
    else if F64.beq a (F64.sub 0.0 1.0) then F64.neg F64.infinity
    else if F64.gt (F64.abs a) 1.0 then F64.nan
    else F64.mul 0.5 (F64.ln (F64.div (F64.add 1.0 a) (F64.sub 1.0 a)))

// ─── Comparison helpers ────────────────────────────────────────────

/// Whether two floats are within `tolerance` of each other, by absolute
/// difference. Two NaNs are NOT close, themselves included.
pub def F64.approx (tolerance : F64) (a : F64) (b : F64) : Bool :=
    if F64.is_nan a then false
    else if F64.is_nan b then false
    else F64.lt (F64.abs (F64.sub a b)) tolerance

/// Whether two floats agree to a few ulp of their own magnitude: the
/// tolerance is `8 * epsilon * max (|a|, |b|, 1)`. The `1` floor is what
/// gives a comparison near zero room to work.
pub def F64.approx_rel (a : F64) (b : F64) : Bool :=
    let mag : F64 := F64.max (F64.max (F64.abs a) (F64.abs b)) 1.0 in
    F64.approx (F64.mul 8.0 (F64.mul F64.epsilon mag)) a b
