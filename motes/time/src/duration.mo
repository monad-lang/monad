/// `Duration` construction, arithmetic and formatting.
///
/// Arithmetic is named (`Duration.add`, `Duration.sub`, `Duration.scale`,
/// `Duration.div_by`) rather than operator-driven: heterogeneous arithmetic
/// instances cannot be selected by either compiler today (see
/// `plans/implementations/multi-param-instance-resolution.md`), and `+` is
/// rebound to `I64.add` on the Rust host. `Duration - Duration` is safe
/// (a homogeneous `Sub` instance) and is provided; never spell `+` on a
/// `Duration`.

use lib::types {Duration}
use lib::internal {i64_floor_div, i64_floor_mod, pad9}
use std::show {Show}

/// Carry an arbitrary nanosecond component back into `[0, 999999999]`.
/// Package-private: every constructor funnels through it, which is what
/// keeps derived `BOrd`'s lexicographic `(secs, nanos)` order chronological.
def Duration.normalize (secs : I64) (nanos : I64) : Duration :=
    let carry := i64_floor_div nanos 1000000000 in
    let rem := i64_floor_mod nanos 1000000000 in
    let d : Duration := { secs := secs + carry, nanos := rem } in
    d

/// The zero span.
pub def Duration.zero : Duration := Duration.normalize 0 0

/// A span of `n` whole seconds (negative for a negative span).
pub def Duration.of_seconds (n : I64) : Duration := Duration.normalize n 0

/// A span of `n` nanoseconds. Negative values normalize so the remainder is
/// non-negative: `of_nanos (-1)` is `{ secs := -1, nanos := 999999999 }`.
pub def Duration.of_nanos (n : I64) : Duration := Duration.normalize 0 n

/// The sum of two spans.
pub def Duration.add (a : Duration) (b : Duration) : Duration :=
    match a {
        mk a_secs a_nanos =>
            match b {
                mk b_secs b_nanos =>
                    Duration.normalize (I64.add a_secs b_secs) (I64.add a_nanos b_nanos)
            }
    }

/// The difference of two spans.
pub def Duration.sub (a : Duration) (b : Duration) : Duration :=
    match a {
        mk a_secs a_nanos =>
            match b {
                mk b_secs b_nanos =>
                    Duration.normalize (I64.sub a_secs b_secs) (I64.sub a_nanos b_nanos)
            }
    }

/// Scale a span by an integer count (a negative count flips its sign).
pub def Duration.scale (d : Duration) (n : I64) : Duration :=
    match d {
        mk secs nanos =>
            Duration.normalize (I64.mul secs n) (I64.mul nanos n)
    }

/// Divide a span by a positive integer count, rounding toward negative
/// infinity. The division goes through total nanoseconds so the remainder
/// carried from `secs` is not lost. Requires `n > 0`.
pub def Duration.div_by (d : Duration) (n : I64) : Duration :=
    match d {
        mk secs nanos =>
            let total := I64.add (I64.mul secs 1000000000) nanos in
            let per := i64_floor_div total n in
            Duration.normalize (i64_floor_div per 1000000000) (i64_floor_mod per 1000000000)
    }

/// `Duration - Duration`, through the homogeneous `Sub` class. This is the
/// one duration operator that is portable across both compilers.
pub instance Sub Duration {
    def sub (a b : Duration) : Duration := Duration.sub a b
}

/// Reachable as `Add.add`. Deliberately not spelled with `+`: the Rust host
/// resolves `+` to `I64.add` (init/lib.mo's rebinding wins there).
pub instance Add Duration {
    def add (a b : Duration) : Duration := Duration.add a b
}

/// Signed decimal seconds with nine fractional digits: `1.500000000s`,
/// `-1.500000000s`, `0.000000000s`.
pub def Duration.format (d : Duration) : String :=
    match d {
        mk secs nanos =>
            let total := I64.add (I64.mul secs 1000000000) nanos in
            let negative := total < 0 in
            let magnitude := if negative then I64.neg total else total in
            let whole := i64_floor_div magnitude 1000000000 in
            let frac := i64_floor_mod magnitude 1000000000 in
            String.concat_all [
                (if negative then "-" else ""),
                I64.to_string whole,
                ".",
                pad9 frac,
                "s"
            ]
    }

/// Signed decimal seconds with nine fractional digits.
pub instance Show Duration {
    def show (d : Duration) : String := Duration.format d
}
