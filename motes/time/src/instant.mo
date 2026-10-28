/// `Instant` arithmetic and ordering, plus the clock read.
///
/// Cross-type arithmetic is named (`Instant.add_duration`,
/// `Instant.sub_duration`, `Instant.diff`) because heterogeneous arithmetic
/// instances cannot be selected by either compiler today. `Instant` values
/// are always normalized, so the derived `BOrd` order is chronological.

use lib::types {Instant, Duration}
use lib::internal {i64_floor_div, i64_floor_mod}
use lib::duration {Duration.normalize}
use std::io {IO.current_time_nano}
use std::base {Ord, Ordering}
open Ordering {eq, gt, lt}

/// Carry an arbitrary nanosecond component back into `[0, 999999999]`.
/// Package-private; every constructor funnels through it.
def Instant.normalize (epoch_sec : I64) (nanos : I64) : Instant :=
    let carry := i64_floor_div nanos 1000000000 in
    let rem := i64_floor_mod nanos 1000000000 in
    let i : Instant := { epoch_sec := epoch_sec + carry, nanos := rem } in
    i

/// Move an instant forward by a span (a negative span moves it backwards).
pub def Instant.add_duration (i : Instant) (d : Duration) : Instant :=
    match i {
        mk i_secs i_nanos =>
            match d {
                mk d_secs d_nanos =>
                    Instant.normalize (I64.add i_secs d_secs) (I64.add i_nanos d_nanos)
            }
    }

/// Move an instant backward by a span (a negative span moves it forwards).
pub def Instant.sub_duration (i : Instant) (d : Duration) : Instant :=
    match i {
        mk i_secs i_nanos =>
            match d {
                mk d_secs d_nanos =>
                    Instant.normalize (I64.sub i_secs d_secs) (I64.sub i_nanos d_nanos)
            }
    }

/// The span from `b` to `a` (`a - b` in the usual sense).
pub def Instant.diff (a : Instant) (b : Instant) : Duration :=
    match a {
        mk a_secs a_nanos =>
            match b {
                mk b_secs b_nanos =>
                    Duration.normalize (I64.sub a_secs b_secs) (I64.sub a_nanos b_nanos)
            }
    }

/// Three-way chronological comparison.
pub instance Ord Instant {
    def compare (a b : Instant) : Ordering :=
        match a {
            mk a_secs a_nanos =>
                match b {
                    mk b_secs b_nanos =>
                        if a_secs < b_secs then lt
                        else if a_secs > b_secs then gt
                        else if a_nanos < b_nanos then lt
                        else if a_nanos > b_nanos then gt
                        else eq
                }
        }
}

/// The current instant from `IO.current_time_nano`.
///
/// That clock read is epoch-based under the interpreter and the web profile,
/// but `CLOCK_MONOTONIC` at an arbitrary origin in native/wasi compiled
/// binaries -- a pre-existing runtime divergence this mote inherits as-is.
/// Use it for ordering and differences; do not assume compiled native values
/// are Unix timestamps.
pub def Instant.now : IO Instant := do {
    let t <- IO.current_time_nano;
    return (Instant.normalize (i64_floor_div t 1000000000) (i64_floor_mod t 1000000000))
}
