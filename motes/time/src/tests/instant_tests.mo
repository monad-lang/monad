/// `Instant` arithmetic, chronological ordering, and the clock read.

use lib::types {Instant, Duration}
use lib::duration {Duration.of_seconds, Duration.of_nanos}
use lib::instant {Instant.add_duration, Instant.sub_duration, Instant.diff, Instant.now}
use std::base {Ord, Ordering}

/// Build a normalized `Instant` directly (the public constructors live on
/// `Date`/`Time`; an instant of known fields needs no validation).
def instant_at (secs : I64) (nanos : I64) : Instant :=
    let i : Instant := { epoch_sec := secs, nanos := nanos } in
    i

def add_then_sub_is_identity (a : Instant) (d : Duration) : Bool :=
    Instant.sub_duration (Instant.add_duration a d) d == a

#[test]
def test_instant_add_then_sub_positive_span : Bool :=
    add_then_sub_is_identity (instant_at 1700000000 250000000) (Duration.of_seconds 90)

#[test]
def test_instant_add_then_sub_negative_span : Bool :=
    add_then_sub_is_identity (instant_at 1700000000 250000000) (Duration.of_seconds (-90))

#[test]
def test_instant_add_carries_nanos : Bool :=
    Instant.add_duration (instant_at 0 600000000) (Duration.of_nanos 600000000)
        == instant_at 1 200000000

#[test]
def test_instant_add_negative_nanos_normalizes : Bool :=
    Instant.add_duration (instant_at 0 0) (Duration.of_nanos (-1))
        == instant_at (-1) 999999999

#[test]
def test_instant_diff_whole_seconds : Bool :=
    Instant.diff (instant_at 15 0) (instant_at 10 0) == Duration.of_seconds 5

#[test]
def test_instant_diff_with_nanos : Bool :=
    Instant.diff (instant_at 11 250000000) (instant_at 10 750000000)
        == Duration.of_nanos 500000000

#[test]
def test_instant_derived_order : Bool :=
    instant_at 10 0 < instant_at 11 0
        && instant_at 10 1 > instant_at 10 0
        && instant_at (-1) 999999999 < instant_at 0 0

#[test]
def test_instant_ord_compare_equal : Bool :=
    match Ord.compare (instant_at 10 0) (instant_at 10 0) {
        Ordering.lt => false,
        Ordering.eq => true,
        Ordering.gt => false
    }

def is_non_negative (i : Instant) : Bool :=
    match Ord.compare (instant_at 0 0) i {
        Ordering.lt => true,
        Ordering.eq => true,
        Ordering.gt => false
    }

/// The clock read is only asserted to be non-negative: the web profile is
/// epoch-based, while native/wasi compiled binaries use a monotonic origin.
#[test]
def test_instant_now_is_non_negative : IO Bool := do {
    let i <- Instant.now;
    return (is_non_negative i)
}
