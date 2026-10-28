/// `Duration` normalization, named arithmetic, the homogeneous `-` instance,
/// and formatting.

use lib::types {Duration}
use lib::duration {
    Duration.zero,
    Duration.of_seconds,
    Duration.of_nanos,
    Duration.add,
    Duration.sub,
    Duration.scale,
    Duration.div_by,
    Duration.format
}

/// Whether `d` has exactly this normalized `(secs, nanos)` pair.
def duration_is (d : Duration) (secs : I64) (nanos : I64) : Bool :=
    match d {
        mk s n => s == secs && n == nanos
    }

#[test]
def test_zero_is_normalized : Bool :=
    duration_is Duration.zero 0 0

#[test]
def test_of_nanos_minus_one_carries_into_secs : Bool :=
    duration_is (Duration.of_nanos (-1)) (-1) 999999999

#[test]
def test_of_nanos_minus_one_billion_and_one : Bool :=
    duration_is (Duration.of_nanos (-1000000001)) (-2) 999999999

#[test]
def test_of_seconds_is_normalized : Bool :=
    duration_is (Duration.of_seconds 5) 5 0

#[test]
def test_add_carries_nanos : Bool :=
    duration_is
        (Duration.add (Duration.of_nanos 600000000) (Duration.of_nanos 600000000))
        1 200000000

#[test]
def test_add_negative_span : Bool :=
    duration_is
        (Duration.add (Duration.of_seconds (-1)) (Duration.of_nanos (-500000000)))
        (-2) 500000000

#[test]
def test_sub_roundtrip : Bool :=
    Duration.sub (Duration.add (Duration.of_seconds 5) (Duration.of_seconds 7))
        (Duration.of_seconds 7) == Duration.of_seconds 5

#[test]
def test_scale_positive : Bool :=
    Duration.scale (Duration.of_seconds 5) 3 == Duration.of_seconds 15

#[test]
def test_scale_negative : Bool :=
    Duration.scale (Duration.of_seconds 5) (-2) == Duration.of_seconds (-10)

#[test]
def test_scale_carries : Bool :=
    duration_is (Duration.scale (Duration.of_nanos 600000000) 2) 1 200000000

#[test]
def test_div_by_positive : Bool :=
    Duration.div_by (Duration.of_seconds 15) 3 == Duration.of_seconds 5

#[test]
def test_div_by_keeps_remainder : Bool :=
    Duration.div_by (Duration.of_nanos 1500000000) 2 == Duration.of_nanos 750000000

#[test]
def test_homogeneous_sub_operator : Bool :=
    (Duration.of_seconds 9 - Duration.of_seconds 4) == Duration.of_seconds 5

#[test]
def test_show_duration_positive : Bool :=
    let d : Duration := Duration.of_nanos 1500000000 in
    Duration.format d == "1.500000000s"

#[test]
def test_show_duration_negative : Bool :=
    let d : Duration := Duration.of_nanos (-1500000000) in
    Duration.format d == "-1.500000000s"

#[test]
def test_show_duration_zero : Bool :=
    Duration.format Duration.zero == "0.000000000s"
