/// `IO.epoch_time_nano` reads the wall clock on every backend.
use std::io {IO.epoch_time_nano}

/// 2020-01-01T00:00:00Z in nanoseconds since the Unix epoch.
def year_2020_ns : I64 := 1577836800000000000

#[test]
def test_epoch_time_is_a_real_timestamp : IO Bool := do {
    let t <- IO.epoch_time_nano;
    IO.pure (t > year_2020_ns)
}

/// Two reads land within a second of each other: nanoseconds, one clock.
/// (Not `b >= a`: a wall-clock step can move it backwards.)
#[test]
def test_epoch_time_reads_agree : IO Bool := do {
    let a <- IO.epoch_time_nano;
    let b <- IO.epoch_time_nano;
    let d : I64 := if b > a then b - a else a - b;
    IO.pure (d < 1000000000)
}
