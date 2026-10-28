/// `DateTime` instant conversion, instant-based equality across offsets,
/// boundary arithmetic, and ISO formatting.

use lib::types {Date, DateTime}
use lib::date {Date.of}
use lib::time_of_day {Time.of}
use lib::duration {Duration.of_seconds}
use lib::instant {Instant.add_duration}
use lib::datetime {DateTime.of_instant, DateTime.to_instant, DateTime.to_iso}

def with_time (date : Date) (h : I64) (mi : I64) (s : I64) (nanos : I64) (offset : I64) : Option DateTime :=
    match Time.of h mi s nanos {
        ok time =>
            let dt : DateTime := { date := date, time := time, offset_minutes := offset } in
            some dt,
        err _ => none
    }

def dt_at (y : I64) (m : I64) (d : I64) (h : I64) (mi : I64) (s : I64) (nanos : I64) (offset : I64) : Option DateTime :=
    match Date.of y m d {
        ok date => with_time date h mi s nanos offset,
        err _ => none
    }

#[test]
def test_datetime_roundtrips_utc_instant : Bool :=
    match dt_at 2024 1 15 10 30 0 0 0 {
        some dt =>
            DateTime.to_iso (DateTime.of_instant (DateTime.to_instant dt) 0) == "2024-01-15T10:30:00Z",
        none => false
    }

/// The plan's Finding-4 gate: equal instants under different written offsets
/// compare equal, even though their renderings differ.
#[test]
def test_datetime_equality_is_by_instant : Bool :=
    match dt_at 2024 1 15 10 0 0 0 60 {
        some a =>
            match dt_at 2024 1 15 9 0 0 0 0 {
                some b => a == b && Bool.not (DateTime.to_iso a == DateTime.to_iso b),
                none => false
            },
        none => false
    }

#[test]
def test_datetime_month_boundary : Bool :=
    match dt_at 2024 1 31 23 0 0 0 0 {
        some start =>
            let later := Instant.add_duration (DateTime.to_instant start) (Duration.of_seconds 7200) in
            DateTime.to_iso (DateTime.of_instant later 0) == "2024-02-01T01:00:00Z",
        none => false
    }

#[test]
def test_datetime_year_boundary : Bool :=
    match dt_at 2024 12 31 23 30 0 0 0 {
        some start =>
            let later := Instant.add_duration (DateTime.to_instant start) (Duration.of_seconds 3600) in
            DateTime.to_iso (DateTime.of_instant later 0) == "2025-01-01T00:30:00Z",
        none => false
    }

#[test]
def test_show_datetime_with_fraction_and_positive_offset : Bool :=
    match dt_at 2024 1 15 10 30 0 123000000 120 {
        some dt => DateTime.to_iso dt == "2024-01-15T10:30:00.123+02:00",
        none => false
    }

#[test]
def test_show_datetime_with_negative_offset : Bool :=
    match dt_at 2024 1 15 10 30 0 0 (-300) {
        some dt => DateTime.to_iso dt == "2024-01-15T10:30:00-05:00",
        none => false
    }

#[test]
def test_show_datetime_without_fraction : Bool :=
    match dt_at 2024 1 15 10 30 0 0 0 {
        some dt => DateTime.to_iso dt == "2024-01-15T10:30:00Z",
        none => false
    }
