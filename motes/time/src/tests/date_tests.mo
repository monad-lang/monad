/// `Date` validation, leap-year/month-length rules, the day-count round trip
/// across century boundaries (which is what validates the Hinnant
/// transcription), and ISO formatting.

use lib::types {Date, TimeError, TimeErrorKind}
use lib::date {Date.of, Date.to_epoch_day, Date.of_epoch_day, Date.is_leap_year, Date.days_in_month, Date.to_iso}
use lib::error {TimeError.kind}

/// Whether `r` produced exactly `y-m-d`.
def date_is (r : Result TimeError Date) (y : I64) (m : I64) (d : I64) : Bool :=
    match r {
        ok date =>
            match date {
                mk yy mm dd => yy == y && mm == m && dd == d
            },
        err _ => false
    }

/// Whether `r` failed with kind `k`.
def failed_with (r : Result TimeError Date) (k : TimeErrorKind) : Bool :=
    match r {
        ok _ => false,
        err e => BEq.beq (TimeError.kind e) k
    }

#[test]
def test_date_of_accepts_leap_day : Bool :=
    date_is (Date.of 2024 2 29) 2024 2 29

#[test]
def test_date_of_rejects_non_leap_feb_29 : Bool :=
    failed_with (Date.of 2023 2 29) TimeErrorKind.day_out_of_range

#[test]
def test_date_of_rejects_feb_30 : Bool :=
    failed_with (Date.of 2024 2 30) TimeErrorKind.day_out_of_range

#[test]
def test_date_of_rejects_month_13 : Bool :=
    failed_with (Date.of 2024 13 1) TimeErrorKind.month_out_of_range

#[test]
def test_date_of_rejects_year_0 : Bool :=
    failed_with (Date.of 0 1 1) TimeErrorKind.year_out_of_range

#[test]
def test_date_of_rejects_year_10000 : Bool :=
    failed_with (Date.of 10000 1 1) TimeErrorKind.year_out_of_range

#[test]
def test_leap_year_rules : Bool :=
    Date.is_leap_year 2000 && Date.is_leap_year 2024
        && Bool.not (Date.is_leap_year 1900)
        && Bool.not (Date.is_leap_year 2100)
        && Bool.not (Date.is_leap_year 2023)

#[test]
def test_days_in_month : Bool :=
    Date.days_in_month 2024 2 == 29
        && Date.days_in_month 2023 2 == 28
        && Date.days_in_month 2024 4 == 30
        && Date.days_in_month 2024 12 == 31

/// `of_epoch_day . to_epoch_day` is the identity for valid dates.
def roundtrips (y : I64) (m : I64) (d : I64) : Bool :=
    match Date.of y m d {
        ok date =>
            match Date.of_epoch_day (Date.to_epoch_day date) {
                mk yy mm dd => yy == y && mm == m && dd == d
            },
        err _ => false
    }

#[test]
def test_epoch_day_roundtrip_lower_bound : Bool := roundtrips 1 1 1

#[test]
def test_epoch_day_roundtrip_epoch : Bool := roundtrips 1970 1 1

#[test]
def test_epoch_day_roundtrip_400_year_leap : Bool := roundtrips 2000 2 29

#[test]
def test_epoch_day_roundtrip_ordinary_leap : Bool := roundtrips 2024 2 29

#[test]
def test_epoch_day_roundtrip_non_leap_century : Bool := roundtrips 2100 2 28

#[test]
def test_epoch_day_roundtrip_upper_bound : Bool := roundtrips 9999 12 31

#[test]
def test_show_date_is_iso : Bool :=
    let d : Date := { year := 2024, month := 1, day := 5 } in
    Date.to_iso d == "2024-01-05"

#[test]
def test_show_date_pads_year : Bool :=
    let d : Date := { year := 7, month := 2, day := 9 } in
    Date.to_iso d == "0007-02-09"
