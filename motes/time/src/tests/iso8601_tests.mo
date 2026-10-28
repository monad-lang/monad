/// ISO-8601 parse/show round-trips, offset parsing, fractional precision, and
/// structured error kinds.

use lib::types {TimeErrorKind}
use lib::date {Date.to_iso}
use lib::datetime {DateTime.to_iso}
use lib::iso8601 {Date.parse_iso, DateTime.parse, parse_offset}
use lib::error {TimeError.kind}
use parsec::core {ParseResult}
open ParseResult {success, fail}

def date_parses_to (s : String) (shown : String) : Bool :=
    match Date.parse_iso s {
        success rem date => String.is_empty rem && Date.to_iso date == shown,
        fail _ => false
    }

def roundtrips (s : String) : Bool :=
    match DateTime.parse s {
        ok dt => DateTime.to_iso dt == s,
        err _ => false
    }

def parse_failed_with (s : String) (k : TimeErrorKind) : Bool :=
    match DateTime.parse s {
        ok _ => false,
        err e => BEq.beq (TimeError.kind e) k
    }

#[test]
def test_parse_date_iso : Bool :=
    date_parses_to "2024-01-15" "2024-01-15"

#[test]
def test_parse_date_iso_rejects_bad_month : Bool :=
    match Date.parse_iso "2024-13-01" {
        success _ _ => false,
        fail _ => true
    }

#[test]
def test_parse_utc_datetime : Bool :=
    roundtrips "2024-01-15T10:30:00Z"

#[test]
def test_parse_positive_offset : Bool :=
    roundtrips "2024-01-15T10:30:00.123+02:00"

#[test]
def test_parse_negative_offset : Bool :=
    roundtrips "2024-01-15T10:30:00-05:00"

#[test]
def test_parse_single_fraction_digit : Bool :=
    roundtrips "2024-01-15T10:30:00.1Z"

#[test]
def test_parse_nine_fraction_digits : Bool :=
    roundtrips "2024-01-15T10:30:00.123456789Z"

#[test]
def test_parse_offset_z : Bool :=
    match parse_offset "Z" {
        success rem value => String.is_empty rem && value == 0,
        fail _ => false
    }

#[test]
def test_parse_offset_positive : Bool :=
    match parse_offset "+02:00" {
        success rem value => String.is_empty rem && value == 120,
        fail _ => false
    }

#[test]
def test_parse_offset_negative : Bool :=
    match parse_offset "-05:00" {
        success rem value => String.is_empty rem && value == (-300),
        fail _ => false
    }

#[test]
def test_parse_rejects_bad_month_with_kind : Bool :=
    parse_failed_with "2024-13-01T00:00:00Z" TimeErrorKind.month_out_of_range

#[test]
def test_parse_rejects_feb_30_with_kind : Bool :=
    parse_failed_with "2024-02-30T00:00:00Z" TimeErrorKind.day_out_of_range

#[test]
def test_parse_rejects_hour_25_with_kind : Bool :=
    parse_failed_with "2024-01-15T25:00:00Z" TimeErrorKind.hour_out_of_range

#[test]
def test_parse_rejects_minute_60_with_kind : Bool :=
    parse_failed_with "2024-01-15T10:60:00Z" TimeErrorKind.minute_out_of_range

#[test]
def test_parse_rejects_second_60_with_kind : Bool :=
    parse_failed_with "2024-01-15T10:30:60Z" TimeErrorKind.second_out_of_range

#[test]
def test_parse_rejects_offset_25_with_kind : Bool :=
    parse_failed_with "2024-01-15T10:30:00+25:00" TimeErrorKind.invalid_offset

#[test]
def test_parse_rejects_malformed_offset_with_kind : Bool :=
    parse_failed_with "2024-01-15T10:30:00+2:00" TimeErrorKind.invalid_offset

#[test]
def test_parse_rejects_missing_offset_with_kind : Bool :=
    parse_failed_with "2024-01-15T10:30:00" TimeErrorKind.invalid_offset

#[test]
def test_parse_rejects_garbage_with_invalid_format : Bool :=
    parse_failed_with "not-a-date" TimeErrorKind.invalid_format

#[test]
def test_parse_rejects_trailing_input_as_other : Bool :=
    parse_failed_with "2024-01-15T10:30:00Zjunk" TimeErrorKind.other
