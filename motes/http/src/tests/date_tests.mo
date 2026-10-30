/// HTTP-date (IMF-fixdate) formatting and parsing.

use std::test {}
use http::date {Http.Date.imf_fixdate, Http.Date.parse_imf_fixdate}

#[test]
def test_epoch_zero_formats : Bool :=
  String.beq (Http.Date.imf_fixdate 0i64) "Thu, 01 Jan 1970 00:00:00 GMT"

#[test]
def test_rfc_example_formats : Bool :=
  String.beq (Http.Date.imf_fixdate 784111777i64) "Sun, 06 Nov 1994 08:49:37 GMT"

#[test]
def test_leap_day_formats : Bool :=
  String.beq (Http.Date.imf_fixdate 951782400i64) "Tue, 29 Feb 2000 00:00:00 GMT"

#[test]
def test_parse_rfc_example : Bool :=
  match Http.Date.parse_imf_fixdate "Sun, 06 Nov 1994 08:49:37 GMT" {
    Option.some e => I64.beq e 784111777i64,
    Option.none => false
  }

#[test]
def test_parse_rejects_garbage : Bool :=
  match Http.Date.parse_imf_fixdate "not a date" {
    Option.some _ => false,
    Option.none => true
  }

#[test]
def test_parse_rejects_negative_year : Bool :=
  match Http.Date.parse_imf_fixdate "Sun, 06 Nov 1900 08:49:37 GMT" {
    Option.some _ => false,
    Option.none => true
  }

#[test]
def test_roundtrip : Bool :=
  match Http.Date.parse_imf_fixdate (Http.Date.imf_fixdate 1700000000i64) {
    Option.some e => I64.beq e 1700000000i64,
    Option.none => false
  }
