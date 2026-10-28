/// ISO-8601 parsing for the supported subset: `YYYY-MM-DD`, a `T`-separated
/// time of day, an optional fractional-second run of any length, and a `Z` or
/// `±HH:MM` offset.
///
/// Excluded by design: week dates, ordinal dates, reduced-precision dates and
/// repeating intervals.
///
/// The shape parsers return `Result TimeError …` rather than `ParseResult` so
/// `Date.of`/`Time.of` range errors keep their kind instead of collapsing to
/// `invalid_format`; the public `ParseResult` entry points are thin views.

use lib::types {Date, Time, DateTime, TimeError, TimeErrorKind}
use lib::internal {take_n_digits, parse_fraction}
use lib::date {Date.of}
use lib::time_of_day {Time.of}
use lib::error {TimeError.of, TimeError.message}
use parsec::core {ParseError, ParseResult}
use parsec::combinators {tag}
open ParseResult {fail, success}

def invalid (message : String) : TimeError :=
    TimeError.of TimeErrorKind.invalid_format message

def invalid_offset (message : String) : TimeError :=
    TimeError.of TimeErrorKind.invalid_offset message

/// Consume `expected` exactly, or fail with `invalid_format`.
def expect_tag (expected : String) (input : String) : Result TimeError String :=
    match tag expected input {
        success rem _ => ok rem,
        fail _ => err (invalid (String.concat "expected " expected))
    }

/// Consume exactly `n` digits, returning the value and the remainder.
def take_digits (n : I64) (input : String) (what : String) : Result TimeError (Pair I64 String) :=
    match take_n_digits n input {
        success rem value => ok (Pair.pair value rem),
        fail _ => err (invalid (String.concat "expected " (String.concat what " digits")))
    }

/// `YYYY-MM-DD`, validating through `Date.of`.
pub def Date.parse_iso (input : String) : ParseResult Date :=
    match parse_date_structured input {
        ok p => match p { Pair.pair date rem => success rem date },
        err e => fail (ParseError.custom (TimeError.message e) input)
    }

def parse_date_structured (input : String) : Result TimeError (Pair Date String) :=
    match take_digits 4 input "year" {
        ok p =>
            match p {
                Pair.pair year rem => parse_date_body year rem
            },
        err e => err e
    }

/// The `-MM-DD` tail after a four-digit year.
def parse_date_body (year : I64) (input : String) : Result TimeError (Pair Date String) :=
    match expect_tag "-" input {
        ok rem1 =>
            match take_digits 2 rem1 "month" {
                ok p1 =>
                    match p1 {
                        Pair.pair month rem2 =>
                            match expect_tag "-" rem2 {
                                ok rem3 =>
                                    match take_digits 2 rem3 "day" {
                                        ok p2 =>
                                            match p2 {
                                                Pair.pair day rem4 =>
                                                    match Date.of year month day {
                                                        ok date => ok (Pair.pair date rem4),
                                                        err e => err e
                                                    }
                                            },
                                        err e => err e
                                    },
                                err e => err e
                            }
                    },
                err e => err e
            },
        err e => err e
    }

/// `HH:MM:SS[.fraction]`, validating through `Time.of`.
def parse_time_body (input : String) : Result TimeError (Pair Time String) :=
    match take_digits 2 input "hour" {
        ok p1 =>
            match p1 {
                Pair.pair hour rem1 =>
                    match expect_tag ":" rem1 {
                        ok rem2 =>
                            match take_digits 2 rem2 "minute" {
                                ok p2 =>
                                    match p2 {
                                        Pair.pair minute rem3 =>
                                            match expect_tag ":" rem3 {
                                                ok rem4 =>
                                                    match take_digits 2 rem4 "second" {
                                                        ok p3 =>
                                                            match p3 {
                                                                Pair.pair second rem5 =>
                                                                    parse_time_finish hour minute second rem5
                                                            },
                                                        err e => err e
                                                    },
                                                err e => err e
                                            }
                                    },
                                err e => err e
                            },
                        err e => err e
                    }
            },
        err e => err e
    }

/// The optional fraction after the seconds, then validation.
def parse_time_finish (hour : I64) (minute : I64) (second : I64) (rem : String) : Result TimeError (Pair Time String) :=
    if String.slice rem 0 1 == "."
    then parse_time_fraction hour minute second rem
    else make_time hour minute second 0 rem

def parse_time_fraction (hour : I64) (minute : I64) (second : I64) (rem : String) : Result TimeError (Pair Time String) :=
    match parse_fraction rem {
        success rem2 nanos => make_time hour minute second nanos rem2,
        fail _ => err (invalid "expected digit after '.'")
    }

def make_time (hour : I64) (minute : I64) (second : I64) (nanos : I64) (rem : String) : Result TimeError (Pair Time String) :=
    match Time.of hour minute second nanos {
        ok time => ok (Pair.pair time rem),
        err e => err e
    }

/// `Z` / `±HH:MM` -> offset in minutes east of UTC.
pub def parse_offset (input : String) : ParseResult I64 :=
    match parse_offset_structured input {
        ok p => match p { Pair.pair value rem => success rem value },
        err e => fail (ParseError.custom (TimeError.message e) input)
    }

def parse_offset_structured (input : String) : Result TimeError (Pair I64 String) :=
    let first := String.slice input 0 1 in
    if first == "Z"
    then ok (Pair.pair 0 (String.drop 1 input))
    else if first == "+"
    then parse_offset_sign 1 (String.drop 1 input)
    else if first == "-"
    then parse_offset_sign (-1) (String.drop 1 input)
    else err (invalid_offset "expected Z, +HH:MM or -HH:MM")

def parse_offset_sign (sign : I64) (input : String) : Result TimeError (Pair I64 String) :=
    match take_digits 2 input "offset hour" {
        ok p1 =>
            match p1 {
                Pair.pair hours rem1 =>
                    match expect_tag ":" rem1 {
                        ok rem2 =>
                            match take_digits 2 rem2 "offset minute" {
                                ok p2 =>
                                    match p2 {
                                        Pair.pair minutes rem3 =>
                                            if hours <= 23 && minutes <= 59
                                            then ok (Pair.pair (I64.mul sign (I64.add (I64.mul hours 60) minutes)) rem3)
                                            else err (invalid_offset "offset out of range")
                                    },
                                err _ => err (invalid_offset "expected +HH:MM or -HH:MM")
                            },
                        err _ => err (invalid_offset "expected +HH:MM or -HH:MM")
                    }
            },
        err _ => err (invalid_offset "expected +HH:MM or -HH:MM")
    }

/// Parse the whole `YYYY-MM-DDTHH:MM:SS[.fraction](Z|±HH:MM)` form, returning
/// the value and the unconsumed remainder.
def DateTime.parse_body (s : String) : Result TimeError (Pair DateTime String) :=
    match parse_date_structured s {
        ok p1 =>
            match p1 {
                Pair.pair date rem1 =>
                    match expect_tag "T" rem1 {
                        ok rem2 =>
                            match parse_time_body rem2 {
                                ok p2 =>
                                    match p2 {
                                        Pair.pair time rem3 =>
                                            match parse_offset_structured rem3 {
                                                ok p3 =>
                                                    match p3 {
                                                        Pair.pair offset rem4 =>
                                                            let dt : DateTime :=
                                                                { date := date, time := time, offset_minutes := offset }
                                                            in
                                                            ok (Pair.pair dt rem4)
                                                    },
                                                err e => err e
                                            }
                                    },
                                err e => err e
                            },
                        err e => err e
                    }
            },
        err e => err e
    }

/// Parse a complete ISO-8601 local date/time with an explicit offset.
///
/// `Z` and `±HH:MM` are the only accepted suffixes; trailing input is
/// rejected as `other`.
pub def DateTime.parse (s : String) : Result TimeError DateTime :=
    match DateTime.parse_body s {
        ok p =>
            match p {
                Pair.pair dt rem =>
                    if String.is_empty rem
                    then ok dt
                    else err (TimeError.of TimeErrorKind.other "unexpected trailing input")
            },
        err e => err e
    }
