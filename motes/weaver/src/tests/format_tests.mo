/// The live line's formatters, at their boundaries.
use weaver::format {format_tokens, format_elapsed}

#[test]
def test_tokens_under_a_thousand_are_raw : Bool :=
    format_tokens 0 == "0" && format_tokens 999 == "999"

#[test]
def test_tokens_abbreviate_thousands : Bool :=
    format_tokens 1000 == "1k"
        && format_tokens 1234 == "1.2k"
        && format_tokens 999999 == "999.9k"

#[test]
def test_tokens_abbreviate_millions : Bool :=
    format_tokens 1000000 == "1M" && format_tokens 1234567 == "1.2M"

#[test]
def test_tokens_clamp_negative : Bool := format_tokens (0 - 5) == "0"

#[test]
def test_elapsed_under_ten_seconds_has_a_decimal : Bool :=
    format_elapsed 34 == "3.4s" && format_elapsed 0 == "0s" && format_elapsed 99 == "9.9s"

#[test]
def test_elapsed_under_a_minute_is_whole_seconds : Bool :=
    format_elapsed 100 == "10s" && format_elapsed 599 == "59s"

#[test]
def test_elapsed_minutes_zero_pad : Bool :=
    format_elapsed 600 == "1m 00s" && format_elapsed 640 == "1m 04s"

#[test]
def test_elapsed_clamps_negative : Bool := format_elapsed (0 - 10) == "0s"
