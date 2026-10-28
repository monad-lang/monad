/// `Time` (time of day) construction and formatting.
///
/// Named `time_of_day.mo` rather than `time.mo` so the module path does not
/// read as `time::time`.

use lib::types {Time, TimeError, TimeErrorKind}
use lib::internal {pad2, pad9, trim_trailing_zeros}
use lib::error {TimeError.of}
use std::show {Show}

/// Validate and build a time of day.
///
/// No leap seconds: `second` is restricted to `[0, 59]`, so `23:59:60` is
/// `second_out_of_range`.
pub def Time.of (hour : I64) (minute : I64) (second : I64) (nanos : I64) : Result TimeError Time :=
    if hour < 0 || hour > 23
    then err (TimeError.of TimeErrorKind.hour_out_of_range "hour must be in [0, 23]")
    else if minute < 0 || minute > 59
    then err (TimeError.of TimeErrorKind.minute_out_of_range "minute must be in [0, 59]")
    else if second < 0 || second > 59
    then err (TimeError.of TimeErrorKind.second_out_of_range "second must be in [0, 59]")
    else if nanos < 0 || nanos > 999999999
    then err (TimeError.of TimeErrorKind.nanos_out_of_range "nanos must be in [0, 999999999]")
    else ok ({ hour := hour, minute := minute, second := second, nanos := nanos } : Time)

/// `HH:MM:SS`, with `.fraction` only when the nanosecond field is non-zero.
/// Trailing zeroes are trimmed but at least one digit is kept, so `.1`,
/// `.123` and `.123456789` all survive a `Show`/parse round-trip.
pub def Time.to_iso (t : Time) : String :=
    match t {
        mk hour minute second nanos =>
            let base := String.concat_all [pad2 hour, ":", pad2 minute, ":", pad2 second] in
            if nanos == 0
            then base
            else String.concat base (String.concat "." (trim_trailing_zeros (pad9 nanos)))
    }

/// `HH:MM:SS[.fraction]`.
pub instance Show Time {
    def show (t : Time) : String := Time.to_iso t
}
