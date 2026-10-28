/// `DateTime`: instant conversion, instant-based equality/ordering, and
/// ISO-8601 formatting.
///
/// `DateTime` stores local calendar fields plus a fixed UTC offset. Its
/// `BEq`/`Ord` deliberately compare the represented instant, not the written
/// fields, so `10:00+01:00` and `09:00+00:00` are equal. A caller that wants
/// representation equality matches the three fields directly.

use lib::types {Time, Instant, DateTime}
use lib::internal {i64_floor_div, i64_floor_mod, pad2}
use lib::date {Date.to_epoch_day, Date.of_epoch_day, Date.to_iso}
use lib::time_of_day {Time.to_iso}
use lib::instant {Instant.normalize}
use std::show {Show}
use std::base {Ord, Ordering}

/// `Z` at offset 0, otherwise `+HH:MM` / `-HH:MM`.
def offset_suffix (offset_minutes : I64) : String :=
    if offset_minutes == 0
    then "Z"
    else
        let sign := if offset_minutes < 0 then "-" else "+" in
        let magnitude := if offset_minutes < 0 then I64.neg offset_minutes else offset_minutes in
        let hours := i64_floor_div magnitude 60 in
        let minutes := i64_floor_mod magnitude 60 in
        String.concat_all [sign, pad2 hours, ":", pad2 minutes]

/// The UTC instant this local date/time denotes.
pub def DateTime.to_instant (dt : DateTime) : Instant :=
    match dt {
        mk date time offset_minutes =>
            let days := Date.to_epoch_day date in
            match time {
                mk hour minute second nanos =>
                    let secs_of_day := hour * 3600 + minute * 60 + second in
                    let local_secs := days * 86400 + secs_of_day in
                    let utc_secs := local_secs - offset_minutes * 60 in
                    Instant.normalize utc_secs nanos
            }
    }

/// Render an instant as a local date/time at `offset_minutes` east of UTC.
///
/// Instants that fall outside `[1, 9999]` after applying the offset produce a
/// year outside `Date`'s validated range; no validation is attempted here.
pub def DateTime.of_instant (i : Instant) (offset_minutes : I64) : DateTime :=
    match i {
        mk epoch_sec nanos =>
            let local_secs := epoch_sec + offset_minutes * 60 in
            let days := i64_floor_div local_secs 86400 in
            let rem := i64_floor_mod local_secs 86400 in
            let date := Date.of_epoch_day days in
            let hour := i64_floor_div rem 3600 in
            let rem2 := i64_floor_mod rem 3600 in
            let minute := i64_floor_div rem2 60 in
            let second := i64_floor_mod rem2 60 in
            let time : Time :=
                { hour := hour, minute := minute, second := second, nanos := nanos }
            in
            let dt : DateTime :=
                { date := date, time := time, offset_minutes := offset_minutes }
            in
            dt
    }

/// Equality means "the same instant", not "the same written fields".
pub instance BEq DateTime {
    def beq (a b : DateTime) : Bool :=
        DateTime.to_instant a == DateTime.to_instant b
}

/// Chronological order of the represented instants.
pub instance Ord DateTime {
    def compare (a b : DateTime) : Ordering :=
        Ord.compare (DateTime.to_instant a) (DateTime.to_instant b)
}

/// `YYYY-MM-DDTHH:MM:SS[.fraction]Z` or `...±HH:MM`.
pub def DateTime.to_iso (dt : DateTime) : String :=
    match dt {
        mk date time offset_minutes =>
            String.concat_all [
                Date.to_iso date,
                "T",
                Time.to_iso time,
                offset_suffix offset_minutes
            ]
    }

/// `YYYY-MM-DDTHH:MM:SS[.fraction]Z` or `...±HH:MM`.
pub instance Show DateTime {
    def show (dt : DateTime) : String := DateTime.to_iso dt
}
