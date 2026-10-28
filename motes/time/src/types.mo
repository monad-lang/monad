/// The `time` mote's value types.
///
/// This file is declarations only. A file carrying `#[derive ...]` attributes
/// must contain no function bodies (the constraint recorded in
/// `motes/tui/src/types.mo`), so constructors, arithmetic and formatting live
/// in `date.mo`/`duration.mo`/`time_of_day.mo`/`instant.mo`/`datetime.mo`.
///
/// The derive macros are referenced only by their names in the attributes
/// below; the compiler's unused-import analysis cannot see that dispatch, so
/// they read as unused. Removing the `use` makes every derive fail with
/// "macro `derive_beq` not found".
use std::derive {derive_beq, derive_bord}

/// A point in time, as signed seconds since 1970-01-01T00:00:00Z plus a
/// sub-second remainder.
///
/// `nanos` is ALWAYS normalized to `[0, 999999999]`, which is what makes the
/// derived lexicographic `(epoch_sec, nanos)` comparison chronological.
/// Splitting the representation keeps the usable range at the full `I64`
/// second range (~±292 billion years) instead of overflowing at year 2262
/// as a single nanosecond count would.
#[derive BEq BOrd]
pub struct Instant {
    epoch_sec : I64,
    nanos : I64,
}

/// A span of time, in the same two-field shape as `Instant`.
///
/// The sign lives entirely in `secs`; `nanos` is always normalized to
/// `[0, 999999999]` even for a negative span, so `-1.5s` is
/// `{ secs := -2, nanos := 500000000 }` and the derived lexicographic order
/// is "shorter span first".
#[derive BEq BOrd]
pub struct Duration {
    secs : I64,
    nanos : I64,
}

/// A proleptic-Gregorian calendar date.
///
/// `Date.of` validates every field; the ranges below are its contract.
/// Restricting `year` to `[1, 9999]` also keeps every intermediate in the
/// day-count algorithm non-negative, which is why that algorithm can use
/// ordinary truncating division.
#[derive BEq BOrd]
pub struct Date {
    year : I64,
    month : I64,
    day : I64,
}

/// A time of day, independent of any date and offset.
///
/// No leap seconds: `second` is `[0, 59]`, so `23:59:60` is rejected.
#[derive BEq BOrd]
pub struct Time {
    hour : I64,
    minute : I64,
    second : I64,
    nanos : I64,
}

/// A local calendar date and time with a fixed UTC offset.
///
/// There is no derive here: equality and ordering must mean "the same
/// instant", so two representations of one moment under different offsets
/// (`10:00+01:00` and `09:00+00:00`) compare equal. `BEq`/`Ord` are
/// hand-written over `DateTime.to_instant` in `datetime.mo`.
pub struct DateTime {
    date : Date,
    time : Time,
    offset_minutes : I64,
}

/// Why a calendar/ISO-8601 operation was rejected.
#[derive BEq]
pub type TimeErrorKind {
    invalid_format,
    year_out_of_range,
    month_out_of_range,
    day_out_of_range,
    hour_out_of_range,
    minute_out_of_range,
    second_out_of_range,
    nanos_out_of_range,
    invalid_offset,
    other,
}

/// A rejected time operation: a machine-branchable kind plus a message.
pub struct TimeError {
    kind : TimeErrorKind,
    message : String,
}

/// The minimal seam a future timezone-database mote would implement.
///
/// Declared now, unused by this mote's fixed-offset `DateTime` (Phase 7 of
/// `plans/library-ideas/time.md`). "Given a zone and an instant, what is the
/// UTC offset in minutes" is the one operation every zone representation can
/// answer.
pub class TimeZone Z {
    def offset_minutes_at : Z -> Instant -> I64
}
