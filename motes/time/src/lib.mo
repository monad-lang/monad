/// The `time` mote's public surface: the value types, the constructors, the
/// named arithmetic, and the ISO-8601 entry points.
///
/// Deliberately thin — a second, hand-maintained index of every def would go
/// stale (the doctrine `motes/json/src/lib.mo` states). Instances (`Show`,
/// `Ord`, `Sub Duration`, `BEq DateTime`) are global and need no re-export.
///
/// Consumers import individual names from the OWNING module
/// (`time::date {Date.of}`, `time::iso8601 {Date.parse_iso}`): a hub's
/// re-exports are not declarations, so a brace item cannot name them. This
/// file is what a bare `use time` resolves to.

pub use lib::types {Date, Time, Instant, Duration, DateTime, TimeError, TimeErrorKind}
pub use lib::date {Date.of, Date.is_leap_year, Date.days_in_month, Date.to_iso}
pub use lib::time_of_day {Time.of, Time.to_iso}
pub use lib::duration {
    Duration.zero,
    Duration.of_seconds,
    Duration.of_nanos,
    Duration.add,
    Duration.sub,
    Duration.scale,
    Duration.div_by,
    Duration.format
}
pub use lib::instant {Instant.now, Instant.add_duration, Instant.sub_duration, Instant.diff}
pub use lib::datetime {DateTime.of_instant, DateTime.to_instant, DateTime.to_iso}
pub use lib::iso8601 {Date.parse_iso, DateTime.parse}
pub use lib::error {TimeError.of, TimeError.kind, TimeError.message}
