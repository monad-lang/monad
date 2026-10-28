/// Calendar math (proleptic Gregorian) and `Date` construction/formatting.
///
/// The day-count algorithm is Howard Hinnant's public-domain
/// "chrono-Compatible Low-Level Date Algorithms" (the one C++20's
/// `year_month_day` uses). `Date.of` restricts years to `[1, 9999]`, which
/// keeps every intermediate in `to_epoch_day` non-negative, so that half can
/// use ordinary truncating division. `of_epoch_day` is also reachable from an
/// arbitrary `Instant`, so it uses floor division for the era split.

use lib::types {Date, TimeError, TimeErrorKind}
use lib::internal {i64_floor_div, i64_mod_pos, pad2, pad4}
use lib::error {TimeError.of}
use std::show {Show}

/// Whether `year` is a leap year in the proleptic Gregorian calendar.
pub def Date.is_leap_year (year : I64) : Bool :=
    Bool.and (i64_mod_pos year 4 == 0)
        (Bool.or (Bool.not (i64_mod_pos year 100 == 0)) (i64_mod_pos year 400 == 0))

/// The number of days in `month` of `year` (28-31).
pub def Date.days_in_month (year : I64) (month : I64) : I64 :=
    if month == 2 then (if Date.is_leap_year year then 29 else 28)
    else if month == 4 then 30
    else if month == 6 then 30
    else if month == 9 then 30
    else if month == 11 then 30
    else 31

/// Days since 1970-01-01 (negative for earlier dates).
///
/// Every division is plain `I64.div`: for `year` in `[1, 9999]` all the
/// operands (`y`, `era`, `yoe`, `mm`, `doy`, `doe`) are non-negative.
def Date.to_epoch_day (d : Date) : I64 :=
    match d {
        mk year month day =>
            let y := if month <= 2 then year - 1 else year in
            let era := y / 400 in
            let yoe := y - era * 400 in
            let mm := if month > 2 then month - 3 else month + 9 in
            let doy := (153 * mm + 2) / 5 + (day - 1) in
            let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy in
            era * 146097 + doe - 719468
    }

/// The inverse of `Date.to_epoch_day` (Hinnant's `civil_from_days`).
///
/// Package-private: callers get a `Date` through `Date.of` validation or
/// `DateTime.of_instant`. For days far outside `[1, 9999]` the returned year
/// simply falls outside that range, as an unchecked inverse must.
def Date.of_epoch_day (days : I64) : Date :=
    let z := days + 719468 in
    let era := i64_floor_div z 146097 in
    let doe := z - era * 146097 in
    let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
    let y := yoe + era * 400 in
    let doy := doe - (365 * yoe + yoe / 4 - yoe / 100) in
    let mp := (5 * doy + 2) / 153 in
    let day := doy - (153 * mp + 2) / 5 + 1 in
    let month := if mp < 10 then mp + 3 else mp - 9 in
    let result : Date :=
        { year := (if month <= 2 then y + 1 else y), month := month, day := day }
    in
    result

/// Validate and build a calendar date.
///
/// Rejects years outside `[1, 9999]`, months outside `[1, 12]`, and days
/// outside the month's real length (so `2023-02-29` and `2024-02-30` fail).
pub def Date.of (year : I64) (month : I64) (day : I64) : Result TimeError Date :=
    if year < 1 || year > 9999
    then err (TimeError.of TimeErrorKind.year_out_of_range "year must be in [1, 9999]")
    else if month < 1 || month > 12
    then err (TimeError.of TimeErrorKind.month_out_of_range "month must be in [1, 12]")
    else
        let dim := Date.days_in_month year month in
        if day < 1 || day > dim
        then err (TimeError.of TimeErrorKind.day_out_of_range "day out of range for year/month")
        else ok ({ year := year, month := month, day := day } : Date)

/// The ISO-8601 calendar-date rendering, `YYYY-MM-DD`.
pub def Date.to_iso (d : Date) : String :=
    match d {
        mk year month day =>
            String.concat_all [pad4 year, "-", pad2 month, "-", pad2 day]
    }

/// `YYYY-MM-DD`.
pub instance Show Date {
    def show (d : Date) : String := Date.to_iso d
}
