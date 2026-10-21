/// Small display formatters for the live thinking line: token counts and
/// frame-clock elapsed time. Pure, so the boundaries are pinned in
/// `format_tests.mo`.

/// One decimal of `n * 10 / unit`, without a trailing `.0`.
def one_decimal (n : I64) (unit : I64) : String :=
    let whole : I64 := n / unit in
    let tenth : I64 := ((n - (whole * unit)) * 10) / unit in
    if tenth == 0
    then I64.to_string whole
    else String.concat (I64.to_string whole) (String.concat "." (I64.to_string tenth))

/// `1234` -> `1.2k`, `1234567` -> `1.2M`, under 1000 raw. Negative counts
/// clamp to 0 (usage is never negative, but a malformed file can be).
pub def format_tokens (n : I64) : String :=
    let v : I64 := if n < 0 then 0 else n in
    if v < 1000
    then I64.to_string v
    else if v < 1000000
    then String.concat (one_decimal v 1000) "k"
    else String.concat (one_decimal v 1000000) "M"

/// Two digits, zero-padded (`4` -> `04`).
def two_digits (n : I64) : String :=
    if n < 10
    then String.concat "0" (I64.to_string n)
    else I64.to_string n

/// Elapsed time from the 100 ms frame clock. Under 10 s: one decimal
/// (`3.4s`); under a minute: whole seconds (`12s`); then `1m 04s`.
/// Negative frames clamp to 0.
pub def format_elapsed (frames : I64) : String :=
    let f : I64 := if frames < 0 then 0 else frames in
    let secs : I64 := f / 10 in
    if secs < 10
    then
        let tenth : I64 := f - (secs * 10) in
        if tenth == 0
        then String.concat (I64.to_string secs) "s"
        else String.concat (String.concat (I64.to_string secs) ".") (String.concat (I64.to_string tenth) "s")
    else if secs < 60
    then String.concat (I64.to_string secs) "s"
    else
        let mins : I64 := secs / 60 in
        let rest : I64 := secs - (mins * 60) in
        String.concat (I64.to_string mins) (String.concat "m " (String.concat (two_digits rest) "s"))
