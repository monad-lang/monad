/// Clocks. `now_ms` is the page's wall clock (`Date.now()`): fine for
/// seeding and display, not for measuring intervals. `monotonic_ms` is
/// `performance.now()`, which does measure intervals.

use lib::ffi {now_ms_raw, monotonic_ms_raw}

pub def Clock.now_ms : IO I64 := IO.mk now_ms_raw

pub def Clock.monotonic_ms : IO I64 := IO.mk monotonic_ms_raw
