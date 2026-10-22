/// Monotonic-enough wall clock in milliseconds. The browser implementation
/// is `Date.now()`, so it is wall-clock, not monotonic; use it for debounce
/// and display, not for measuring intervals.

use lib::ffi {now_ms_raw}

pub def Clock.now_ms : IO I64 := IO.mk now_ms_raw
