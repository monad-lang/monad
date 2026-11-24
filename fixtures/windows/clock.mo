#![mote { name := "clock", deps := [init, std] }]

// The time family, which is where the Windows runtime departs most from POSIX:
// mingw has neither `clock_gettime(CLOCK_MONOTONIC)` nor
// `timespec_get`/`TIME_UTC`, so `platform_win32.c` drives everything from
// `QueryPerformanceCounter` (100 ns ticks) and `GetSystemTimeAsFileTime`
// (the wall clock, rebased from 1601 onto 1970).
//
// Asserted as PROPERTIES, not values: a monotonic reading must advance across
// a real sleep, and a wall-clock timestamp must land after 2020. Printing
// either reading would make this test unrunnable twice.
open IO {println}

#[native sleep_io]
priv def sleep_io_raw (ms : I64) : RawIO Unit

def sleep_ms (ms : I64) : IO Unit := IO.mk (sleep_io_raw ms)

// 2020-01-01T00:00:00Z in nanoseconds.
def after_twenty_twenty : I64 := 1577836800000000000

def flag (b : Bool) : String := if b then "true" else "false"

def main (args : List String) : IO Unit := do {
    let before <- IO.current_time_nano;
    sleep_ms 20;
    let after <- IO.current_time_nano;
    let wall <- IO.epoch_time_nano;
    println (flag (I64.gt after before) ++ " " ++ flag (I64.gt wall after_twenty_twenty))
}
