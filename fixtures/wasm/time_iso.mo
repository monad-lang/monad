// The `time` mote under the web profile: ISO-8601 parse/show round-trip plus
// a sanity read of the browser clock.
//
// `scripts/check-wasm-target.sh` builds this for wasm32-unknown-unknown,
// instantiates it through wasm/web/smoke.mjs, and also diffs the native and
// wasi builds against the same expected line. The fixture is affine-clean
// (inline motes default to `affine = error`) and prints exactly one line:
//
//   2024-01-15T10:30:00.123+02:00 true true
//
// The final field is only "is the clock non-negative": the web profile's
// clock is epoch-based while native/wasi compiled binaries use a monotonic
// origin, so the absolute value must never be printed.

#![mote { name := "time_iso", deps := [time] }]

use std::io {IO.println}
use time::types {DateTime, Instant, TimeError}
use time::iso8601 {DateTime.parse}
use time::datetime {DateTime.to_iso}
use time::instant {Instant.now}

def bool_text (b : Bool) : String :=
    if b then "true" else "false"

def describe (r : Result TimeError DateTime) (clock_ok : Bool) : String :=
    match r {
        ok dt =>
            let shown := DateTime.to_iso dt in
            let roundtrip :=
                match DateTime.parse shown {
                    ok again => DateTime.to_iso again == shown,
                    err _ => false
                }
            in
            String.concat_all [shown, " ", bool_text roundtrip, " ", bool_text clock_ok],
        err _ => "parse-failed"
    }

def clock_is_non_negative (i : Instant) : Bool :=
    match i {
        mk secs nanos =>
            if secs > 0 then true
            else if secs == 0 then nanos >= 0
            else false
    }

def run : IO I64 := do {
    let parsed := DateTime.parse "2024-01-15T10:30:00.123+02:00";
    let now <- Instant.now;
    let _ <- IO.println (describe parsed (clock_is_non_negative now));
    return 0
}

def main (args : List String) : IO I64 := run
