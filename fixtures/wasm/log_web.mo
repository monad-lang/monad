// The `log` mote on the web profile: regression for the recorded
// `log-mote-not-web-safe` gap.
//
// `Logger.format_json_line` reaches `Json.to_string`, whose float arm once
// pulled in the web-gated `f64_to_string`. Since the 2026-10-24 web float
// fix the whole path builds, and this fixture pins that: `scripts/
// check-wasm-target.sh` builds it for wasm32-unknown-unknown, the sink
// checks the line's shape, and stdout must be exactly "ok".
//
// The sink does the checking itself (rather than capturing into a `Ref`)
// so the fixture needs no shared mutable state and stays affine-clean.

#![mote { name := "log_web", deps := [log] }]

use std::io {IO.write_stdout}
use log::level {LogLevel}
use log::logger {Logger, Logger.info, Logger.with_format, Logger.with_sink, LogFormat}

def check_line (line : String) : IO Unit :=
    IO.write_stdout
        (if String.starts_with "{\"fields\":" line && String.contains line "\"msg\":\"hello\""
        then "ok\n"
        else "bad\n")

def main : IO Unit := do {
    let logger : Logger :=
        Logger.with_format (Logger.with_sink LogLevel.info check_line) LogFormat.json_lines;
    Logger.info logger "hello"
}
