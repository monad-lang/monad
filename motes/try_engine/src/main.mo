// The /try engine's wasm ABI.
//
// `try_run(sources, source)` is the one export the worker calls. Both
// parameters are Monad `String`s, which cross the export boundary as i64
// words holding the UTF-8 pointer (proved in `fixtures/wasm/try_abi.mo`);
// `sources` carries the served prelude `.mo` files the page fetched, framed
// as `lib::sources` describes. The result is PUSHED through `web_wasm`'s
// `TryBridge.push_result` because an `IO`-typed export cannot return a
// value.

use lib::pipeline {Outcome, run_source}
use lib::sources {SourceModule, parse_sources}
use web_wasm::try_bridge {TryBridge.push_result}

#[export "c"]
def try_run (sources : String) (source : String) : IO Unit :=
    match parse_sources sources {
        Result.err e => push_unreadable e,
        Result.ok modules => run_with modules source,
    }

/// The payload itself did not parse -- a load failure with the detail,
/// never a silently empty prelude.
def push_unreadable (detail : String) : IO Unit :=
    TryBridge.push_result 2 "" ""
        (String.concat "the prelude sources the page supplied could not be read: " detail) ""

def run_with (modules : List SourceModule) (source : String) : IO Unit := do {
    let o <- run_source modules source;
    match o {
        Outcome.mk { status, value, typ, error, notes } =>
            TryBridge.push_result status value typ error notes,
    }
}

def main : IO Unit := IO.pure unit
