// pty / check -- PASS/FAIL lines, skip-green gating, and WV_BIN resolution.
//
// The test's Bool is the verdict (`monad test` reports it); these lines keep
// the Python drivers' diagnostic text in the log. A gated test returns true
// when its switch is unset, and false only when the switch is on and a
// prerequisite (the binary, an executable bit) is missing.

use std::io {IO.println}

pub def Check.report (name : String) (ok : Bool) : IO Bool := do {
    IO.println (String.concat (if ok then "PASS " else "FAIL ") name);
    return ok
}

pub def Check.skip (what : String) : IO Bool := do {
    IO.println (String.concat "SKIP " what);
    return true
}

/// The env var is PRESENT, whatever its value (`WEAVER_PTY=1` in CI,
/// `PTY_SELFTEST=1` for the FFI smokes).
pub def Check.enabled (name : String) : IO Bool := do {
    let v <- IO.get_env name;
    return (match v {
        Option.some _ => true,
        Option.none => false
    })
}

/// The env var is present and non-empty (`WEAVER_PTY_REQUIRED=1`).
pub def Check.value_set (name : String) : IO Bool := do {
    let v <- IO.get_env name;
    return (match v {
        Option.some s => Bool.not (String.is_empty s),
        Option.none => false
    })
}

/// `WV_BIN` when set, else `fallback`.
pub def Check.bin_path (fallback : String) : IO String := do {
    let v <- IO.get_env "WV_BIN";
    return (match v {
        Option.some b => b,
        Option.none => fallback
    })
}
