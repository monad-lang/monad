// pty / tests / spawn_spike -- the Phase 0 FFI smoke.
//
// Compiled-backend only (the Rust host ignores `#[extern "c"]`), so the test
// skips green unless PTY_SELFTEST=1. It proves the pieces the harness rests
// on: `forkpty` allocates a pty and forks, `execl8` execs `/bin/sh`, the
// master fd is adopted as an `FdStream`, output is read, and the child is
// reaped.
use lib::spawn {SpawnConfig, Pty}
use std::io {IO.println}

def gate : IO Bool := do {
    let on <- IO.get_env "PTY_SELFTEST";
    return (match on { Option.some _ => true, Option.none => false })
}

def run_smoke (m : Pty) : IO Bool := do {
    let out <- Pty.read_all m 3000;
    Pty.finish m;
    let ok := String.contains out "hi";
    IO.println (if ok then "PASS pty forkpty shell roundtrip" else "FAIL pty forkpty shell roundtrip");
    return ok
}

#[test]
def test_forkpty_shell_roundtrip : IO Bool := do {
    let on <- gate;
    if Bool.not on then do {
        IO.println "SKIP pty forkpty smoke (set PTY_SELFTEST=1; compiled backend only)";
        return true
    } else do {
        let cfg : SpawnConfig := {
            bin := "/bin/sh",
            args := List.cons "-c" (List.cons "printf hi" List.empty),
            rows := 24,
            cols := 80,
            env := List.empty,
            cwd := Option.none
        };
        let r <- Pty.spawn cfg;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty forkpty smoke: " e); return false },
            Result.ok m => run_smoke m
        }
    }
}
