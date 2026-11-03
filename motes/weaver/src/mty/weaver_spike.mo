// mty / tests / weaver_spike -- the Phase 0 terminal smoke against a real
// weaver binary: the initial alt-screen frame, a resize clear, and the
// double-Ctrl+C restore. Uses the Phase 1 event-driven waits (no fixed
// post-send sleeps). Compiled-backend only; skipped unless
// MTY_SELFTEST=1. `WV_BIN` selects the binary (default:
// target-monad/release/weaver).
use mty::spawn {SpawnConfig, Mty, Output}
use mty::check {Check.report, Check.skip, Check.enabled, Check.bin_path}
use std::io {IO.println}
use std::process {process_id, exec_cmd}

def base_env (root : String) : List (Pair String (Option String)) :=
    List.cons (Pair.pair "HOME" (Option.some root))
        (List.cons (Pair.pair "WEAVER_SESSION_ROOT" (Option.some (String.concat root "/sessions")))
            (List.cons (Pair.pair "WEAVER_PROC_ROOT" (Option.some (String.concat root "/procs")))
                List.empty))

def env_with_turns (root : String) (turns : Option String) : List (Pair String (Option String)) :=
    match turns {
        Option.some p => List.cons (Pair.pair "SHUTTLE_MOCK_TURNS" (Option.some p)) (base_env root),
        Option.none => base_env root
    }

def weaver_args : List String :=
    List.cons "--provider" (List.cons "mock" (List.cons "--model" (List.cons "mock" List.empty)))

def saw_alt_screen (o : Output) : Bool := String.contains o.raw "\u{1b}[?1049h"

def saw_resize_clear (o : Output) : Bool := I64.gt o.grid.clears 0

def saw_restore (o : Output) : Bool := String.contains o.raw "\u{1b}[?1049l"

def drive (m : Mty) (root : String) : IO Bool := do {
    let frame_ok <- Mty.wait_until m saw_alt_screen 6000;
    Mty.resize m 30 100;
    let resize_ok <- Mty.wait_until m saw_resize_clear 2000;
    Mty.send_text m "\u{3}";
    Mty.send_text m "\u{3}";
    let exit_ok <- Mty.wait_until m saw_restore 2000;
    Mty.finish m;
    let _ <- exec_cmd "rm" (List.cons "-rf" (List.cons root List.empty));
    let a <- Check.report "weaver initial alt-screen" frame_ok;
    let b <- Check.report "weaver resize clear" resize_ok;
    let c <- Check.report "weaver double ctrl-c restore" exit_ok;
    return (a && b && c)
}

def run_spike (bin : String) : IO Bool := do {
    let t <- IO.current_time_nano;
    let root := String.concat "/tmp/mty_weaver_"
        (String.concat (I64.to_string process_id) (String.concat "_" (I64.to_string t)));
    let _ <- exec_cmd "mkdir" (List.cons "-p" (List.cons root List.empty));
    let turns <- IO.get_env "WV_TURNS";
    let cfg : SpawnConfig := {
        bin := bin,
        args := weaver_args,
        rows := 24,
        cols := 80,
        env := env_with_turns root turns,
        cwd := Option.some root
    };
    let r <- Mty.spawn cfg;
    match r {
        Result.err e => do {
            let _ <- exec_cmd "rm" (List.cons "-rf" (List.cons root List.empty));
            IO.println (String.concat "FAIL mty weaver spawn: " e);
            return false
        },
        Result.ok m => drive m root
    }
}

pub def run_weaver_frame_resize_exit : IO Bool := do {
    let on <- Check.enabled "MTY_SELFTEST";
    if Bool.not on then do {
        Check.skip "mty weaver spike (set MTY_SELFTEST=1; compiled backend only)"
    } else do {
        let bin <- Check.bin_path "target-monad/release/weaver";
        run_spike bin
    }
}
