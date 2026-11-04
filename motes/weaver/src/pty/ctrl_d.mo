// weaver / pty / ctrl_d -- one Ctrl+D hints, a Ctrl+C/Ctrl+D cross-gesture
// does not exit, and two consecutive Ctrl+D presses restore the terminal.
// Ported from pty_repro_ctrl_d.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def spawn_slow (bin : String) (root : String) : IO (Result String Pty) := do {
    let turns <- fixture_path "turns_slow.json";
    spawn bin "mock" 20 80 root (Option.some turns) List.empty
}

def single_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    let o0 <- Pty.output m;
    let a <- Check.report "S1 no hint before any press" (Bool.not (tight_has o0 "pressCtrl+D"));
    Pty.send_text m "\u{4}";
    let hint <- Pty.wait_until m (fn (o : Output) => tight_has o "pressCtrl+Dagain") 2000;
    let b <- Check.report "S1 one Ctrl+D shows the hint" hint;
    let o1 <- Pty.output m;
    let c <- Check.report "S1 one Ctrl+D does not exit"
        (Bool.not (Output.contains o1 "\u{1b}[?1049l"));
    Pty.send_text m "\u{3}";
    Pty.pump m 800;
    Pty.send_text m "\u{4}";
    Pty.pump m 1000;
    let o2 <- Pty.output m;
    let d <- Check.report "S2 Ctrl+C then Ctrl+D does not exit"
        (Bool.not (Output.contains o2 "\u{1b}[?1049l"));
    Pty.finish m;
    return (up && a && b && c && d)
}

def single_and_cross (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_slow bin root;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty ctrl_d spawn: " e); return false },
        Result.ok m => single_go m
    }
}

def double_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "\u{4}";
    Pty.pump m 800;
    Pty.send_text m "\u{4}";
    let exit_ok <- Pty.wait_until m (fn (o : Output) => Output.contains o "\u{1b}[?1049l") 3000;
    let a <- Check.report "S3 double Ctrl+D exits" exit_ok;
    let _ <- Pty.wait_until m (fn (o : Output) => o.eof) 3000;
    let reaped <- Pty.reap m;
    let b <- Check.report "S4 the process is gone" (I64.gt reaped 0);
    Pty.finish m;
    return (up && a && b)
}

def double_exits (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_slow bin root;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty ctrl_d spawn: " e); return false },
        Result.ok m => double_go m
    }
}

pub def run_ctrl_d_single_and_cross_gesture : IO Bool :=
    run_gated "pty weaver ctrl_d" test_ctrl_d_single_body

def test_ctrl_d_single_body (bin : String) : IO Bool :=
    with_root "ctrl_d_single" (fn (root : String) => single_and_cross bin root)

pub def run_ctrl_d_double_exits : IO Bool :=
    run_gated "pty weaver ctrl_d" test_ctrl_d_double_body

def test_ctrl_d_double_body (bin : String) : IO Bool :=
    with_root "ctrl_d_double" (fn (root : String) => double_exits bin root)
