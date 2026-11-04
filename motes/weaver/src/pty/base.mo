// weaver / pty / base -- the first frame renders without a key, `go` opens the
// approval overlay, `y` runs the read and completes the turn, the completion
// repaints, and the double Ctrl+C gesture hints then restores the screen.
// Ported from the retired scripts/weaver-tui-repro/pty_repro.py; the scripted
// turns are generated with a real note path (the Python fixture pointed at a
// never-created /tmp path and its final checks were stale).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args}
use weaver::pty_fixtures {write_base_script}
use std::io {IO.println}
use std::path {Path}
use std::test {Test.write_fixture}

/// Wait for the rendered first frame, not just the alt-screen switch: the
/// switch is emitted before the frame, so a snapshot on `?1049h` alone can
/// race the status/placeholder paint.
def first_frame (o : Output) : Bool :=
    Bool.and (has_tight o "manual")
        (Bool.and (has_tight o "typeamessage") (Output.contains o "\u{1b}[?1049h"))

def has_tight (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def has_stripped (o : Output) (needle : String) : Bool :=
    String.contains (Output.stripped o) needle

def done_turn (o : Output) : Bool :=
    has_tight o "donereading"

def base_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m first_frame 6000;
    let o0 <- Pty.output m;
    let a <- Check.report "initial frame renders without a key" (first_frame o0);
    Pty.send_text m "x";
    Pty.send_text m "go\n";
    let overlay <- Pty.wait_until m (fn (o : Output) => has_stripped o "Permission required") 6000;
    let b <- Check.report "approval overlay comes up after go" overlay;
    let o1 <- Pty.output m;
    let mark := String.length o1.raw;
    Pty.send_text m "y";
    let finished <- Pty.wait_until m done_turn 12000;
    let c <- Check.report "answer accepted and the turn completes" finished;
    let repainted <- Pty.wait_until m (fn (o : Output) => String.contains (Output.since o mark) "\u{1b}[2J") 15000;
    let d <- Check.report "turn over before the exit gesture" repainted;
    Pty.send_text m "\u{3}";
    let hinted <- Pty.wait_until m (fn (o : Output) => has_tight o "pressCtrl+Cagain") 3000;
    let e <- Check.report "first Ctrl+C shows the exit hint" hinted;
    Pty.send_text m "\u{3}";
    let restored <- Pty.wait_until m (fn (o : Output) => Output.contains o "\u{1b}[?1049l") 3000;
    let f <- Check.report "second Ctrl+C restores the screen" restored;
    Pty.finish m;
    return (up && a && b && c && d && e && f)
}

def base_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_base.json";
    let note := String.concat root "/note.txt";
    let _ <- Test.write_fixture (Path.path note) "hi";
    let wrote <- write_base_script turns note;
    if Bool.not wrote then do {
        IO.println "FAIL pty base: could not write the turn script";
        return false
    } else do {
        let no_color : List (Pair String (Option String)) :=
            List.cons (Pair.pair "NO_COLOR" (Option.some "1")) List.empty;
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) no_color;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty base spawn: " e); return false },
            Result.ok m => base_go m
        }
    }
}

pub def run_base_initial_frame_overlay_exit : IO Bool :=
    run_gated "pty weaver base" test_base_body

def test_base_body (bin : String) : IO Bool :=
    with_root "base" (fn (root : String) => base_run bin root)
