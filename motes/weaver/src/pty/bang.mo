// weaver / pty / bang -- `! cmd` runs the user's shell line at once, its
// output lands in the transcript, and the next model line carries it as a
// note (read back from the saved history: the mock provider records no
// requests).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn_args, status_turns, quit_cleanly}
use std::process {exec_cmd}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def history_has (root : String) (needle : String) : IO Bool := do {
    let rc <- exec_cmd "sh" ["-c", String.concat_list ["grep -rqF '", needle, "' ", root, "/sessions/*/history"]];
    IO.pure (rc == 0)
}

// The output `bang-ok` never appears in the echoed command line itself.
def bang_go (m : Pty) (root : String) : IO Bool := do {
    let up <- Pty.wait_until m (fn (o : Output) => tight_has o "typeamessage") 6000;
    let a <- Check.report "the prompt is up" up;
    Pty.send_text m "! printf 'bang%s' -ok\n";
    let shown <- Pty.wait_until m (fn (o : Output) => tight_has o "bang-ok") 6000;
    let b <- Check.report "the command's output is in the transcript" shown;
    Pty.send_text m "hello\n";
    let one <- Pty.wait_until m (fn (o : Output) => status_turns o 1) 8000;
    let c <- Check.report "the next turn completes" one;
    let quit <- quit_cleanly m 4000;
    Pty.finish m;
    let noted <- history_has root "the user ran a shell command";
    let carried <- history_has root "bang-ok";
    let d <- Check.report "the turn's message carries the note and the output" (noted && carried);
    IO.pure (a && b && c && quit && d)
}

def bang_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_long.json";
    let r <- spawn_args bin "mock" List.empty 24 100 root (Option.some turns) [Pair.pair "PWD" (Option.some root)];
    match r {
        Result.err e => Check.report (String.concat "spawn: " e) false,
        Result.ok m => bang_go m root,
    }
}

pub def run_bang_runs_and_rides_the_next_turn : IO Bool :=
    run_gated "pty weaver bang" (fn (bin : String) => with_root "bang" (fn (root : String) => bang_run bin root))
