// weaver / pty / instructions -- a trusted project's AGENTS.md is named in
// the startup note, and an edit to it between two turns reaches the model
// as a change note on the second turn's message (read back from the
// session's saved history: the mock provider records no requests);
// `/memory` then lists the file at its new size.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn_args, status_turns, quit_cleanly}
use std::test {Test.write_fixture}
use std::process {exec_cmd}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def agents_at (root : String) : Path :=
    Path.path (String.concat root "/AGENTS.md")

/// The note is in a history block on disk: grep's status says.
def history_has (root : String) (needle : String) : IO Bool := do {
    let rc <- exec_cmd "sh" ["-c", String.concat_list ["grep -rqF '", needle, "' ", root, "/sessions/*/history"]];
    IO.pure (rc == 0)
}

def instr_go (m : Pty) (root : String) : IO Bool := do {
    let up <- Pty.wait_until m (fn (o : Output) => tight_has o "typeamessage" && tight_has o "instructions:") 6000;
    let a <- Check.report "the startup note names the loaded AGENTS.md" up;
    Pty.send_text m "first\n";
    let one <- Pty.wait_until m (fn (o : Output) => status_turns o 1) 8000;
    let _ <- Test.write_fixture (agents_at root) "Keep tests green.\nAlways answer in haiku.\n";
    Pty.send_text m "second\n";
    let two <- Pty.wait_until m (fn (o : Output) => status_turns o 2) 8000;
    let b <- Check.report "both turns complete" (one && two);
    Pty.send_text m "/memory\n";
    let listed <- Pty.wait_until m (fn (o : Output) => tight_has o "AGENTS.md(repo,42B)") 4000;
    let e <- Check.report "/memory lists the file at its new size" listed;
    // `/memory` is a side command: its dialog takes the first Ctrl+C. A
    // lone Esc closes it only after the dialog's next quiet poll (100 ms),
    // so give it that before quitting.
    Pty.send_text m "\u{1b}";
    Pty.pump m 500;
    // On the grid, not the stream (the placeholder was painted at startup):
    // wait for the dialog's footer to go, so the Ctrl+Cs reach the loop.
    let _ <- Pty.wait_until m (fn (o : Output) => match Output.find o "Enter/Esc close" { Option.some _ => false, Option.none => true }) 3000;
    let quit <- quit_cleanly m 4000;
    Pty.finish m;
    let noted <- history_has root "changed during the session";
    let c <- Check.report "the second turn carries the change note" noted;
    let diffed <- history_has root "+ Always answer in haiku.";
    let d <- Check.report "the note shows the added line" diffed;
    IO.pure (a && b && e && quit && c && d)
}

def instr_run (bin : String) (root : String) : IO Bool := do {
    let _ <- Test.write_fixture (agents_at root) "Keep tests green.\n";
    let turns <- fixture_path "turns_long.json";
    let r <- spawn_args bin "mock" List.empty 24 100 root (Option.some turns) [Pair.pair "PWD" (Option.some root)];
    match r {
        Result.err e => Check.report (String.concat "spawn: " e) false,
        Result.ok m => instr_go m root,
    }
}

pub def run_instructions_note_a_mid_session_edit : IO Bool :=
    run_gated "pty weaver instructions" (fn (bin : String) => with_root "instructions" (fn (root : String) => instr_run bin root))
