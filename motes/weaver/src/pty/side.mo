// weaver / pty / side -- side commands and /btw run beside a turn: /help
// opens its dialog while the spinner is live, /btw's answer opens in a
// dialog while the turn keeps going, the turn's reply still lands, and keys
// reach the prompt after the dialogs and the /tasks monitor close.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn, quit_cleanly}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def thinking_visible (o : Output) : Bool := tight_has o "thinking"

// The mock answers each call after 4 s: long enough for both side dialogs
// to open and close while the turn is still running.
def delay_env : List (Pair String (Option String)) :=
    [Pair.pair "SHUTTLE_MOCK_DELAY_MS" (Option.some "4000")]

def side_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "fix the build\n";
    let busy <- Pty.wait_until m thinking_visible 5000;
    Pty.send_text m "/help\r";
    let help <- Pty.wait_until m (fn (o : Output) => grid_has o "/mode [manual") 4000;
    let a <- Check.report "/help opens a dialog while the turn runs" (busy && help);
    Pty.send_text m "\u{1b}";
    let _ <- Pty.wait_until m (fn (o : Output) => Bool.not (grid_has o "/mode [manual")) 3000;
    // The mock picks its entry by the history's assistant count, and the
    // side question carries none: its answer is the script's first entry.
    // The dialog is told apart by its subtitle, the question.
    Pty.send_text m "/btw what is it doing\r";
    let btw <- Pty.wait_until m (fn (o : Output) => Bool.and (grid_has o "what is it doing") (grid_has o "reply side")) 9000;
    let b <- Check.report "/btw's answer opens in a dialog" btw;
    Pty.send_text m "\u{1b}";
    // On the grid, not the stream: the btw dialog already painted the text,
    // and in the transcript the btw answer is a hidden detail block.
    let reply <- Pty.wait_until m (fn (o : Output) => Bool.and (grid_has o "reply side: the turn") (Bool.not (grid_has o "Enter/Esc close"))) 10000;
    let c <- Check.report "the turn's reply still lands" reply;
    Pty.send_text m "zz-typed";
    let typed <- Pty.wait_until m (fn (o : Output) => grid_has o "zz-typed") 3000;
    let d <- Check.report "keys reach the prompt after the dialogs" typed;
    // The log review's F8: keys were lost after the /tasks monitor closed.
    // Clear "zz-typed" from the box first (8 backspaces).
    Pty.send_text m (String.repeat "\u{7f}" 8);
    Pty.send_text m "/tasks\r";
    let _ <- Pty.wait_until m (fn (o : Output) => grid_has o "Esc") 3000;
    Pty.send_text m "\u{1b}";
    Pty.pump m 500;
    Pty.send_text m "after-monitor";
    let typed2 <- Pty.wait_until m (fn (o : Output) => grid_has o "after-monitor") 3000;
    let f <- Check.report "keys reach the prompt after the /tasks monitor" typed2;
    let restored <- quit_cleanly m 3000;
    let e <- Check.report "clean exit after the side dialogs" restored;
    Pty.finish m;
    return (up && a && b && c && d && f && e)
}

def side_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_side.json";
    let r <- spawn bin "mock" 24 100 root (Option.some turns) delay_env;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty side spawn: " e); return false },
        Result.ok m => side_go m
    }
}

pub def run_side_commands_beside_a_turn : IO Bool :=
    run_gated "pty weaver side" test_side_body

def test_side_body (bin : String) : IO Bool :=
    with_root "side" (fn (root : String) => side_run bin root)
