// weaver / pty / round2 -- rounded borders and the dim statusbar, eight mock
// turns, PageUp/PageDown and the SGR wheel indicator, Alt+Enter multiline
// submit, and history recall. Ported from
// pty_repro_round2.py (retired); the Python's history check
// was hard-coded True and its scroll checks scanned the accumulated stream,
// so both are real assertions here.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {
    run_gated, with_root, fixture_path, spawn, sgr, status_turns, input_row,
    any_row, quit_cleanly
}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

/// Wait for the rendered frame (the placeholder), not just the alt-screen
/// switch, before snapshotting the border/status colours.
def first_frame (o : Output) : Bool :=
    Bool.and (saw_alt o) (tight_has o "typeamessage")

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def input_shown (o : Output) : Bool :=
    match input_row o {
        Option.some _ => true,
        Option.none => false
    }

def row_has (o : Output) (r : I64) (needle : String) : Bool :=
    String.contains (Output.row_text o r) needle

def reply_seen (o : Output) (i : I64) : Bool :=
    Bool.and (tight_has o (String.concat "reply" (String.concat (I64.to_string i) ":")))
        (status_turns o (i + 1))

def indicator_seen (o : Output) : Bool :=
    Bool.and (tight_has o "above") (tight_has o "PgDn")

#[partial]
def eight_turns (m : Pty) (i : I64) (acc : Bool) : IO Bool := do {
    if Bool.not (I64.lt i 8) then IO.pure acc
    else do {
        Pty.send_text m "go\n";
        let seen <- Pty.wait_until m (fn (o : Output) => reply_seen o i) 8000;
        let label := String.concat "turn " (String.concat (I64.to_string i) " completes");
        let acc2 <- Check.report label seen;
        eight_turns m (i + 1) (Bool.and acc acc2)
    }
}

def round2_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m first_frame 6000;
    let o0 <- Pty.output m;
    let a <- Check.report "rounded border glyphs" (Output.contains o0 "╭");
    let b <- Check.report "dim statusbar" (Output.contains o0 "\u{1b}[2m");
    let turns <- eight_turns m 0 true;
    Pty.send_text m "\u{1b}[5~";
    let paged <- Pty.wait_until m indicator_seen 3000;
    let c <- Check.report "PageUp scrolls and shows the indicator" paged;
    Pty.send_text m "\u{1b}[6~";
    let bottom <- Pty.wait_until m (fn (o : Output) => Bool.not (grid_has o "above")) 3000;
    let d <- Check.report "PageDown returns to the bottom" bottom;
    Pty.send_text m (sgr 64 9 9 "M");
    let wheel <- Pty.wait_until m (fn (o : Output) => grid_has o "PgDn") 3000;
    let e <- Check.report "an SGR wheel report scrolls" wheel;
    Pty.send_text m "one";
    let typed <- Pty.wait_until m (fn (o : Output) => grid_has o "one") 3000;
    let f <- Check.report "the first multiline word is in the input" typed;
    Pty.send_text m "\u{1b}\r";
    Pty.pump m 200;
    Pty.send_text m "two\n";
    // The script is exhausted; the retry policy backs off 2 s + 4 s before the
    // turn errors. Wait for the input box to come back (empty again).
    let done <- Pty.wait_until m input_shown 15000;
    let o1 <- Pty.output m;
    let g <- Check.report "the multiline submit echoes both lines"
        (Bool.and done (Bool.and (any_row o1.grid "one" 1 16) (any_row o1.grid "two" 1 16)));
    Pty.send_text m "\u{1b}[A";
    let recalled <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (row_has o 17 "one") (row_has o 18 "two")) 3000;
    let h <- Check.report "ArrowUp recalls the multiline entry" recalled;
    Pty.send_text m "\u{1b}[B";
    let cleared <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (input_shown o) (Bool.not (row_has o 17 "one"))) 3000;
    let i <- Check.report "ArrowDown returns to the live input" cleared;
    let restored <- quit_cleanly m 4000;
    let j <- Check.report "double Ctrl+C restores the screen" restored;
    Pty.finish m;
    return (Bool.and up (Bool.and a (Bool.and b (Bool.and turns (Bool.and c (Bool.and d (Bool.and e (Bool.and f (Bool.and g (Bool.and h (Bool.and i j)))))))))))
}

def round2_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_long.json";
    let r <- spawn bin "mock" 20 80 root (Option.some turns) List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty round2 spawn: " e); return false },
        Result.ok m => round2_go m
    }
}

pub def run_round2_scroll_multiline_history : IO Bool :=
    run_gated "pty weaver round2" test_round2_body

def test_round2_body (bin : String) : IO Bool :=
    with_root "round2" (fn (root : String) => round2_run bin root)
