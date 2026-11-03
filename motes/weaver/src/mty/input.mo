// weaver / mty / input -- the caret is visible on the first frame, typing
// lands on the input row, a click moves the caret, a drag copies via OSC 52,
// and the caret returns after a submit. Ported from
// pty_repro_input.py (retired).
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {run_gated, with_root, fixture_path, spawn, pos_row, pos_col, sgr, found_at_row}
use std::base64 {B64.encode_std}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def caret_here (s : String) : Bool :=
    String.contains s ";7m" || String.contains s "[7m"

/// The alt-screen switch is emitted before the first frame; wait for the
/// caret itself so the snapshot cannot race the paint under CI load.
def first_frame (o : Output) : Bool :=
    Bool.and (saw_alt o) (caret_here o.raw)

def found (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def since_caret (o : Output) (mark : I64) : Bool :=
    caret_here (Output.since o mark)

def input_go (m : Mty) : IO Bool := do {
    let up <- Mty.wait_until m first_frame 6000;
    let o0 <- Mty.output m;
    let a <- Check.report "startup caret is visible without a key" (caret_here o0.raw);
    Mty.send_text m "hello";
    let landed <- Mty.wait_until m (fn (o : Output) => found o "hello") 3000;
    let b <- Check.report "typed text lands in the input box" landed;
    let o1 <- Mty.output m;
    let c <- Check.report "typed text is on the input row" (found_at_row o1 "hello" 21);
    let row := match Output.find o1 "hello" { Option.some p => pos_row p, Option.none => 21 };
    let col := match Output.find o1 "hello" { Option.some p => pos_col p, Option.none => 1 };
    // Click just before the 'e' (col + 1) and type X -> hXello.
    let click := col + 1;
    Mty.send_text m (sgr 0 click row "M");
    Mty.pump m 200;
    Mty.send_text m (sgr 0 click row "m");
    Mty.pump m 200;
    Mty.send_text m "X";
    let clicked <- Mty.wait_until m (fn (o : Output) => found o "hXello") 3000;
    let d <- Check.report "a click places the caret" clicked;
    // Drag from the 'h' over two cells and release: copy hXe.
    Mty.send_text m (sgr 0 col row "M");
    Mty.pump m 200;
    Mty.send_text m (sgr 32 (col + 2) row "M");
    Mty.pump m 200;
    let payload := String.concat "\u{1b}]52;c;"
        (String.concat (B64.encode_std (String.to_list "hXe")) "\u{1b}\\");
    Mty.send_text m (sgr 0 (col + 2) row "m");
    let copied <- Mty.wait_until m (fn (o : Output) => Output.contains o payload) 3000;
    let e <- Check.report "an input drag copies its text via OSC 52" copied;
    let o2 <- Mty.output m;
    let mark := String.length o2.raw;
    Mty.send_text m "\n";
    let caret_back <- Mty.wait_until m (fn (o : Output) => since_caret o mark) 3000;
    let f <- Check.report "the caret returns after a submit" caret_back;
    Mty.finish m;
    return (up && a && b && c && d && e && f)
}

def input_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_select.json";
    let r <- spawn bin "mock" 24 80 root (Option.some turns) List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL mty input spawn: " e); return false },
        Result.ok m => input_go m
    }
}

pub def run_input_caret_click_drag : IO Bool :=
    run_gated "mty weaver input" test_input_body

def test_input_body (bin : String) : IO Bool :=
    with_root "input" (fn (root : String) => input_run bin root)
