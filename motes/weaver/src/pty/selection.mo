// weaver / pty / selection -- a drag over transcript text paints reverse
// video and copies the span through OSC 52, including a pair of wide glyphs.
// Ported from pty_repro_selection.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn, sgr, pos_row, pos_col}
use std::base64 {B64.encode_std}
use std::io {IO.println}

def found (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def osc52 (text : String) : String :=
    String.concat "\u{1b}]52;c;"
        (String.concat (B64.encode_std (String.to_list text)) "\u{1b}\\")

def reverse_seen (o : Output) (mark : I64) : Bool :=
    let s := Output.since o mark in
    String.contains s "\u{1b}[7m" || String.contains s ";7m"

def selection_go (m : Pty) : IO Bool := do {
    let mouse <- Pty.wait_until m (fn (o : Output) => Output.contains o "\u{1b}[?1002h") 6000;
    let a <- Check.report "mouse drag reporting enabled (?1002h)" mouse;
    Pty.send_text m "go\n";
    let rendered <- Pty.wait_until m (fn (o : Output) => found o "hello") 6000;
    let b <- Check.report "reply rendered" rendered;
    let o0 <- Pty.output m;
    let spot := match Output.find o0 "hello" {
        Option.some p => p,
        Option.none => Pair.pair 0 0
    };
    let r := pos_row spot;
    let c := pos_col spot;
    Pty.send_text m (sgr 0 c r "M");
    Pty.pump m 200;
    Pty.send_text m (sgr 32 (c + 5) r "M");
    Pty.pump m 200;
    let o1 <- Pty.output m;
    let mark := String.length o1.raw;
    Pty.send_text m (sgr 0 (c + 5) r "m");
    let hl <- Pty.wait_until m (fn (o : Output) => reverse_seen o mark) 3000;
    let d <- Check.report "drag paints a reverse-video highlight" hl;
    let copied <- Pty.wait_until m (fn (o : Output) => Output.contains o (osc52 "hello")) 3000;
    let e <- Check.report "release copies 'hello' via OSC 52" copied;
    let wide <- Pty.wait_until m (fn (o : Output) => found o "日本") 3000;
    let f <- Check.report "wide reply rendered" wide;
    let o2 <- Pty.output m;
    let spot2 := match Output.find o2 "日本" {
        Option.some p => p,
        Option.none => Pair.pair 0 0
    };
    let r2 := pos_row spot2;
    let c2 := pos_col spot2;
    let mark2 := String.length o2.raw;
    Pty.send_text m (sgr 0 c2 r2 "M");
    Pty.pump m 200;
    Pty.send_text m (sgr 32 (c2 + 3) r2 "M");
    Pty.pump m 300;
    Pty.send_text m (sgr 0 (c2 + 3) r2 "m");
    let copied2 <- Pty.wait_until m (fn (o : Output) => String.contains (Output.since o mark2) (osc52 "日本")) 3000;
    let g <- Check.report "release copies the wide glyphs via OSC 52" copied2;
    Pty.finish m;
    return (Bool.and a (Bool.and b (Bool.and d (Bool.and e (Bool.and f g)))))
}

def selection_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_select.json";
    let r <- spawn bin "mock" 24 80 root (Option.some turns) List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty selection spawn: " e); return false },
        Result.ok m => selection_go m
    }
}

pub def run_selection_drag_and_osc52 : IO Bool :=
    run_gated "pty weaver selection" test_selection_body

def test_selection_body (bin : String) : IO Bool :=
    with_root "selection" (fn (root : String) => selection_run bin root)
