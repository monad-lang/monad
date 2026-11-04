// weaver / pty / resize -- a real pty shrinks and grows: each geometry change
// emits ESC[2J, the bottom border lands on the new last transcript row, and
// the long reply re-wraps to the new content width. Ported from
// pty_repro_resize.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use pty::grid {Grid}
use weaver::pty_support {
    run_gated, with_root, fixture_path, spawn, any_row, rows_with, quit_cleanly
}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def row_has (o : Output) (r : I64) (needle : String) : Bool :=
    String.contains (Grid.row_text o.grid r) needle

def row_border (o : Output) (r : I64) : Bool :=
    Bool.and (row_has o r "╰") (row_has o r "╯")

def resize_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    let border0 <- Pty.wait_until m (fn (o : Output) => row_border o 25) 5000;
    let a <- Check.report "initial bottom border at row 26" border0;
    Pty.send_text m "go\n";
    let initial <- Pty.wait_until m (fn (o : Output) => any_row o.grid "x" 1 25) 6000;
    let b <- Check.report "reply rendered at the initial width" initial;

    let o1 <- Pty.output m;
    let mark1 := String.length o1.raw;
    Pty.resize m 24 40;
    let cleared1 <- Pty.wait_until m (fn (o : Output) => I64.gt o.grid.clears 0) 4000;
    let o2 <- Pty.output m;
    let c <- Check.report "shrink clears the screen (ESC[2J)"
        (cleared1 && String.contains (Output.since o2 mark1) "\u{1b}[2J");
    let border1 <- Pty.wait_until m (fn (o : Output) => row_border o 19) 4000;
    let d <- Check.report "shrunken bottom border at row 20" border1;
    let o3 <- Pty.output m;
    let rows1 := rows_with o3.grid "x" 1 19;
    let e <- Check.report "reply re-wrapped to the 36-cell content width"
        (I64.gt rows1 4);

    let mark2 := String.length o3.raw;
    Pty.resize m 32 100;
    let cleared2 <- Pty.wait_until m (fn (o : Output) => I64.gt o.grid.clears 0) 4000;
    let o4 <- Pty.output m;
    let f <- Check.report "grow clears the screen (ESC[2J)"
        (cleared2 && String.contains (Output.since o4 mark2) "\u{1b}[2J");
    let border2 <- Pty.wait_until m (fn (o : Output) => row_border o 27) 4000;
    let g <- Check.report "grown bottom border at row 28" border2;
    let o5 <- Pty.output m;
    let rows2 := rows_with o5.grid "x" 1 27;
    let h <- Check.report "reply re-wrapped to the 96-cell content width"
        (Bool.and (I64.gt rows2 1) (I64.lt rows2 5));

    let restored <- quit_cleanly m 3000;
    let i <- Check.report "clean exit after resize" restored;
    Pty.finish m;
    return (up && a && b && c && d && e && f && g && h && i)
}

def resize_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_resize.json";
    let r <- spawn bin "mock" 30 80 root (Option.some turns) List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty resize spawn: " e); return false },
        Result.ok m => resize_go m
    }
}

pub def run_resize_clears_and_rewraps : IO Bool :=
    run_gated "pty weaver resize" test_resize_body

def test_resize_body (bin : String) : IO Bool :=
    with_root "resize" (fn (root : String) => resize_run bin root)
