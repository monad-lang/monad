// The `tui` mote's terminal-control smoke: the `term_ctl` native end to
// end (cbreak enter/leave, TIOCGWINSZ size), exercised interpreted AND
// compiled -- the Rust host's dispatch arm and runtime.c's
// `monad_term_ctl` are two implementations, and this file is how a
// divergence between them shows up. Away from a tty the mode ops print
// `false` and the size falls back to `COLUMNS`/`LINES` then 24x80, so
// the expected output does not depend on a terminal.
#![mote { name := "tui_terminal_example", deps := [tui] }]

// Dotted names are imported by their own spelling
// (`use std::process {Proc.capture}`'s pattern for `Proc.*`).
use tui::terminal {Terminal.enter_raw_mode, Terminal.leave_raw_mode, Terminal.size}

open IO {println}

def bool_str (b : Bool) : String :=
    match b { true => "true", false => "false" }

def main (args : List String) : IO Unit := do {
    let entered <- Terminal.enter_raw_mode;
    println ("enter_raw_mode: " ++ bool_str entered);
    let left <- Terminal.leave_raw_mode;
    println ("leave_raw_mode: " ++ bool_str left);
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols =>
            println ("size: rows=" ++ I64.to_string rows ++ " cols=" ++ I64.to_string cols)
    }
}
