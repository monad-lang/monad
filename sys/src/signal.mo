/// Signals as an ADT. Numbers are a table here, never literals at a call
/// site (Linux x86_64/aarch64 agree on this set; Phase 10 moves the table
/// behind the backend seam for macOS/Windows).
pub type Signal {
    hup, int, quit, kill, usr1, usr2, term, cont, stop, tstp, winch,
    other (n : I64)
}

pub def Signal.number (s : Signal) : I64 :=
    match s {
        Signal.hup => 1,
        Signal.int => 2,
        Signal.quit => 3,
        Signal.kill => 9,
        Signal.usr1 => 10,
        Signal.usr2 => 12,
        Signal.term => 15,
        Signal.cont => 18,
        Signal.stop => 19,
        Signal.tstp => 20,
        Signal.winch => 28,
        Signal.other n => n
    }

pub def Signal.name (s : Signal) : String :=
    match s {
        Signal.hup => "HUP",
        Signal.int => "INT",
        Signal.quit => "QUIT",
        Signal.kill => "KILL",
        Signal.usr1 => "USR1",
        Signal.usr2 => "USR2",
        Signal.term => "TERM",
        Signal.cont => "CONT",
        Signal.stop => "STOP",
        Signal.tstp => "TSTP",
        Signal.winch => "WINCH",
        Signal.other n => String.concat "SIG" (I64.to_string n)
    }
