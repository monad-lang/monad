// weaver / pty / boot -- the UI opens before startup finishes: a loading
// box ("Starting weaver") draws first, and a line typed straight away is
// queued and answered once the session is up.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args}
use weaver::pty_fixtures {write_turns, text_turn_json}
use std::io {IO.println}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false,
    }

def boot_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_boot.json";
    let wrote <- write_turns turns [text_turn_json "booted and answered"];
    if Bool.not wrote then do {
        IO.println "FAIL pty boot: could not write the turn script";
        return false
    } else do {
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 30 100 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty boot spawn: " e); return false },
            Result.ok m => boot_go m,
        }
    }
}

def boot_go (m : Pty) : IO Bool := do {
    // The loading box is the first frame; on a fast start it may show for
    // one frame only, so the raw stream (not the grid) is checked.
    let box <- Pty.wait_until m (fn (o : Output) => String.contains (Output.tight o) "Startingweaver") 6000;
    let a <- Check.report "the loading box draws before the session is up" box;
    Pty.send_text m "hello\r";
    let answered <- Pty.wait_until m (fn (o : Output) => grid_has o "booted and answered") 10000;
    let b <- Check.report "a line typed during startup is answered once it is up" answered;
    Pty.finish m;
    return (a && b)
}

pub def run_boot_opens_the_ui_first : IO Bool :=
    run_gated "pty weaver boot" (fn (bin : String) => with_root "boot" (fn (root : String) => boot_run bin root))
