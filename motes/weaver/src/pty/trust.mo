// weaver / pty / trust -- a project with an AGENTS.md is asked about before
// the TUI starts: `n` starts untrusted with a note, `y` is recorded (and
// loads the file, named in the startup note) so the next start does not
// ask, and an edit to the file asks again.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args, read_text}
use std::test {Test.write_fixture}

def asked (o : Output) : Bool :=
    String.contains (Output.stripped o) "Trust this project?"

def frame_up (o : Output) : Bool :=
    String.contains (Output.tight o) "typeamessage"

/// `PWD` too: `Place.probe` reads it, and the pty's `chdir` into the
/// root does not change the driver's inherited value.
def untrusted_env (root : String) : List (Pair String (Option String)) :=
    [Pair.pair "WEAVER_TRUST" (Option.some "0"), Pair.pair "PWD" (Option.some root)]

/// One start: wait for the question (or the frame, when `expect_ask` is
/// false), answer, wait for the frame showing `needle` (spaces removed), and quit with a
/// double Ctrl+C.
def one_start (bin : String) (root : String) (answer : String) (expect_ask : Bool) (needle : String) : IO Bool := do {
    let r <- spawn_args bin "mock" List.empty 24 100 root Option.none (untrusted_env root);
    match r {
        Result.err _ => IO.pure false,
        Result.ok m => start_go m answer expect_ask needle,
    }
}

def start_go (m : Pty) (answer : String) (expect_ask : Bool) (needle : String) : IO Bool := do {
    let q <- Pty.wait_until m (fn (o : Output) => asked o || frame_up o) 6000;
    let o0 <- Pty.output m;
    let saw : Bool := asked o0;
    let _ <- if saw then Pty.send_text m (String.concat answer "\n") else IO.pure unit;
    let up <- Pty.wait_until m (fn (o : Output) => frame_up o && String.contains (Output.tight o) needle) 6000;
    Pty.send_text m "\u{3}";
    Pty.send_text m "\u{3}";
    Pty.finish m;
    IO.pure (q && up && (if saw then expect_ask else Bool.not expect_ask))
}

def trust_run (bin : String) (root : String) : IO Bool := do {
    let _ <- Test.write_fixture (Path.path (String.concat root "/AGENTS.md")) "Always answer in haiku.\n";
    let first <- one_start bin root "n" true "projectnottrusted";
    let a <- Check.report "a new project is asked about, and n leaves it untrusted" first;
    let second <- one_start bin root "y" true "instructions:";
    let b <- Check.report "asked again after n; y starts trusted with AGENTS.md loaded" second;
    let rec <- read_text (String.concat root "/.weaver/trusted.json");
    let c <- Check.report "the yes is recorded" (String.contains rec "Always answer in haiku.");
    let third <- one_start bin root "" false "AGENTS.md(repo";
    let d <- Check.report "a recorded project starts without the question, AGENTS.md loaded" third;
    let _ <- Test.write_fixture (Path.path (String.concat root "/AGENTS.md")) "Always answer in limericks.\n";
    let fourth <- one_start bin root "n" true "";
    let e <- Check.report "an edited AGENTS.md is asked about again" fourth;
    return (a && b && c && d && e)
}

pub def run_trust_asks_records_and_reasks : IO Bool :=
    run_gated "pty weaver trust" (fn (bin : String) => with_root "trust" (fn (root : String) => trust_run bin root))
