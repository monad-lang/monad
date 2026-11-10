// weaver / pty / skills -- a user skill is discovered at startup (the note
// names it), `/skills` lists it, and `/<name> args` runs a turn whose user
// message carries the skill's instructions and the arguments.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn_args, status_turns, quit_cleanly}
use std::test {Test.write_fixture}
use std::process {exec_cmd}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def history_has (root : String) (needle : String) : IO Bool := do {
    let rc <- exec_cmd "sh" ["-c", String.concat_list ["grep -rqF '", needle, "' ", root, "/sessions/*/history"]];
    IO.pure (rc == 0)
}

def skills_go (m : Pty) (root : String) : IO Bool := do {
    let up <- Pty.wait_until m (fn (o : Output) => tight_has o "typeamessage" && tight_has o "skills:greet") 6000;
    let a <- Check.report "the startup note names the skill" up;
    Pty.send_text m "/skills\n";
    let listed <- Pty.wait_until m (fn (o : Output) => tight_has o "/greet(user)Greetsomeonewarmly.") 4000;
    let b <- Check.report "/skills lists it" listed;
    // `/skills` is a side command: Esc closes its dialog after a quiet poll.
    Pty.send_text m "\u{1b}";
    Pty.pump m 500;
    let _ <- Pty.wait_until m (fn (o : Output) => match Output.find o "Enter/Esc close" { Option.some _ => false, Option.none => true }) 3000;
    Pty.send_text m "/greet Ada\n";
    let ran <- Pty.wait_until m (fn (o : Output) => status_turns o 1) 8000;
    let c <- Check.report "/greet runs a turn" ran;
    let quit <- quit_cleanly m 4000;
    Pty.finish m;
    let body <- history_has root "SKILL-BODY-MARKER";
    let args <- history_has root "Arguments: Ada";
    let d <- Check.report "the turn carries the instructions and the arguments" (body && args);
    IO.pure (a && b && c && quit && d)
}

def skills_run (bin : String) (root : String) : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", String.concat root "/.config/weaver/skills/greet"];
    let _ <- Test.write_fixture (Path.path (String.concat root "/.config/weaver/skills/greet/SKILL.md"))
        "---\nname: greet\ndescription: Greet someone warmly.\n---\n\nSKILL-BODY-MARKER: say hello to the person named in the arguments.\n";
    let turns <- fixture_path "turns_long.json";
    let r <- spawn_args bin "mock" List.empty 24 100 root (Option.some turns)
        [Pair.pair "PWD" (Option.some root), Pair.pair "XDG_CONFIG_HOME" Option.none];
    match r {
        Result.err e => Check.report (String.concat "spawn: " e) false,
        Result.ok m => skills_go m root,
    }
}

pub def run_skills_discover_list_and_invoke : IO Bool :=
    run_gated "pty weaver skills" (fn (bin : String) => with_root "skills" (fn (root : String) => skills_run bin root))
