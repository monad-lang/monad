// weaver / pty / approvals -- auto mode runs an ordinary command without
// asking and REFUSES a destructive one: the first shell call (`touch
// ran_ok`) runs unprompted, the second (`git push --force`) is denied with
// its danger reason, and the turn continues to the model's final answer
// with no keypress (a dialog would have blocked it).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args}
use weaver::pty_fixtures {write_turns, tool_use_turn_json, text_turn_json}
use json::json {Json, Json.make_object_pairs, Json.make_str}
use std::io {IO.println, IO.read_file}
use std::path {Path}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def shell_turn (id : String) (command : String) : Json :=
    let input : Json := Json.make_object_pairs [Pair.pair "command" (Json.make_str command)] in
    tool_use_turn_json id "shell" input

def write_script (path : String) : IO Bool :=
    write_turns path
        [shell_turn "s1" "touch ran_ok",
            shell_turn "s2" "git push --force",
            text_turn_json "finished both"]

def file_exists (path : String) : IO Bool := do {
    let r <- IO.read_file (Path.path path);
    return (match r { Result.ok _ => true, Result.err _ => false })
}

def approvals_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
    Pty.send_text m "/mode auto\r";
    let auto <- Pty.wait_until m (fn (o : Output) => grid_has o "auto") 3000;
    let a <- Check.report "auto mode is on" (Bool.and ready auto);
    Pty.send_text m "go\r";
    let refused <- Pty.wait_until m (fn (o : Output) => grid_has o "refused a dangerous command") 8000;
    let b <- Check.report "git push --force is refused with its reason" refused;
    let ran <- file_exists (String.concat root "/ran_ok");
    let c <- Check.report "the plain command ran without asking" ran;
    let done <- Pty.wait_until m (fn (o : Output) => grid_has o "finished both") 8000;
    let d <- Check.report "the turn continues after the refusal, with no dialog" done;
    Pty.finish m;
    return (a && b && c && d)
}

def approvals_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_approvals.json";
    let wrote <- write_script turns;
    if Bool.not wrote then do {
        IO.println "FAIL pty approvals: could not write the turn script";
        return false
    } else do {
        // The workspace is the test root, as it would be for a user there.
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty approvals spawn: " e); return false },
            Result.ok m => approvals_go m root
        }
    }
}

pub def run_auto_mode_refuses_destructive_commands : IO Bool :=
    run_gated "pty weaver approvals" (fn (bin : String) => with_root "approvals" (fn (root : String) => approvals_run bin root))
