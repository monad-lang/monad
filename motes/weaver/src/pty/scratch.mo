// weaver / pty / scratch -- the session scratch dir in a real terminal.
//
// In auto mode a scratch-only command runs with no dialog and no refusal:
// $WEAVER_SCRATCH and $TMPDIR point at the session's own scratch dir, a
// wildcard delete there is not "dangerous", and the dir exists on disk.
// Tool output is collapsed in the transcript, so the assertions read the
// files the command left in the scratch dir (and the turn's final text,
// which only arrives if the classifier was skipped -- it would otherwise
// have consumed that scripted turn).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args}
use weaver::pty_fixtures {write_turns, tool_use_turn_json, text_turn_json}
use json::json {Json, Json.make_object_pairs, Json.make_str}
use std::io {IO.println, IO.is_dir, IO.list_dir, IO.file_exists, IO.read_file}
use std::stream {StreamError}
use std::path {Path, Path.to_string, Path.join}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false,
    }

def shell_turn (id : String) (command : String) : Json :=
    let input : Json := Json.make_object_pairs [Pair.pair "command" (Json.make_str command)] in
    tool_use_turn_json id "shell" input

/// Writes the two env vars, creates and deletes a directory, and leaves a
/// marker: the three things the scratch dir promises.
def scratch_command : String :=
    "printf '%s\\n' \"$WEAVER_SCRATCH\" > \"$WEAVER_SCRATCH\"/env.txt; printf '%s\\n' \"$TMPDIR\" > \"$WEAVER_SCRATCH\"/tmp.txt; mkdir -p \"$WEAVER_SCRATCH\"/junk; rm -rf \"$WEAVER_SCRATCH\"/junk; touch \"$WEAVER_SCRATCH\"/marker"

def write_script (path : String) : IO Bool :=
    write_turns path
        [shell_turn "s1" scratch_command,
            text_turn_json "scratch work finished"]

#[partial]
def check_dirs (dirs : List Path) : IO Bool :=
    match dirs {
        List.empty => IO.pure false,
        List.cons d rest => do {
            let sc : Path := Path.join d (Path.path "scratch");
            let there <- IO.is_dir sc;
            if Bool.not there then check_dirs rest
            else do {
                let marker <- IO.file_exists (Path.join sc (Path.path "marker"));
                let env <- IO.read_file (Path.join sc (Path.path "env.txt"));
                let tmp <- IO.read_file (Path.join sc (Path.path "tmp.txt"));
                let junk <- IO.is_dir (Path.join sc (Path.path "junk"));
                let ok : Bool := Bool.and marker (Bool.and (Bool.not junk) (Bool.and (env_is env sc) (env_is tmp sc)));
                if ok then IO.pure true else check_dirs rest
            }
        },
    }

def env_is (r : Result StreamError String) (sc : Path) : Bool :=
    match r {
        Result.ok text => String.contains text (Path.to_string sc),
        Result.err _ => false,
    }

def scratch_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_scratch.json";
    let wrote <- write_script turns;
    if Bool.not wrote then do {
        IO.println "FAIL pty scratch: could not write the turn script";
        return false
    } else do {
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 30 100 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty scratch spawn: " e); return false },
            Result.ok m => do {
                let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
                Pty.send_text m "/mode auto\r";
                let auto <- Pty.wait_until m (fn (o : Output) => grid_has o "[auto]") 3000;
                let a <- Check.report "auto mode is on" (Bool.and ready auto);
                Pty.send_text m "go\r";
                // The final turn's text only lands if the shell pick skipped
                // the classifier (which would have eaten this scripted turn).
                let done <- Pty.wait_until m (fn (o : Output) => grid_has o "scratch work finished") 10000;
                let b <- Check.report "the scratch command ran and the turn continued" done;
                let no_dialog <- Pty.wait_until m (fn (o : Output) => grid_has o "Permission required") 300;
                let c <- Check.report "no approval dialog appeared" (Bool.not no_dialog);
                let sessions <- IO.list_dir (Path.path (String.concat root "/sessions"));
                let there <- check_dirs sessions;
                let d <- Check.report "the scratch dir holds the env files, the marker, and no junk" there;
                Pty.finish m;
                return (a && b && c && d)
            },
        }
    }
}

pub def run_scratch_dir_and_env : IO Bool :=
    run_gated "pty weaver scratch" (fn (bin : String) => with_root "scratch" (fn (root : String) => scratch_run bin root))
