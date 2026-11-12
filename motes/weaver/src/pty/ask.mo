// weaver / pty / ask -- the `ask` tool's dialog and its auto answer.
//
// Manual mode: the model asks, the dialog appears, Space toggles two
// options and Enter confirms; the tool result carries both labels. Auto
// mode: the same turn answers the recommended option with no dialog.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args}
use weaver::pty_fixtures {write_turns, tool_use_turn_json, text_turn_json}
use json::json {Json, Json.make_object_pairs, Json.make_str, Json.make_bool, Json.make_array}
use std::io {IO.println}
use std::path {Path}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false,
    }

def ask_input : Json :=
    Json.make_object_pairs [
        Pair.pair "question" (Json.make_str "Which target?"),
        Pair.pair "multi" (Json.make_bool true),
        Pair.pair "options" (Json.make_array [
            Json.make_object_pairs [Pair.pair "label" (Json.make_str "debug")],
            Json.make_object_pairs [Pair.pair "label" (Json.make_str "release"), Pair.pair "recommended" (Json.make_bool true)],
        ]),
    ]

def write_script (path : String) : IO Bool :=
    write_turns path
        [tool_use_turn_json "a1" "ask" ask_input,
            text_turn_json "thanks for the answer"]

def ask_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_ask.json";
    let wrote <- write_script turns;
    if Bool.not wrote then do {
        IO.println "FAIL pty ask: could not write the turn script";
        return false
    } else do {
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 30 100 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty ask spawn: " e); return false },
            Result.ok m => do {
                let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
                Pty.send_text m "go\r";
                let asked <- Pty.wait_until m (fn (o : Output) => grid_has o "Which target?") 8000;
                let a <- Check.report "the question dialog appeared" (Bool.and ready asked);
                Pty.send_text m " ";
                Pty.send_text m "\u{1b}[B";
                Pty.send_text m " ";
                Pty.send_text m "\r";
                let answered <- Pty.wait_until m (fn (o : Output) => grid_has o "answers: debug, release") 8000;
                let b <- Check.report "the multi answer reached the model" answered;
                let done <- Pty.wait_until m (fn (o : Output) => grid_has o "thanks for the answer") 8000;
                let c <- Check.report "the turn continued" done;
                Pty.finish m;
                return (a && b && c)
            },
        }
    }
}

pub def run_ask_dialog_and_answer : IO Bool :=
    run_gated "pty weaver ask" (fn (bin : String) => with_root "ask" (fn (root : String) => ask_run bin root))

def ask_auto_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_ask_auto.json";
    let wrote <- write_script turns;
    if Bool.not wrote then do {
        IO.println "FAIL pty ask auto: could not write the turn script";
        return false
    } else do {
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 30 100 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty ask auto spawn: " e); return false },
            Result.ok m => do {
                let _ <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
                Pty.send_text m "/mode auto\r";
                let _ <- Pty.wait_until m (fn (o : Output) => grid_has o "[auto]") 3000;
                Pty.send_text m "go\r";
                let assumed <- Pty.wait_until m (fn (o : Output) => grid_has o "assuming release") 8000;
                let a <- Check.report "auto answered the recommended option" assumed;
                let dialog <- Pty.wait_until m (fn (o : Output) => grid_has o "Which target?") 300;
                let b <- Check.report "no question dialog appeared" (Bool.not dialog);
                Pty.finish m;
                return (a && b)
            },
        }
    }
}

pub def run_ask_auto_answers_recommended : IO Bool :=
    run_gated "pty weaver ask auto" (fn (bin : String) => with_root "ask_auto" (fn (root : String) => ask_auto_run bin root))
