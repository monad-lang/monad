// weaver / pty / rss -- roadmap PR 2's app-level gate: a 100-tool turn in
// auto mode must not grow RSS by the old ~21 MB per tool call. Two identical
// turns; the delta between them is steady-state growth.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args, rss_kb}
use weaver::pty_fixtures {write_turns, tool_use_turn_json, text_turn_json}
use json::json {Json, Json.make_object_pairs, Json.make_str}
use std::io {IO.println}
use std::path {Path}
use std::test {Test.write_fixture}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def read_input (path : String) : Json :=
    Json.make_object_pairs [Pair.pair "path" (Json.make_str path)]

#[partial]
def tool_turns (n : I64) (i : I64) (path : String) (acc : List Json) : List Json :=
    if I64.lt n 1
    then List.reverse acc
    else tool_turns (n - 1) (i + 1) path
        (List.cons (tool_use_turn_json (String.concat "r" (I64.to_string i)) "read" (read_input path)) acc)

/// 100 reads, a final text, then the same again: the mock indexes by the
/// history's assistant count, so the second block starts where the first ends.
def script_turns (path : String) : List Json :=
    List.append
        (List.append (tool_turns 100 0 path List.empty) [text_turn_json "done one"])
        (List.append (tool_turns 100 100 path List.empty) [text_turn_json "done two"])

/// 100 tool calls adding more than 200 MB is the leak; healthy growth is a
/// few MB of history.
def rss_bound_kb : I64 := 200000

def rss_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
    Pty.send_text m "/mode auto\r";
    let auto <- Pty.wait_until m (fn (o : Output) => grid_has o "auto") 3000;
    let a <- Check.report "auto mode is on" (ready && auto);
    Pty.send_text m "go\r";
    let one <- Pty.wait_until m (fn (o : Output) => grid_has o "done one") 90000;
    let b <- Check.report "the first 100-tool turn completes" one;
    let before <- rss_kb (Pty.child_pid m);
    Pty.send_text m "go\r";
    let two <- Pty.wait_until m (fn (o : Output) => grid_has o "done two") 90000;
    let c <- Check.report "the second 100-tool turn completes" two;
    let after <- rss_kb (Pty.child_pid m);
    let delta : I64 := after - before;
    IO.println (String.concat "INFO VmRSS before=" (String.concat (I64.to_string before)
        (String.concat " after=" (String.concat (I64.to_string after)
            (String.concat " delta_kb=" (I64.to_string delta))))));
    let d <- Check.report "100 tool calls grow RSS by under 200 MB" (I64.lt delta rss_bound_kb);
    Pty.finish m;
    return (a && b && c && d)
}

def rss_run (bin : String) (root : String) : IO Bool := do {
    let note : String := String.concat root "/small.txt";
    let _ <- Test.write_fixture (Path.path note) "hello\n";
    let turns := String.concat root "/turns_rss.json";
    let wrote <- write_turns turns (script_turns note);
    if Bool.not wrote then do {
        IO.println "FAIL pty rss: could not write the turn script";
        return false
    } else do {
        let env : List (Pair String (Option String)) := [Pair.pair "PWD" (Option.some root)];
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) env;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty rss spawn: " e); return false },
            Result.ok m => rss_go m root
        }
    }
}

pub def run_a_100_tool_turn_stays_bounded : IO Bool :=
    run_gated "pty weaver rss" (fn (bin : String) => with_root "rss" (fn (root : String) => rss_run bin root))
