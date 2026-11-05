// weaver / pty / todos -- a turn that calls todo_write shows the list
// above the status row, and Ctrl+T folds it to its summary line.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args, report_screen}
use weaver::pty_fixtures {write_turns, tool_use_turn_json, text_turn_json}
use json::json {Json, Json.make_object_pairs, Json.make_str, Json.make_array}
use std::io {IO.println}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def item (content : String) (status : String) (active : String) : Json :=
    Json.make_object_pairs
        [Pair.pair "content" (Json.make_str content), Pair.pair "status" (Json.make_str status),
            Pair.pair "active_form" (Json.make_str active)]

def write_script (path : String) : IO Bool :=
    let input : Json := Json.make_object_pairs [Pair.pair "todos" (Json.make_array
        [item "Read the module" "completed" "", item "Run the tests" "in_progress" "Running the tests",
            item "Commit the fix" "pending" ""])] in
    write_turns path [tool_use_turn_json "t1" "todo_write" input, text_turn_json "listed the steps"]

def todos_go (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
    Pty.send_text m "go\r";
    let shown <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "todos 1/3") (Bool.and (grid_has o "Running the tests") (grid_has o "Commit the fix"))) 8000;
    let a <- report_screen m "the todo panel lists the items" (Bool.and ready shown);
    let done <- Pty.wait_until m (fn (o : Output) => grid_has o "listed the steps") 6000;
    let b <- Check.report "todo_write runs without an approval" done;
    Pty.send_text m "\u{14}";
    let folded <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "(ctrl+t)") (Bool.not (grid_has o "Commit the fix"))) 3000;
    let c <- Check.report "Ctrl+T folds the panel to its summary" folded;
    Pty.finish m;
    return (a && b && c)
}

def todos_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_todos.json";
    let wrote <- write_script turns;
    if Bool.not wrote then do {
        IO.println "FAIL pty todos: could not write the turn script";
        return false
    } else do {
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty todos spawn: " e); return false },
            Result.ok m => todos_go m
        }
    }
}

pub def run_todo_panel_shows_and_folds : IO Bool :=
    run_gated "pty weaver todos" (fn (bin : String) => with_root "todos" (fn (root : String) => todos_run bin root))
