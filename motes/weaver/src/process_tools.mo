/// `read_process` / `kill_process` / `list_processes`: the model-facing
/// half of the background-process store (`procs.mo`). `shell` starts the
/// tasks (`shell_tool.mo`; `wait_seconds: 0` starts one without waiting).
/// Schemas mirror shuttle's shell tool: a flat object of string params.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.make_object, Json.make_str, Json.make_array, Json.get_array,
    Json.Number, Json.get_object, Json.object_get, Json.get_num, Json.get_num_i64, Json.get_str,
}
use parsec::number {parse_i64}
use std::concurrent::combine {sleepIO}
use weaver::process_args {ReadProcessArgs, KillProcessArgs}
use std::map {Map, BTreeMap}
use std::io {IO.current_time_nano}
use std::path {Path}
use init::transformers {ResultT}
use weaver::procs {
    ProcEntry, ProcStatus, ProcStatus.text, Procs.list, Procs.entry, Procs.entry_at, Procs.root, Procs.tail, Procs.kill, Procs.log_kill,
}
use weaver::format {format_elapsed}
use log::logger {Logger}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

pub def str_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "string")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

#[partial]
def params_to_map (params : List (Pair String Json)) (acc : BTreeMap String Json) : BTreeMap String Json :=
    match params {
        List.empty => acc,
        List.cons p rest => match p { Pair.pair k v => params_to_map rest (Map.insert k v acc) },
    }

def pair_fst (p : Pair String Json) : Json :=
    Json.make_str (match p { Pair.pair k _ => k })

def params_schema (params : List (Pair String Json)) : Json :=
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object (params_to_map params BTreeMap.empty))
            (Map.insert "required" (Json.make_array (List.map pair_fst params)) BTreeMap.empty)))

// ── read_process ────────────────────────────────────────────────────────

def read_schema : Json :=
    let wait : Json := Json.make_object (Map.insert "type" (Json.make_str "integer")
        (Map.insert "description" (Json.make_str "Optional: wait up to this many seconds (max 60) for the task to exit before answering.") BTreeMap.empty)) in
    let props : BTreeMap String Json :=
        Map.insert "wait_seconds" wait (params_to_map [str_param "id" "The task id returned by shell."] BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props)
            (Map.insert "required" (Json.make_array [Json.make_str "id"]) BTreeMap.empty)))

pub def ReadProcessTool.spec : ToolSpec :=
    { name := "read_process",
        description := "Show a background task's status and its last 40 output lines. To wait for a task, pass wait_seconds instead of calling read_process repeatedly.",
        schema := read_schema }

pub def ReadProcessTool.impl : ToolImpl := ReadProcessTool.impl_with (fn (_ : Unit) => IO.pure false)

/// The tool with the turn's stop request (Esc), which ends a wait early.
pub def ReadProcessTool.impl_with (stop : Unit -> IO Bool) : ToolImpl :=
    { spec := ReadProcessTool.spec, cap := Capability.read, run := read_run stop }

def read_entry (id : String) (e : ProcEntry) (note : String) : IO Content := do {
    let now <- IO.current_time_nano;
    let lines <- Procs.tail e 40;
    let body : String := if List.is_empty lines then "(no output)" else String.concat_list lines;
    let head : String := String.concat "id " (String.concat e.id
        (String.concat ": " (String.concat (ProcStatus.text e.status)
            (String.concat "  " (String.concat (format_elapsed ((now - e.started_ns) / 100000000))
                (String.concat "\ncommand: " (String.concat e.command
                    "\n--- last 40 lines ---\n")))))));
    IO.pure (tool_ok id (String.concat_list [head, body, note]))
}

def read_found (id : String) (task : String) (note : String) (found : Option ProcEntry) : IO Content :=
    match found {
        Option.none => IO.pure (tool_err id (String.concat "unknown task: " task)),
        Option.some e => read_entry id e note,
    }

def read_lookup (root : Path) (id : String) (task : String) (note : String) : IO Content := do {
    let found <- Procs.entry_at root task;
    read_found id task note found
}

/// The longest `wait_seconds` honoured.
def max_wait_seconds : I64 := 60

def num_int (n : Result String Json.Number) : Option I64 :=
    match Json.get_num_i64 n {
        Result.ok i => Option.some i,
        Result.err _ => Option.none,
    }

def str_int (r : Result String String) : Option I64 :=
    match r {
        Result.ok t => parse_i64 (String.trim t),
        Result.err _ => Option.none,
    }

/// Integer argument `key`, as a number or a numeric string, clamped to
/// 0..`max`; `fallback` when it is absent or unreadable.
pub def int_arg (key : String) (fallback : I64) (max : I64) (j : Json) : I64 :=
    let got : Option I64 := match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => match Json.object_get key o {
            Option.none => Option.none,
            Option.some w => match num_int (Json.get_num w) {
                Option.some i => Option.some i,
                Option.none => str_int (Json.get_str w),
            },
        },
    } in
    match got {
        Option.none => fallback,
        Option.some n => if n < 0 then 0 else if n > max then max else n,
    }

/// `wait_seconds`, clamped to 0..60.
def wait_of (j : Json) : I64 := int_arg "wait_seconds" 0 max_wait_seconds j

/// A JSON-Schema integer property.
pub def int_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "integer")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

/// `{"type":"object", ...}` with `required` naming only some properties.
pub def object_schema (props : List (Pair String Json)) (required : List String) : Json :=
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object (params_to_map props BTreeMap.empty))
            (Map.insert "required" (Json.make_array (List.map Json.make_str required)) BTreeMap.empty)))

def still_running (found : Option ProcEntry) : Bool :=
    match found {
        Option.some e => match e.status { ProcStatus.running => true, _ => false },
        Option.none => false,
    }

/// Poll the task's own directory every 250 ms until it stops running,
/// the deadline passes, or the turn is asked to stop: one tool call
/// instead of a model call per poll. True when the stop ended it.
#[partial]
def wait_exit (root : Path) (task : String) (deadline : I64) (stop : Unit -> IO Bool) : IO Bool := do {
    let found <- Procs.entry_at root task;
    let now <- IO.current_time_nano;
    if Bool.and (still_running found) (now < deadline)
    then wait_unless_stopped root task deadline stop
    else IO.pure false
}

#[partial]
def wait_unless_stopped (root : Path) (task : String) (deadline : I64) (stop : Unit -> IO Bool) : IO Bool := do {
    let stopped <- stop unit;
    if stopped
    then IO.pure true
    else do {
        sleepIO 250;
        wait_exit root task deadline stop
    }
}

/// `read_process` against the task store at `root`: wait first when
/// asked. Esc ends the wait (the task keeps running) and says so.
pub def read_at (root : Path) (id : String) (task : String) (secs : I64) (stop : Unit -> IO Bool) : IO Content := do {
    let now <- IO.current_time_nano;
    let stopped <- if secs > 0 then wait_exit root task (now + secs * 1000000000) stop else IO.pure false;
    read_lookup root id task (if stopped then "\n[wait interrupted by the user; the task is still running]" else "")
}

def read_run (stop : Unit -> IO Bool) (id : String) (j : Json) : ResultT String IO Content :=
    match ReadProcessArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let root <- Procs.root;
                let c <- read_at root id args.id (wait_of j) stop;
                IO.pure (Result.ok c)
            }),
    }

// ── kill_process ────────────────────────────────────────────────────────

def kill_params : List (Pair String Json) :=
    [str_param "id" "The task id to stop."]

pub def KillProcessTool.spec : ToolSpec :=
    { name := "kill_process", description := "Stop a background task (SIGTERM, then SIGKILL).", schema := params_schema kill_params }

pub def KillProcessTool.impl (log : Option Logger) : ToolImpl :=
    { spec := KillProcessTool.spec, cap := Capability.exec, run := kill_run log }

def kill_entry (log : Option Logger) (id : String) (e : ProcEntry) : IO Content := do {
    let r <- Procs.kill e;
    let _ <- Procs.log_kill log "model" e r;
    match r {
        Result.ok msg => IO.pure (tool_ok id msg),
        Result.err msg => IO.pure (tool_err id (String.concat "kill_process: " msg)),
    }
}

def kill_found (log : Option Logger) (id : String) (task : String) (found : Option ProcEntry) : IO Content :=
    match found {
        Option.none => IO.pure (tool_err id (String.concat "unknown task: " task)),
        Option.some e => kill_entry log id e,
    }

def kill_lookup (log : Option Logger) (id : String) (task : String) : IO Content := do {
    let found <- Procs.entry task;
    kill_found log id task found
}

def kill_run (log : Option Logger) (id : String) (j : Json) : ResultT String IO Content :=
    match KillProcessArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let c <- kill_lookup log id args.id;
                IO.pure (Result.ok c)
            }),
    }

// ── list_processes ──────────────────────────────────────────────────────

pub def ListProcessesTool.spec : ToolSpec :=
    { name := "list_processes", description := "List this run's background tasks.", schema := params_schema List.empty }

pub def ListProcessesTool.impl : ToolImpl :=
    { spec := ListProcessesTool.spec, cap := Capability.read, run := list_run }

#[partial]
def line_of (e : ProcEntry) (now : I64) (acc : List String) : List String :=
    List.cons (String.concat e.id (String.concat "  " (String.concat (ProcStatus.text e.status)
        (String.concat "  " (String.concat (format_elapsed ((now - e.started_ns) / 100000000))
            (String.concat "  " e.command)))))) acc

#[partial]
def lines_of (xs : List ProcEntry) (now : I64) (acc : List String) : List String :=
    match xs {
        List.empty => List.reverse acc,
        List.cons e rest => lines_of rest now (line_of e now acc),
    }

def list_run (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let entries <- Procs.list;
        let now <- IO.current_time_nano;
        let body : String := if List.is_empty entries then "no background processes" else String.concat_list (lines_of entries now List.empty);
        IO.pure (Result.ok (tool_ok id body))
    })
