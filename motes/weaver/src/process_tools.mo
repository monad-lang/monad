/// `start_process` / `read_process` / `kill_process` / `list_processes`:
/// the model-facing half of the background-process store (`procs.mo`).
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
use weaver::process_args {StartProcessArgs, ReadProcessArgs, KillProcessArgs}
use std::map {Map, BTreeMap}
use std::io {IO.current_time_nano}
use std::path {Path, Path.to_string}
use init::transformers {ResultT}
use weaver::procs {
    ProcEntry, ProcStatus, ProcStatus.text, Procs.start, Procs.list, Procs.entry, Procs.entry_at, Procs.root, Procs.tail, Procs.kill, Procs.log_start, Procs.log_kill,
}
use weaver::format {format_elapsed}
use log::logger {Logger}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

def str_param (name : String) (desc : String) : Pair String Json :=
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

// ── start_process ───────────────────────────────────────────────────────

def start_params : List (Pair String Json) :=
    [str_param "command" "Shell command to run detached. Its stdout and stderr go to a per-task log.",
        str_param "cwd" "Working directory, or \"\" to inherit weaver's."]

pub def StartProcessTool.spec : ToolSpec :=
    { name := "start_process", description := "Start a background shell command; returns its task id and log path.", schema := params_schema start_params }

pub def StartProcessTool.impl (log : Option Logger) : ToolImpl :=
    { spec := StartProcessTool.spec, cap := Capability.exec, run := start_run log }

def start_run (log : Option Logger) (id : String) (j : Json) : ResultT String IO Content :=
    match StartProcessArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let r <- Procs.start args.command args.cwd;
                match r {
                    Result.err e => IO.pure (Result.ok (tool_err id (String.concat "start_process: " e))),
                    Result.ok e2 => do {
                        let _ <- Procs.log_start log e2;
                        let text : String := String.concat "started " (String.concat e2.id
                            (String.concat " (pid " (String.concat (I64.to_string e2.pid)
                                (String.concat ")\nlog: " (String.concat (Path.to_string e2.log)
                                    "\nUse read_process to poll; kill_process to stop.")))));
                        IO.pure (Result.ok (tool_ok id text))
                    },
                }
            }),
    }

// ── read_process ────────────────────────────────────────────────────────

def read_schema : Json :=
    let wait : Json := Json.make_object (Map.insert "type" (Json.make_str "integer")
        (Map.insert "description" (Json.make_str "Optional: wait up to this many seconds (max 60) for the task to exit before answering.") BTreeMap.empty)) in
    let props : BTreeMap String Json :=
        Map.insert "wait_seconds" wait (params_to_map [str_param "id" "The task id returned by start_process."] BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props)
            (Map.insert "required" (Json.make_array [Json.make_str "id"]) BTreeMap.empty)))

pub def ReadProcessTool.spec : ToolSpec :=
    { name := "read_process",
        description := "Show a background task's status and its last 40 output lines. To wait for a task, pass wait_seconds instead of calling read_process repeatedly.",
        schema := read_schema }

pub def ReadProcessTool.impl : ToolImpl :=
    { spec := ReadProcessTool.spec, cap := Capability.read, run := read_run }

def read_entry (id : String) (e : ProcEntry) : IO Content := do {
    let now <- IO.current_time_nano;
    let lines <- Procs.tail e 40;
    let body : String := if List.is_empty lines then "(no output)" else String.concat_list lines;
    let head : String := String.concat "id " (String.concat e.id
        (String.concat ": " (String.concat (ProcStatus.text e.status)
            (String.concat "  " (String.concat (format_elapsed ((now - e.started_ns) / 100000000))
                (String.concat "\ncommand: " (String.concat e.command
                    "\n--- last 40 lines ---\n")))))));
    IO.pure (tool_ok id (String.concat head body))
}

def read_found (id : String) (task : String) (found : Option ProcEntry) : IO Content :=
    match found {
        Option.none => IO.pure (tool_err id (String.concat "unknown task: " task)),
        Option.some e => read_entry id e,
    }

def read_lookup (root : Path) (id : String) (task : String) : IO Content := do {
    let found <- Procs.entry_at root task;
    read_found id task found
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

/// `wait_seconds` as a number or a numeric string, clamped to 0..60.
def wait_of (j : Json) : I64 :=
    let got : Option I64 := match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => match Json.object_get "wait_seconds" o {
            Option.none => Option.none,
            Option.some w => match num_int (Json.get_num w) {
                Option.some i => Option.some i,
                Option.none => str_int (Json.get_str w),
            },
        },
    } in
    match got {
        Option.none => 0,
        Option.some n => if n < 0 then 0 else if n > max_wait_seconds then max_wait_seconds else n,
    }

def still_running (found : Option ProcEntry) : Bool :=
    match found {
        Option.some e => match e.status { ProcStatus.running => true, _ => false },
        Option.none => false,
    }

/// Poll the task's own directory every 250 ms until it stops running or
/// the deadline passes: one tool call instead of a model call per poll.
#[partial]
def wait_exit (root : Path) (task : String) (deadline : I64) : IO Unit := do {
    let found <- Procs.entry_at root task;
    let now <- IO.current_time_nano;
    if Bool.and (still_running found) (now < deadline)
    then do {
        sleepIO 250;
        wait_exit root task deadline
    }
    else IO.pure unit
}

/// `read_process` against the task store at `root`: wait first when asked.
def read_at (root : Path) (id : String) (task : String) (secs : I64) : IO Content := do {
    let now <- IO.current_time_nano;
    let _ <- if secs > 0 then wait_exit root task (now + secs * 1000000000) else IO.pure unit;
    read_lookup root id task
}

def read_run (id : String) (j : Json) : ResultT String IO Content :=
    match ReadProcessArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let root <- Procs.root;
                let c <- read_at root id args.id (wait_of j);
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
