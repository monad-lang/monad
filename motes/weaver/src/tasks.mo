/// weaver / tasks -- everything a turn left running or ran on the side:
/// background processes (`procs.mo`) and subagent runs (the `task` tool),
/// as one list for the `/tasks` monitor, the footer's running count and the
/// exit notes the next turn hears about. Files only, like the process
/// store: a subagent run is `<session>/agents/<id>.status.json`.
use std::io {IO.read_file, IO.write_file, IO.list_dir, IO.current_time_nano}
use std::path {Path, Path.to_string, Path.file_name}
use std::process {exec_cmd, process_id}
use std::list {List.filter, List.length, List.any}
use json::json {
    Json, Json.parse, Json.to_string, Json.make_object_pairs, Json.make_str, Json.make_num_int,
    Json.get_object, Json.get_str, Json.get_num, Json.get_num_i64, Json.object_get,
}
use std::map {BTreeMap}
use weaver::procs {ProcEntry, ProcStatus, ProcStatus.text, Procs.list}
use weaver::store {StoreState, Store.child}
use weaver::format {format_elapsed}
use weaver::text {Text.first_line}

pub type TaskKind {
    task_proc,
    task_agent,
}

/// One row of the monitor. `label` is the command or the subagent's
/// prompt; `status` its display word(s).
pub struct TaskEntry {
    kind : TaskKind,
    id : String,
    label : String,
    status : String,
    running : Bool,
    started_ns : I64,
    /// The process, for tail and kill; none for a subagent.
    proc : Option ProcEntry,
    /// A finished subagent's answer, first lines.
    summary : String,
}

// ── subagent runs ───────────────────────────────────────────────────────

def agents_dir (s : StoreState) : Path := Store.child s.dir "agents"

def status_path (s : StoreState) (id : String) : Path :=
    Store.child (agents_dir s) (String.concat id ".status.json")

/// A fresh subagent id: `a-<pid>-<ns>`.
pub def Tasks.agent_id : IO String := do {
    let now <- IO.current_time_nano;
    IO.pure (String.concat "a-" (String.concat (I64.to_string process_id) (String.concat "-" (I64.to_string now))))
}

def agent_json (prompt : String) (status : String) (started : I64) (summary : String) : String :=
    Json.to_string (Json.make_object_pairs
        [Pair.pair "prompt" (Json.make_str prompt), Pair.pair "status" (Json.make_str status),
            Pair.pair "started_ns" (Json.make_num_int started), Pair.pair "summary" (Json.make_str summary)])

/// Record a subagent run's state; without a store there is nothing to keep.
pub def Tasks.record_agent (store : Option StoreState) (id : String) (prompt : String) (status : String) (started : I64) (summary : String) : IO Unit :=
    match store {
        Option.none => IO.pure unit,
        Option.some s => do {
            let _ <- exec_cmd "mkdir" ["-p", Path.to_string (agents_dir s)];
            let _ <- IO.write_file (status_path s id) (agent_json prompt status started summary);
            IO.pure unit
        },
    }

def str_of (obj : BTreeMap String Json) (key : String) : String :=
    match Json.object_get key obj {
        Option.some j => match Json.get_str j { Result.ok s => s, Result.err _ => "" },
        Option.none => "",
    }

def ns_of (obj : BTreeMap String Json) : I64 :=
    match Json.object_get "started_ns" obj {
        Option.some j => match Json.get_num_i64 (Json.get_num j) { Result.ok n => n, Result.err _ => 0 },
        Option.none => 0,
    }

pub def Tasks.agent_of_json (id : String) (text : String) : Option TaskEntry :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match Json.get_object j {
            Result.err _ => Option.none,
            Result.ok obj =>
                let status : String := str_of obj "status" in
                let e : TaskEntry := { kind := TaskKind.task_agent, id := id, label := Text.first_line (str_of obj "prompt"),
                    status := status, running := String.beq status "running", started_ns := ns_of obj,
                    proc := Option.none, summary := str_of obj "summary" } in
                Option.some e,
        },
    }

def agent_entry (path : Path) : IO (Option TaskEntry) := do {
    let name : String := Path.file_name path;
    let suffix : String := ".status.json";
    if Bool.not (String.ends_with name suffix) then IO.pure Option.none
    else do {
        let r <- IO.read_file path;
        match r {
            Result.err _ => IO.pure Option.none,
            Result.ok text => IO.pure (Tasks.agent_of_json (String.slice name 0 (String.length name - String.length suffix)) text),
        }
    }
}

#[partial]
def agent_entries (paths : List Path) (acc : List TaskEntry) : IO (List TaskEntry) :=
    match paths {
        List.empty => IO.pure acc,
        List.cons p rest => do {
            let one <- agent_entry p;
            match one {
                Option.none => agent_entries rest acc,
                Option.some e => agent_entries rest (List.cons e acc),
            }
        },
    }

def agents (store : Option StoreState) : IO (List TaskEntry) :=
    match store {
        Option.none => IO.pure List.empty,
        Option.some s => do {
            let paths <- IO.list_dir (agents_dir s);
            agent_entries paths List.empty
        },
    }

// ── the list ────────────────────────────────────────────────────────────

pub def Tasks.of_proc (e : ProcEntry) : TaskEntry :=
    let running : Bool := match e.status { ProcStatus.running => true, _ => false } in
    let t : TaskEntry := { kind := TaskKind.task_proc, id := e.id, label := e.command, status := ProcStatus.text e.status,
        running := running, started_ns := e.started_ns, proc := Option.some e, summary := "" } in
    t

/// Every task, newest first.
pub def Tasks.list (store : Option StoreState) : IO (List TaskEntry) := do {
    let ps <- Procs.list;
    let ags <- agents store;
    IO.pure (Tasks.sort (List.append (List.map Tasks.of_proc ps) ags))
}

#[partial]
pub def Tasks.sort (xs : List TaskEntry) : List TaskEntry :=
    match xs {
        List.empty => xs,
        List.cons x rest => insert_newest x (Tasks.sort rest),
    }

#[partial]
def insert_newest (x : TaskEntry) (xs : List TaskEntry) : List TaskEntry :=
    match xs {
        List.empty => [x],
        List.cons y ys => if I64.lt y.started_ns x.started_ns then List.cons x xs else List.cons y (insert_newest x ys),
    }

pub def Tasks.running_count (ts : List TaskEntry) : I64 :=
    List.length (List.filter (fn (t : TaskEntry) => t.running) ts)

/// `● running  3.4s  echo hi` (`○` once it ended).
pub def Tasks.line (now_ns : I64) (t : TaskEntry) : String :=
    let mark : String := if t.running then "● " else "○ " in
    let kind : String := match t.kind { TaskKind.task_proc => "", TaskKind.task_agent => "agent: " } in
    String.concat mark (String.concat t.status (String.concat "  "
        (String.concat (format_elapsed ((now_ns - t.started_ns) / 100000000))
            (String.concat "  " (String.concat kind t.label)))))

// ── exit notes ──────────────────────────────────────────────────────────

/// The ids running at one poll: the next poll's notes compare against it.
pub def Tasks.running_ids (ts : List TaskEntry) : List String :=
    List.map (fn (t : TaskEntry) => t.id) (List.filter (fn (t : TaskEntry) => t.running) ts)

/// A note for each background process that was running and no longer is:
/// `[background task p-… exited (0): make test]`. Subagents end inside
/// their own tool call, so the model already has their result.
pub def Tasks.exit_notes (before : List String) (now : List TaskEntry) : List String :=
    List.map (fn (t : TaskEntry) => String.concat "[background task " (String.concat t.id
        (String.concat " " (String.concat t.status (String.concat ": " (String.concat t.label "]"))))))
        (Tasks.exited before now)

/// The background processes that were running at the last poll and are not now.
pub def Tasks.exited (before : List String) (now : List TaskEntry) : List TaskEntry :=
    List.filter (fn (t : TaskEntry) =>
        Bool.and (Bool.not t.running)
            (Bool.and (is_proc t) (List.any (fn (id : String) => String.beq id t.id) before))) now

def is_proc (t : TaskEntry) : Bool :=
    match t.kind { TaskKind.task_proc => true, TaskKind.task_agent => false }
