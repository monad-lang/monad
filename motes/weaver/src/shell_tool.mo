/// weaver's `shell`: every command is a task in the task store
/// (`procs.mo`), and the call's wait is a BUDGET, not a deadline.
///
/// The command runs detached in its own process group, its merged output
/// going to the task's log, and the call polls for the exit file. Because
/// nothing blocks on a pipe, every tick can also look at:
///
/// - the turn's stop request (Esc): kill the group, report what ran;
/// - a `background` marker in the task dir (Ctrl+B): stop waiting now;
/// - the budget (`wait_seconds`, default 30): stop waiting, NOT kill.
///
/// A command that outlives its wait is released into an ordinary background
/// task: the model gets the output so far and the id, and the exit arrives
/// later as an inbox note, like any task's. `wait_seconds: 0` starts a task
/// without waiting at all.
///
/// A command that finishes in time is discarded from the store after its
/// output is read. The log is capped at 64 MiB; past that the group is
/// killed, since a runaway writer would otherwise fill the disk.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {Json, Json.get_object, Json.object_get, Json.get_str}
use std::io {IO.current_time_nano, IO.file_exists, IO.file_size, IO.write_file}
use std::path {Path, Path.to_string}
use std::process {process_id, exec_cmd, Proc.capture, Proc.shell_quote}
use std::concurrent::combine {sleepIO}
use init::transformers {ResultT}
use log::logger {Logger}
use weaver::procs {
    ProcEntry, ProcStatus, Procs.root, Procs.start_at, Procs.start_foreground, Procs.release,
    Procs.discard, Procs.kill, Procs.status_of, Procs.log_start, Procs.log_detach,
}
use weaver::process_tools {str_param, int_param, object_schema, int_arg}
use weaver::store {StoreState, Store.child}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

/// The default and the longest wait, in seconds.
pub def WeaverShell.default_wait : I64 := 30
pub def WeaverShell.max_wait : I64 := 300

/// The log size past which a running command is killed.
pub def WeaverShell.max_log_bytes : I64 := 67108864

/// What the tool shows of the output: the last lines within both caps.
def shown_lines : I64 := 200
def shown_bytes : I64 := 65536

/// The longest sleep between ticks; the first is 10 ms and each doubles.
def max_tick_ms : I64 := 200

/// The file naming the task dir the turn is waiting on, which the UI reads
/// for Ctrl+B and the live output line; it exists only during a wait.
/// Session-scoped like `stop.txt`.
pub def WeaverShell.fg_path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "foreground.txt",
        Option.none =>
            Path.path (String.concat "/tmp/weaver-fg-"
                (String.concat (I64.to_string process_id) ".txt")),
    }

/// The tool's environment. `root` is the task store; `budget_ms`
/// overrides the model's `wait_seconds` (tests pass a short one; 0 means
/// use the argument).
pub struct ShellEnv {
    root : Path,
    fg : Path,
    stop : Unit -> IO Bool,
    log : Option Logger,
    budget_ms : I64,
}

pub def WeaverShell.never_stop : Unit -> IO Bool := fn (_ : Unit) => IO.pure false

def shell_params : List (Pair String Json) :=
    [str_param "command" "Shell command to run. stdout and stderr are merged.",
        int_param "wait_seconds" "How long to wait for it, 0-300 (default 30). A command still running then keeps running as a background task; you get its output so far and a task id, and a note when it exits. 0 starts it in the background without waiting."]

pub def WeaverShell.spec : ToolSpec :=
    { name := "shell",
        description := "Run a shell command as a task and return its output. Long commands are not killed: past the wait they continue in the background (see wait_seconds). Use read_process / kill_process / list_processes for background tasks.",
        schema := object_schema shell_params ["command"] }

/// The tool against the real task store.
pub def WeaverShell.impl (log : Option Logger) (stop : Unit -> IO Bool) (fg : Path) : ToolImpl :=
    { spec := WeaverShell.spec, cap := Capability.exec, run := shell_run log stop fg }

def shell_run (log : Option Logger) (stop : Unit -> IO Bool) (fg : Path) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let root <- Procs.root;
        let env : ShellEnv := { root := root, fg := fg, stop := stop, log := log, budget_ms := 0 };
        let c <- WeaverShell.run env id j;
        IO.pure (Result.ok c)
    })

def command_of (j : Json) : Option String :=
    match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => match Json.object_get "command" o {
            Option.none => Option.none,
            Option.some c => match Json.get_str c {
                Result.ok s => if String.is_empty (String.trim s) then Option.none else Option.some s,
                Result.err _ => Option.none,
            },
        },
    }

/// The tool's whole run, with an explicit environment (the tests' entry).
pub def WeaverShell.run (env : ShellEnv) (id : String) (j : Json) : IO Content :=
    match command_of j {
        Option.none => IO.pure (tool_err id "shell: `command` must be a non-empty string"),
        Option.some command =>
            let secs : I64 := int_arg "wait_seconds" WeaverShell.default_wait WeaverShell.max_wait j in
            let ms : I64 := if env.budget_ms > 0 then env.budget_ms else secs * 1000 in
            if secs == 0 then start_detached env id command else start_waiting env id command ms,
    }

// ── starting ────────────────────────────────────────────────────────────

def start_detached (env : ShellEnv) (id : String) (command : String) : IO Content := do {
    let r <- Procs.start_at env.root command "" false;
    match r {
        Result.err e => IO.pure (tool_err id (String.concat "shell: " e)),
        Result.ok e => started env id e,
    }
}

def started (env : ShellEnv) (id : String) (e : ProcEntry) : IO Content := do {
    let _ <- Procs.log_start env.log e;
    IO.pure (tool_ok id (String.concat "started in the background: " (task_ref e)))
}

/// `task p-… (pid …); log: …` plus how to manage it.
def task_ref (e : ProcEntry) : String :=
    String.concat_list ["task ", e.id, " (pid ", I64.to_string e.pid, ")\nlog: ", Path.to_string e.log,
        "\nYou get a note when it exits; read_process shows its output, kill_process stops it."]

def start_waiting (env : ShellEnv) (id : String) (command : String) (ms : I64) : IO Content := do {
    let r <- Procs.start_foreground env.root command "";
    match r {
        Result.err e => IO.pure (tool_err id (String.concat "shell: " e)),
        Result.ok e => waiting env id e ms,
    }
}

def waiting (env : ShellEnv) (id : String) (e : ProcEntry) (ms : I64) : IO Content := do {
    let _ <- Procs.log_start env.log e;
    let _ <- IO.write_file env.fg (Path.to_string e.dir);
    let now <- IO.current_time_nano;
    let outcome <- wait_loop env e (now + ms * 1000000) 10 now;
    let _ <- exec_cmd "rm" ["-f", Path.to_string env.fg];
    finish env id e ms outcome
}

// ── the wait ────────────────────────────────────────────────────────────

/// One tick's verdict.
pub type ShellTick {
    pending,
    done,
    interrupted,
    detached_by_user,
    detached_by_budget,
    flooded,
}

/// Sleep, look, and either go round again (doubling the sleep up to
/// `max_tick_ms`) or return the verdict. `sized_ns` is when the log size
/// was last checked; it is checked about once a second.
#[partial]
def wait_loop (env : ShellEnv) (e : ProcEntry) (deadline_ns : I64) (delay : I64) (sized_ns : I64) : IO ShellTick := do {
    sleepIO delay;
    let now <- IO.current_time_nano;
    let size_due : Bool := now - sized_ns > 1000000000;
    let t <- tick env e deadline_ns now size_due;
    match t {
        ShellTick.pending =>
            wait_loop env e deadline_ns (if delay * 2 > max_tick_ms then max_tick_ms else delay * 2)
                (if size_due then now else sized_ns),
        _ => IO.pure t,
    }
}

/// Checked in this order: an exit wins over a stop that arrived with it,
/// and a stop wins over a detach.
def tick (env : ShellEnv) (e : ProcEntry) (deadline_ns : I64) (now : I64) (size_due : Bool) : IO ShellTick := do {
    let done <- IO.file_exists (Store.child e.dir "exit");
    if done then IO.pure ShellTick.done else tick_stop env e deadline_ns now size_due
}

def tick_stop (env : ShellEnv) (e : ProcEntry) (deadline_ns : I64) (now : I64) (size_due : Bool) : IO ShellTick := do {
    let stop <- env.stop unit;
    if stop then IO.pure ShellTick.interrupted else tick_detach e deadline_ns now size_due
}

def tick_detach (e : ProcEntry) (deadline_ns : I64) (now : I64) (size_due : Bool) : IO ShellTick := do {
    let asked <- IO.file_exists (Store.child e.dir "background");
    if asked then IO.pure ShellTick.detached_by_user
    else if now > deadline_ns then IO.pure ShellTick.detached_by_budget
    else if size_due then tick_size e
    else IO.pure ShellTick.pending
}

def tick_size (e : ProcEntry) : IO ShellTick := do {
    let n <- IO.file_size e.log;
    IO.pure (match n {
        Option.some b => if b > WeaverShell.max_log_bytes then ShellTick.flooded else ShellTick.pending,
        Option.none => ShellTick.pending,
    })
}

// ── the outcome ─────────────────────────────────────────────────────────

def finish (env : ShellEnv) (id : String) (e : ProcEntry) (ms : I64) (t : ShellTick) : IO Content :=
    match t {
        ShellTick.done => finish_exited id e,
        ShellTick.interrupted => finish_killed id e "[interrupted by the user]\n",
        ShellTick.flooded => finish_killed id e "[output passed 64 MiB; command killed]\n",
        ShellTick.detached_by_user => finish_detached env id e "by the user",
        _ => finish_detached env id e (String.concat_list ["after ", I64.to_string (ms / 1000), "s"]),
    }

def finish_exited (id : String) (e : ProcEntry) : IO Content := do {
    let status <- settled_status e;
    let out <- WeaverShell.output e;
    Procs.discard e;
    IO.pure (match status {
        ProcStatus.exited code =>
            if code == 0 then tool_ok id out
            else tool_err id (String.concat out (String.concat_list ["[exit status ", I64.to_string code, "]\n"])),
        _ => tool_err id (String.concat out "[exit status unknown]\n"),
    })
}

/// The exit file appears before its content is flushed; one short retry
/// covers the gap.
def settled_status (e : ProcEntry) : IO ProcStatus := do {
    let s <- Procs.status_of e.dir e.pid;
    match s {
        ProcStatus.exited _ => IO.pure s,
        _ => settled_retry e,
    }
}

def settled_retry (e : ProcEntry) : IO ProcStatus := do {
    sleepIO 20;
    Procs.status_of e.dir e.pid
}

def finish_killed (id : String) (e : ProcEntry) (marker : String) : IO Content := do {
    let _ <- Procs.kill e;
    let out <- WeaverShell.output e;
    Procs.discard e;
    IO.pure (tool_err id (String.concat out marker))
}

def finish_detached (env : ShellEnv) (id : String) (e : ProcEntry) (why : String) : IO Content := do {
    Procs.release e;
    let _ <- Procs.log_detach env.log e why;
    let out <- WeaverShell.output e;
    IO.pure (tool_ok id (String.concat_list [out, "[still running; moved to the background ", why, " as ", task_ref e, "]\n"]))
}

// ── reading the log ─────────────────────────────────────────────────────

/// The log's tail within `shown_lines`/`shown_bytes`, led by a note when
/// earlier lines were left out. One capture: the newline count, then the
/// tail.
pub def WeaverShell.output (e : ProcEntry) : IO String := do {
    let log : String := Proc.shell_quote (Path.to_string e.log);
    let script : String := String.concat_list ["wc -l < ", log, "; tail -c ", I64.to_string shown_bytes, " ", log,
        " | tail -n ", I64.to_string shown_lines];
    let r <- Proc.capture "sh" ["-c", script];
    IO.pure (match r { Pair.pair _ out => WeaverShell.trim_output out })
}

/// Split `<count>\n<tail>` and add the omitted-lines note.
pub def WeaverShell.trim_output (captured : String) : String :=
    let cut : I64 := first_newline captured 0 in
    let total : I64 := digits (String.to_list (String.slice captured 0 cut)) 0 in
    let tail : String := String.drop (cut + 1) captured in
    let shown : I64 := newlines (String.to_list tail) 0 in
    let omitted : I64 := total - shown in
    if omitted > 0
    then String.concat_list ["[", I64.to_string omitted, " earlier lines omitted]\n", tail]
    else tail

#[partial]
def first_newline (s : String) (i : I64) : I64 :=
    if i + 1 > String.length s then i
    else if String.slice s i 1 == "\n" then i
    else first_newline s (i + 1)

#[partial]
def digits (bs : List U8) (acc : I64) : I64 :=
    match bs {
        List.empty => acc,
        List.cons b rest =>
            if Bool.and (U8.to_i64 b > 47) (U8.to_i64 b < 58)
            then digits rest (acc * 10 + U8.to_i64 b - 48)
            else digits rest acc,
    }

#[partial]
def newlines (bs : List U8) (acc : I64) : I64 :=
    match bs {
        List.empty => acc,
        List.cons b rest => newlines rest (if U8.beq b 10u8 then acc + 1 else acc),
    }
