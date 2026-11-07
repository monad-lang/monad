/// Background-process tests: the detached script's quoting, a real
/// process that exits, and one that is killed. Temp roots are
/// PID-qualified (a fixed /tmp name collides across runs), and every test
/// removes what it creates.
use weaver::procs {
    ProcEntry, ProcStatus, Procs.detached_script, Procs.start_at, Procs.start_foreground, Procs.release, Procs.discard, Procs.shutdown_at,
    Procs.scan_at, Procs.tail, Procs.kill, Procs.entry_at, Procs.log_start, Procs.log_kill, Procs.log_exit,
}
use log::logger {Logger}
use log::level {LogLevel}
use weaver::process_tools {read_at, wait_of}
use shuttle::message_types {Content}
use json::json {Json, Json.parse}
use std::path {Path, Path.to_string}
use std::process {process_id, exec_cmd, Proc.kill_group}
use tui::terminal {Terminal.poll}
use std::io {IO.read_file, IO.is_dir, IO.current_time_nano}
use std::concurrent::combine {sleepIO}

def temp_root (suffix : String) : String :=
    String.concat "/tmp/weaver_procs_test_"
        (String.concat (I64.to_string process_id) (String.concat "_" suffix))

def cleanup (root : String) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", root];
    IO.pure unit
}

def is_exited0 (s : ProcStatus) : Bool :=
    match s {
        ProcStatus.exited code => code == 0,
        _ => false,
    }

def is_running (s : ProcStatus) : Bool :=
    match s {
        ProcStatus.running => true,
        _ => false,
    }

def is_killed (s : ProcStatus) : Bool :=
    match s {
        ProcStatus.killed => true,
        _ => false,
    }

#[partial]
def find_entry (id : String) (xs : List ProcEntry) : Option ProcEntry :=
    match xs {
        List.empty => Option.none,
        List.cons e rest => if e.id == id then Option.some e else find_entry id rest,
    }

def is_some (o : Option ProcEntry) : Bool :=
    match o { Option.some _ => true, Option.none => false }

#[test]
def test_detached_script_quotes_and_detaches : Bool :=
    let script : String := Procs.detached_script (Path.path "/tmp/r/p-1") "" "echo hi" in
    String.contains script "'/tmp/r/p-1/log'"
        && String.contains script "'/tmp/r/p-1/pid'"
        && String.contains script "'/tmp/r/p-1/exit'"
        && String.contains script "2>&1 < /dev/null"
        && String.contains script "& echo $!"
        && String.starts_with "set -m; " script

def after_or (id : String) (xs : List ProcEntry) (fallback : ProcEntry) : IO ProcEntry :=
    IO.pure (match find_entry id xs { Option.some x => x, Option.none => fallback })

def exit_case (root : String) (e : ProcEntry) : IO Bool := do {
    let _ <- Terminal.poll 400;
    let entries <- Procs.scan_at (Path.path root);
    let after <- after_or e.id entries e;
    let lines <- Procs.tail after 5;
    let text : String := String.concat_list lines;
    let _ <- cleanup root;
    IO.pure (is_exited0 after.status && String.contains text "one" && String.contains text "two")
}

#[test]
def test_started_process_exits_and_keeps_its_log : IO Bool := do {
    let root : String := temp_root "exit";
    let _ <- cleanup root;
    let r <- Procs.start_at (Path.path root) "echo one; echo two" "" false;
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => exit_case root e,
    }
}

def sleep_case (root : String) (e : ProcEntry) : IO Bool := do {
    let _ <- Terminal.poll 200;
    let entries <- Procs.scan_at (Path.path root);
    let running : Bool := match find_entry e.id entries {
        Option.some x => is_running x.status,
        Option.none => false,
    };
    let killed <- Procs.kill e;
    let _ <- Terminal.poll 300;
    let entries2 <- Procs.scan_at (Path.path root);
    let dead : Bool := match find_entry e.id entries2 {
        Option.some x => is_killed x.status,
        Option.none => false,
    };
    let _ <- cleanup root;
    IO.pure (running && (match killed { Result.ok _ => true, Result.err _ => false }) && dead)
}

#[test]
def test_a_sleep_is_running_then_killed : IO Bool := do {
    let root : String := temp_root "sleep";
    let _ <- cleanup root;
    let r <- Procs.start_at (Path.path root) "sleep 30" "" false;
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => sleep_case root e,
    }
}

/// The kill reaches the task's children: its process group goes, not
/// only the shell that started it.
def group_case (root : String) (e : ProcEntry) : IO Bool := do {
    let _ <- sleepIO 300;
    let child_text <- IO.read_file (Path.path (String.concat root "/child"));
    let child : String := match child_text { Result.ok t => String.trim t, Result.err _ => "" };
    let before <- IO.is_dir (Path.path (String.concat "/proc/" child));
    let _ <- Procs.kill e;
    let _ <- sleepIO 300;
    let after <- IO.is_dir (Path.path (String.concat "/proc/" child));
    let _ <- cleanup root;
    IO.pure (Bool.not (String.is_empty child) && before && Bool.not after)
}

#[test]
def test_kill_takes_the_task_s_children : IO Bool := do {
    let root : String := temp_root "group";
    let _ <- cleanup root;
    let _ <- exec_cmd "mkdir" ["-p", root];
    let r <- Procs.start_at (Path.path root) (String.concat "sleep 31 & echo $! > " (String.concat root "/child; wait")) "" false;
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => group_case root e,
    }
}

// ── read_process: one entry, and waiting ────────────────────────────────

def content_text (c : Content) : String :=
    match c {
        Content.tool_result _ out _ => out,
        _ => "",
    }

def wait_case (root : String) (e : ProcEntry) : IO Bool := do {
    let c <- read_at (Path.path root) "call-1" e.id 10 (fn (_ : Unit) => IO.pure false);
    let out : String := content_text c;
    cleanup root;
    return (String.contains out "exited (0)" && String.contains out "done")
}

def wait_started (root : String) (r : Result String ProcEntry) : IO Bool :=
    match r {
        Result.err _ => do { cleanup root; return false },
        Result.ok e => wait_case root e,
    }

/// One `read_process` with `wait_seconds` returns the finished task: no
/// model call per poll.
#[test]
def test_read_process_waits_for_the_exit : IO Bool := do {
    let root : String := temp_root "wait";
    let started <- Procs.start_at (Path.path root) "sleep 1; echo done" "" false;
    wait_started root started
}

/// The id comes from the model: a path is never looked up.
#[test]
def test_entry_at_rejects_a_path_id : IO Bool := do {
    let got <- Procs.entry_at (Path.path "/tmp") "../etc";
    return (match got { Option.none => true, Option.some _ => false })
}

def wait_in (text : String) : I64 :=
    match Json.parse text {
        Result.ok j => wait_of j,
        Result.err _ => 0 - 1,
    }

#[test]
def test_wait_seconds_parses_and_clamps : Bool :=
    wait_in "{\"id\": \"p-1\", \"wait_seconds\": 600}" == 60
        && wait_in "{\"id\": \"p-1\", \"wait_seconds\": \"5\"}" == 5
        && wait_in "{\"id\": \"p-1\"}" == 0
        && wait_in "{\"id\": \"p-1\", \"wait_seconds\": -3}" == 0

// ── debug-log events ────────────────────────────────────────────────────

def logged_entry : ProcEntry :=
    let e : ProcEntry := { id := "p-7", pid := 4242, command := "make\ttest", cwd := "", started_ns := 0,
        status := ProcStatus.running, log := Path.path "/tmp/x", dir := Path.path "/tmp" } in
    e

#[test]
def test_proc_events_reach_the_log : IO Bool := do {
    let root : String := temp_root "events";
    let _ <- cleanup root;
    let _ <- exec_cmd "mkdir" ["-p", root];
    let path : String := String.concat root "/run.log";
    let log : Option Logger := Option.some (Logger.file LogLevel.info path);
    let _ <- Procs.log_start log logged_entry;
    let _ <- Procs.log_kill log "user" logged_entry (Result.ok "killed p-7");
    let _ <- Procs.log_exit log "p-7" "exited (0)";
    let r <- IO.read_file (Path.path path);
    let _ <- cleanup root;
    let text : String := match r { Result.ok t => t, Result.err _ => "" };
    IO.pure (String.contains text "ev=proc_start id=p-7 child=4242 cmd=make"
        && String.contains text "ev=proc_kill id=p-7 by=user ok=true"
        && String.contains text "ev=proc_exit id=p-7 status=exited (0)")
}

/// A foreground task hides from scans until released; `entry_at` finds it
/// by id either way, and `discard` removes it.
def foreground_case (root : String) (e : ProcEntry) : IO Bool := do {
    let hidden <- Procs.scan_at (Path.path root);
    let by_id <- Procs.entry_at (Path.path root) e.id;
    Procs.release e;
    let shown <- Procs.scan_at (Path.path root);
    let _ <- Procs.kill e;
    Procs.discard e;
    let gone <- IO.is_dir e.dir;
    let _ <- cleanup root;
    IO.pure (List.is_empty hidden && is_some by_id
        && is_some (find_entry e.id shown) && Bool.not gone)
}

#[test]
def test_a_foreground_task_is_hidden_until_released : IO Bool := do {
    let root : String := temp_root "fg";
    let _ <- cleanup root;
    let r <- Procs.start_foreground (Path.path root) "sleep 30" "";
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => foreground_case root e,
    }
}

/// Shutdown reaches a foreground task too: killed, and its dir removed.
def shutdown_case (root : String) (e : ProcEntry) : IO Bool := do {
    Procs.shutdown_at (Path.path root);
    let gone <- IO.is_dir e.dir;
    let alive <- Proc.kill_group e.pid 0;
    let _ <- cleanup root;
    IO.pure (Bool.not gone && Bool.not alive)
}

#[test]
def test_shutdown_kills_a_foreground_task : IO Bool := do {
    let root : String := temp_root "fgdown";
    let _ <- cleanup root;
    let r <- Procs.start_foreground (Path.path root) "sleep 30" "";
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => shutdown_case root e,
    }
}

def stopped_case (root : String) (e : ProcEntry) : IO Bool := do {
    let t0 <- IO.current_time_nano;
    let c <- read_at (Path.path root) "call-2" e.id 30 (fn (_ : Unit) => IO.pure true);
    let t1 <- IO.current_time_nano;
    let out : String := content_text c;
    let _ <- Procs.kill e;
    cleanup root;
    return (t1 - t0 < 1000000000 && String.contains out "running"
        && String.contains out "[wait interrupted by the user; the task is still running]")
}

def stopped_started (root : String) (r : Result String ProcEntry) : IO Bool :=
    match r {
        Result.err _ => do { cleanup root; return false },
        Result.ok e => stopped_case root e,
    }

/// Esc ends a `read_process` wait at once; the task keeps running.
#[test]
def test_read_process_wait_ends_on_stop : IO Bool := do {
    let root : String := temp_root "wait-stop";
    let started <- Procs.start_at (Path.path root) "sleep 30" "" false;
    stopped_started root started
}
