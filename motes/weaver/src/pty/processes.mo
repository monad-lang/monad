// weaver / pty / processes -- a start_process turn opens the approval overlay;
// the footer counts the running task; `/tasks` lists it, Enter opens it and
// `x` really stops the pid; the kill and the exit note reach the transcript.
// Ported from pty_repro_processes.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {
    run_gated, with_root, spawn_args, wait_proc_entries,
    wait_pid_gone, kill_pid_9
}
use weaver::pty_fixtures {write_process_script}
use weaver::procs {ProcEntry}
use std::io {IO.println}

def has_tight (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def has_stripped (o : Output) (needle : String) : Bool :=
    String.contains (Output.stripped o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def placeholder_seen (o : Output) : Bool :=
    grid_has o "type a message"

def started (o : Output) : Bool :=
    has_tight o "startedit"

def task_checks (m : Pty) (e : ProcEntry) : IO Bool := do {
    let id := e.id;
    let pid := e.pid;
    let command := e.command;
    let counted <- Pty.wait_until m (fn (o : Output) => grid_has o "1 task running") 4000;
    let a <- Check.report "the footer counts the running task" counted;
    Pty.send_text m "/tasks\r";
    let listed <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "Tasks") (Bool.and (grid_has o "running") (grid_has o command))) 4000;
    let b <- Check.report "the monitor lists the running task with its command" listed;
    Pty.send_text m "\r";
    let detail <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o (String.concat "Task " id)) (grid_has o "Kill the process")) 4000;
    let c <- Check.report "Enter opens the task's detail" detail;
    Pty.send_text m "x";
    let gone <- wait_pid_gone pid 6000;
    let d <- Check.report "x kills the task's pid" gone;
    let shown <- Pty.wait_until m (fn (o : Output) => grid_has o "status: killed") 4000;
    let f <- Check.report "the detail shows it killed" shown;
    Pty.send_text m "\u{1b}";
    let _ <- Pty.wait_until m (fn (o : Output) => grid_has o "Enter opens a task") 3000;
    Pty.send_text m "\u{1b}";
    let noted <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o (String.concat "killed " id)) (grid_has o "[background task")) 6000;
    let g <- Check.report "the kill and the exit note reach the transcript" noted;
    Pty.finish m;
    let still <- Pty.pid_alive pid;
    let _ <- (match still { true => kill_pid_9 pid, false => IO.pure unit });
    return (a && b && c && d && f && g)
}

def process_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    Pty.send_text m "go\n";
    let overlay <- Pty.wait_until m (fn (o : Output) => has_stripped o "Permission required") 6000;
    let a <- Check.report "the start_process approval dialog appears" (Bool.and ready overlay);
    Pty.send_text m "y";
    let done <- Pty.wait_until m started 8000;
    let b <- Check.report "the turn continues after starting" done;
    let procs := String.concat root "/procs";
    let es <- wait_proc_entries procs 5000;
    match es {
        List.empty => do {
            let c <- Check.report "the task directory appears" false;
            Pty.finish m;
            return (Bool.and a (Bool.and b c))
        },
        List.cons e _ => do {
            let c <- task_checks m e;
            return (Bool.and a (Bool.and b c))
        }
    }
}

def processes_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_process.json";
    let wrote <- write_process_script turns "exec sleep 30";
    if Bool.not wrote then do {
        IO.println "FAIL pty processes: could not write the turn script";
        return false
    } else do {
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty processes spawn: " e); return false },
            Result.ok m => process_go m root
        }
    }
}

pub def run_start_process_list_and_kill : IO Bool :=
    run_gated "pty weaver processes" test_processes_body

def test_processes_body (bin : String) : IO Bool :=
    with_root "processes" (fn (root : String) => processes_run bin root)
