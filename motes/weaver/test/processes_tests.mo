// mty / weaver / processes -- a start_process turn opens the approval overlay,
// `/processes` lists the running task with its command, and
// `/processes kill <id>` really stops the pid. Ported from
// pty_repro_processes.py (retired).
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {
    run_gated, with_root, spawn_args, wait_proc_entries,
    wait_pid_gone, kill_pid_9
}
use weaver::mty_fixtures {write_process_script}
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

def task_checks (m : Mty) (e : ProcEntry) : IO Bool := do {
    let id := e.id;
    let pid := e.pid;
    let command := e.command;
    Mty.send_text m "/processes\r";
    let listed <- Mty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "running") (grid_has o id)) 4000;
    let a <- Check.report "the snapshot lists the running task" listed;
    let with_cmd <- Mty.wait_until m (fn (o : Output) => grid_has o command) 2000;
    let b <- Check.report "the snapshot carries the command" with_cmd;
    Mty.send_text m (String.concat "/processes kill " (String.concat id "\r"));
    let killed <- Mty.wait_until m (fn (o : Output) => has_tight o "killed") 4000;
    let c <- Check.report "kill reports the kill" killed;
    let gone <- wait_pid_gone pid 6000;
    let d <- Check.report "the killed task's pid is gone" gone;
    Mty.finish m;
    let still <- Mty.pid_alive pid;
    let _ <- (match still { true => kill_pid_9 pid, false => IO.pure unit });
    return (Bool.and a (Bool.and b (Bool.and c d)))
}

def process_go (m : Mty) (root : String) : IO Bool := do {
    let ready <- Mty.wait_until m placeholder_seen 6000;
    Mty.send_text m "go\n";
    let overlay <- Mty.wait_until m (fn (o : Output) => has_stripped o "Permission required") 6000;
    let a <- Check.report "the start_process approval dialog appears" (Bool.and ready overlay);
    Mty.send_text m "y";
    let done <- Mty.wait_until m started 8000;
    let b <- Check.report "the turn continues after starting" done;
    let procs := String.concat root "/procs";
    let es <- wait_proc_entries procs 5000;
    match es {
        List.empty => do {
            let c <- Check.report "the task directory appears" false;
            Mty.finish m;
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
        IO.println "FAIL mty processes: could not write the turn script";
        return false
    } else do {
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL mty processes spawn: " e); return false },
            Result.ok m => process_go m root
        }
    }
}

#[test]
def test_start_process_list_and_kill : IO Bool :=
    run_gated "mty weaver processes" test_processes_body

def test_processes_body (bin : String) : IO Bool :=
    with_root "processes" (fn (root : String) => processes_run bin root)
