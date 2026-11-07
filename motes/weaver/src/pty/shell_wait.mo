// weaver / pty / shell_wait -- a `shell` call the turn waits on: the live
// row shows the command's last output line and names Ctrl+B; Esc ends the
// turn at once and kills the command; Ctrl+B ends the wait, the command
// stays a running background task, and quitting weaver stops it.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args, quit_cleanly}
use weaver::pty_fixtures {write_shell_wait_script}
use std::process {exec_cmd}
use std::io {IO.println, IO.current_time_nano, IO.list_dir}
use std::path {Path}
use std::list {List.all}
use weaver::procs {ProcEntry, ProcStatus, Procs.scan_at}
use std::concurrent::combine {sleepIO}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

/// The task store's entries, read the way weaver reads them (a liveness
/// probe on the recorded pid, not the host's process table).
def tasks_of (root : String) : IO (List ProcEntry) :=
    Procs.scan_at (Path.path (String.concat root "/procs"))

def one_running (es : List ProcEntry) : Bool :=
    match es {
        List.cons e rest => Bool.and (List.is_empty rest) (match e.status { ProcStatus.running => true, _ => false }),
        List.empty => false,
    }

def none_running (es : List ProcEntry) : Bool :=
    List.all (fn (e : ProcEntry) => match e.status { ProcStatus.running => false, _ => true }) es

/// Poll until no task in the store is running.
#[partial]
def wait_none_running (root : String) (left_ms : I64) : IO Bool := do {
    let es <- tasks_of root;
    if none_running es then IO.pure true
    else if left_ms < 1 then IO.pure false
    else do {
        sleepIO 200;
        wait_none_running root (left_ms - 200)
    }
}

/// An interrupted foreground task is killed, then its directory removed.
def store_empty (root : String) : IO Bool := do {
    let dirs <- IO.list_dir (Path.path (String.concat root "/procs"));
    IO.pure (List.is_empty dirs)
}

/// Submit, approve the `shell` pick, and wait for the live row.
def start_waiting (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m (fn (o : Output) => grid_has o "type a message") 6000;
    Pty.send_text m "go\n";
    let asked <- Pty.wait_until m (fn (o : Output) => grid_has o "Permission required") 6000;
    Pty.send_text m "y";
    let waiting <- Pty.wait_until m (fn (o : Output) => grid_has o "Ctrl+B background") 6000;
    IO.pure (ready && asked && waiting)
}

// ── Esc ─────────────────────────────────────────────────────────────────

def esc_go (m : Pty) (root : String) : IO Bool := do {
    let up <- start_waiting m;
    let a <- Check.report "the live row names Ctrl+B while the command runs" up;
    let t0 <- IO.current_time_nano;
    Pty.send_text m "\u{1b}";
    let stopped <- Pty.wait_until m (fn (o : Output) => tight_has o "[stopped]") 6000;
    let t1 <- IO.current_time_nano;
    let b <- Check.report "Esc ends the waiting turn within 3 s" (stopped && t1 - t0 < 3000000000);
    let o <- Pty.output m;
    let c <- Check.report "the result says the command was interrupted" (tight_has o "interruptedbytheuser");
    let gone <- store_empty root;
    let d <- Check.report "the command is killed and its task removed" gone;
    let ended <- quit_cleanly m 4000;
    let quit <- Check.report "weaver quits cleanly" ended;
    Pty.finish m;
    return (a && b && c && d && quit)
}

def esc_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_shell_esc.json";
    let wrote <- write_shell_wait_script turns "sleep 31";
    if Bool.not wrote then do {
        IO.println "FAIL pty shell esc: could not write the turn script";
        return false
    } else do {
        let r <- spawn_args bin "mock" List.empty 24 100 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty shell esc spawn: " e); return false },
            Result.ok m => esc_go m root
        }
    }
}

pub def run_shell_wait_esc : IO Bool :=
    run_gated "pty weaver shell esc" (fn (bin : String) => with_root "shell_esc" (fn (root : String) => esc_run bin root))

// ── Ctrl+B ──────────────────────────────────────────────────────────────

/// The result is in the session's saved history (on screen it wraps
/// inside the transcript frame); the turn's block lands just after its
/// text shows, so poll for it.
#[partial]
def history_has (root : String) (needle : String) (left_ms : I64) : IO Bool := do {
    let rc <- exec_cmd "grep" ["-rqsF", needle, String.concat root "/sessions", "--exclude-dir=transcript"];
    if rc == 0 then IO.pure true
    else if left_ms < 1 then IO.pure false
    else do {
        sleepIO 200;
        history_has root needle (left_ms - 200)
    }
}

def ctrl_b_go (m : Pty) (root : String) : IO Bool := do {
    let up <- start_waiting m;
    let line <- Pty.wait_until m (fn (o : Output) => grid_has o "⎿ tick-2") 6000;
    let a <- Check.report "the live row shows the command's last output line" (up && line);
    Pty.send_text m "\u{2}";
    let done <- Pty.wait_until m (fn (o : Output) => tight_has o "donewaiting") 6000;
    let released <- history_has root "moved to the background by the user" 4000;
    let b <- Check.report "Ctrl+B ends the wait and the turn finishes" (released && done);
    let es <- tasks_of root;
    let c <- Check.report "the command keeps running as a background task" (one_running es);
    // A waited-on task is hidden from the task list; the footer counts it
    // once it is released.
    let listed <- Pty.wait_until m (fn (o : Output) => grid_has o "1 task running") 4000;
    let d <- Check.report "the footer counts it as a background task" listed;
    let ended <- quit_cleanly m 4000;
    let quit <- Check.report "weaver quits cleanly" ended;
    Pty.finish m;
    let stopped <- wait_none_running root 3000;
    let e <- Check.report "quitting weaver stops it" stopped;
    return (a && b && c && d && quit && e)
}

def ctrl_b_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_shell_ctrl_b.json";
    let wrote <- write_shell_wait_script turns "echo tick-1; sleep 1; echo tick-2; sleep 32";
    if Bool.not wrote then do {
        IO.println "FAIL pty shell ctrl-b: could not write the turn script";
        return false
    } else do {
        let r <- spawn_args bin "mock" List.empty 24 100 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty shell ctrl-b spawn: " e); return false },
            Result.ok m => ctrl_b_go m root
        }
    }
}

pub def run_shell_wait_ctrl_b : IO Bool :=
    run_gated "pty weaver shell ctrl-b" (fn (bin : String) => with_root "shell_ctrl_b" (fn (root : String) => ctrl_b_run bin root))
