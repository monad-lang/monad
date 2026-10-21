/// Background-process tests: the detached script's quoting, a real
/// process that exits, and one that is killed. Temp roots are
/// PID-qualified (a fixed /tmp name collides across runs), and every test
/// removes what it creates.
use weaver::procs {
    ProcEntry, ProcStatus, Procs.detached_script, Procs.start_at,
    Procs.scan_at, Procs.tail, Procs.kill,
}
use std::path {Path, Path.to_string}
use std::process {process_id, exec_cmd}
use tui::terminal {Terminal.poll}

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

#[test]
def test_detached_script_quotes_and_detaches : Bool :=
    let script : String := Procs.detached_script (Path.path "/tmp/r/p-1") "" "echo hi" in
    String.contains script "'/tmp/r/p-1/log'"
        && String.contains script "'/tmp/r/p-1/pid'"
        && String.contains script "'/tmp/r/p-1/exit'"
        && String.contains script "2>&1 < /dev/null"
        && String.contains script "& echo $!"

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
    let r <- Procs.start_at (Path.path root) "echo one; echo two" "";
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
    let r <- Procs.start_at (Path.path root) "sleep 30" "";
    match r {
        Result.err _ => do { let _ <- cleanup root; IO.pure false },
        Result.ok e => sleep_case root e,
    }
}
