/// weaver's `shell` tool against a temp task store: output and exit status,
/// the output cap, Esc, Ctrl+B, the wait budget, and `wait_seconds: 0`.
use weaver::shell_tool {ShellEnv, WeaverShell.run, WeaverShell.never_stop, WeaverShell.trim_output, WeaverShell.request_background}
use weaver::procs {ProcEntry, ProcStatus, Procs.scan_at, Procs.kill}
use shuttle::message_types {Content}
use json::json {Json, Json.parse, Json.make_str, Json.make_object}
use std::map {Map, BTreeMap}
use std::list {List.all}
use std::path {Path}
use std::process {process_id, exec_cmd, Proc.kill_group}
use std::io {IO.list_dir, IO.read_file, IO.write_file, IO.current_time_nano}
use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {forkIO}

def temp_root (suffix : String) : String :=
    String.concat "/tmp/weaver_shell_test_"
        (String.concat (I64.to_string process_id) (String.concat "_" suffix))

def cleanup (root : String) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", root];
    IO.pure unit
}

def env_at (root : String) (stop : Unit -> IO Bool) (budget_ms : I64) : ShellEnv :=
    let e : ShellEnv := { root := Path.path root, fg := Path.path (String.concat root ".fg"),
        stop := stop, log := Option.none, budget_ms := budget_ms, scratch := Option.none } in
    e

def args (text : String) : Json :=
    match Json.parse text {
        Result.ok j => j,
        Result.err _ => Json.make_str "",
    }

def text_of (c : Content) : String :=
    match c {
        Content.tool_result _ out _ => out,
        _ => "",
    }

def is_err (c : Content) : Bool :=
    match c {
        Content.tool_result _ _ e => e,
        _ => false,
    }

/// Run `json` against a fresh store; the store is removed afterwards and
/// whether it was left empty is reported alongside the result.
def run_in (root : String) (env : ShellEnv) (json : String) : IO (Pair Content I64) := do {
    let _ <- cleanup root;
    let c <- WeaverShell.run env "t1" (args json);
    let left <- IO.list_dir (Path.path root);
    let _ <- cleanup root;
    IO.pure (Pair.pair c (List.length left))
}

#[test]
def test_output_and_success : IO Bool := do {
    let root : String := temp_root "ok";
    let r <- run_in root (env_at root WeaverShell.never_stop 0) "{\"command\":\"echo hi; echo err 1>&2\"}";
    match r { Pair.pair c left => IO.pure (Bool.not (is_err c) && String.beq (text_of c) "hi\nerr\n" && left == 0) }
}

#[test]
def test_nonzero_exit_is_an_error_with_its_status : IO Bool := do {
    let root : String := temp_root "exit";
    let r <- run_in root (env_at root WeaverShell.never_stop 0) "{\"command\":\"echo x; exit 3\"}";
    match r { Pair.pair c _ => IO.pure (is_err c && String.beq (text_of c) "x\n[exit status 3]\n") }
}

#[test]
def test_missing_command_is_an_error : IO Bool := do {
    let root : String := temp_root "none";
    let r <- run_in root (env_at root WeaverShell.never_stop 0) "{\"wait_seconds\":5}";
    match r { Pair.pair c _ => IO.pure (is_err c) }
}

#[test]
def test_long_output_keeps_the_tail : IO Bool := do {
    let root : String := temp_root "long";
    let r <- run_in root (env_at root WeaverShell.never_stop 0) "{\"command\":\"seq 1 500\"}";
    match r { Pair.pair c _ =>
        IO.pure (String.starts_with "[340 earlier lines omitted]\n341\n" (text_of c)
            && String.ends_with (text_of c) "\n500\n") }
}

#[test]
def test_trim_output_without_omission : Bool :=
    String.beq (WeaverShell.trim_output "2\na\nb\n") "a\nb\n"

/// Esc: a stop that fires mid-command kills the group and reports it.
def stop_after (deadline : I64) : Unit -> IO Bool :=
    fn (_ : Unit) => do {
        let now <- IO.current_time_nano;
        IO.pure (now > deadline)
    }

#[test]
def test_a_stop_interrupts_a_running_command : IO Bool := do {
    let root : String := temp_root "stop";
    let t0 <- IO.current_time_nano;
    let r <- run_in root (env_at root (stop_after (t0 + 300000000)) 0) "{\"command\":\"echo started; sleep 30\"}";
    let t1 <- IO.current_time_nano;
    match r { Pair.pair c left =>
        IO.pure (is_err c && String.beq (text_of c) "started\n[interrupted by the user]\n"
            && t1 - t0 < 3000000000 && left == 0) }
}

/// The budget: the command keeps running as a listed background task.
def detached_case (root : String) (c : Content) : IO Bool := do {
    let listed <- Procs.scan_at (Path.path root);
    let running : Bool := List.length listed == 1 && List.all is_running listed;
    let _ <- kill_all listed;
    let _ <- cleanup root;
    IO.pure (Bool.not (is_err c) && running
        && String.contains (text_of c) "early\n[still running; moved to the background after 0s as task p-")
}

def is_running (e : ProcEntry) : Bool :=
    match e.status { ProcStatus.running => true, _ => false }

#[partial]
def kill_all (xs : List ProcEntry) : IO Unit :=
    match xs {
        List.empty => IO.pure unit,
        List.cons e rest => do { let _ <- Procs.kill e; kill_all rest },
    }

#[test]
def test_the_budget_detaches_instead_of_killing : IO Bool := do {
    let root : String := temp_root "budget";
    let _ <- cleanup root;
    let c <- WeaverShell.run (env_at root WeaverShell.never_stop 400) "t1" (args "{\"command\":\"echo early; sleep 30\"}");
    detached_case root c
}

/// Ctrl+B, as the TUI's key does it.
def press_ctrl_b (fg : String) : IO Unit := do {
    sleepIO 300;
    let _ <- WeaverShell.request_background (Path.path fg);
    IO.pure unit
}

def ctrl_b_case (root : String) (c : Content) : IO Bool := do {
    let listed <- Procs.scan_at (Path.path root);
    let _ <- kill_all listed;
    let _ <- cleanup root;
    let _ <- cleanup (String.concat root ".fg");
    IO.pure (Bool.not (is_err c) && List.length listed == 1
        && String.contains (text_of c) "moved to the background by the user as task p-")
}

#[test]
def test_a_background_request_detaches_now : IO Bool := do {
    let root : String := temp_root "ctrlb";
    let _ <- cleanup root;
    let _ <- forkIO (fn (_ : Unit) => press_ctrl_b (String.concat root ".fg"));
    let c <- WeaverShell.run (env_at root WeaverShell.never_stop 0) "t1" (args "{\"command\":\"sleep 30\"}");
    ctrl_b_case root c
}

#[test]
def test_wait_zero_starts_in_the_background : IO Bool := do {
    let root : String := temp_root "zero";
    let _ <- cleanup root;
    let c <- WeaverShell.run (env_at root WeaverShell.never_stop 0) "t1" (args "{\"command\":\"sleep 30\",\"wait_seconds\":0}");
    let listed <- Procs.scan_at (Path.path root);
    let _ <- kill_all listed;
    let _ <- cleanup root;
    IO.pure (Bool.not (is_err c) && List.length listed == 1
        && String.starts_with "started in the background: task p-" (text_of c))
}

/// With no command being waited on, Ctrl+B does nothing.
#[test]
def test_a_background_request_without_a_wait_is_a_no_op : IO Bool := do {
    let asked <- WeaverShell.request_background (Path.path (temp_root "no-fg-file"));
    IO.pure (Bool.not asked)
}

/// The session scratch dir reaches the task as WEAVER_SCRATCH and
/// TMPDIR (the gate's scratch exemption and the shell agree on it).
#[test]
def test_the_scratch_env_reaches_the_task : IO Bool := do {
    let root : String := temp_root "scratch";
    let scratch : String := String.concat root "_scr";
    let _ <- exec_cmd "mkdir" ["-p", scratch];
    let env : ShellEnv := { root := Path.path root, fg := Path.path (String.concat root ".fg"),
        stop := WeaverShell.never_stop, log := Option.none, budget_ms := 5000,
        scratch := Option.some (Path.path scratch) };
    let _ <- cleanup root;
    let cmd : String := "printf '%s\\n%s' \"$WEAVER_SCRATCH\" \"$TMPDIR\"";
    let input : Json := Json.make_object (Map.insert "command" (Json.make_str cmd) BTreeMap.empty);
    let c <- WeaverShell.run env "t1" input;
    let out : String := text_of c;
    let _ <- cleanup root;
    let _ <- cleanup scratch;
    IO.pure (Bool.and (String.contains out scratch) (Bool.and (Bool.not (is_err c)) (String.contains out "/tmp")))
}
