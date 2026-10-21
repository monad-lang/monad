/// Background processes: a detached `sh -c` whose stdout+stderr go to a
/// per-process log, with pid/exit/killed marker files. Everything is
/// files, so there is no mutable registry (the language has no IORef) and
/// a crashed harness leaves a readable record.
///
/// A launched process is NOT a child group: `kill` targets the shell pid,
/// and a grandchild that detaches can survive. The foreground `shell`
/// tool is untouched.
use std::io {IO.get_env, IO.is_dir, IO.list_dir, IO.read_file, IO.write_file, IO.current_time_nano}
use std::path {Path, Path.to_string, Path.join, Path.file_name}
use std::process {exec_cmd, process_id, Proc.capture}
use json::json {
    Json, Json.parse, Json.to_string, Json.make_object, Json.make_str, Json.make_num_int,
    Json.get_object, Json.get_str, Json.get_num, Json.get_num_i64, Json.object_get,
}
use std::map {BTreeMap}
use parsec::number {parse_i64}
use weaver::store {Store.sessions_root, Store.child}
use weaver::format {format_elapsed}

pub type ProcStatus {
    running,
    exited (code : I64),
    killed,
    lost,
}

pub struct ProcEntry {
    id : String,
    pid : I64,
    command : String,
    cwd : String,
    started_ns : I64,
    status : ProcStatus,
    log : Path,
    dir : Path,
}

pub def ProcStatus.text (s : ProcStatus) : String :=
    match s {
        ProcStatus.running => "running",
        ProcStatus.exited code => String.concat "exited (" (String.concat (I64.to_string code) ")"),
        ProcStatus.killed => "killed",
        ProcStatus.lost => "lost",
    }

/// The monitor's one-line description: `running  3.4s  echo hi`.
pub def ProcEntry.line (e : ProcEntry) (now_ns : I64) : String :=
    let frames : I64 := (now_ns - e.started_ns) / 100000000 in
    String.concat (ProcStatus.text e.status)
        (String.concat "  " (String.concat (format_elapsed frames)
            (String.concat "  " e.command)))

// ── the run root ────────────────────────────────────────────────────────

def non_empty (s : String) : Option String :=
    if String.is_empty s then Option.none else Option.some s

/// `WEAVER_PROC_ROOT`, else `<sessions root>/procs/p-<weaver pid>`, else
/// `/tmp/weaver-procs/p-<pid>`. Session-independent, so /clear and
/// /resume do not orphan the monitor's view.
def root_default : IO Path := do {
    let sessions <- Store.sessions_root;
    let base : Path := match sessions {
        Option.some p => p,
        Option.none => Path.path "/tmp/weaver-procs",
    };
    let procs : Path := Path.join base (Path.path "procs");
    IO.pure (Path.join procs (Path.path (String.concat "p-" (I64.to_string process_id))))
}

def root_of (override : String) : IO Path :=
    match non_empty override {
        Option.some s => IO.pure (Path.path s),
        Option.none => root_default,
    }

pub def Procs.root : IO Path := do {
    let got <- IO.get_env "WEAVER_PROC_ROOT";
    let override : String := match got { Option.some s => s, Option.none => "" };
    root_of override
}

pub def Procs.ensure (root : Path) : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string root];
    IO.is_dir root
}

// ── files ───────────────────────────────────────────────────────────────

def read_opt (p : Path) : IO (Option String) := do {
    let r <- IO.read_file p;
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok s => IO.pure (Option.some s),
    }
}

def write_text (p : Path) (s : String) : IO Unit := do {
    let _ <- IO.write_file p s;
    IO.pure unit
}

def shell_quote (s : String) : String :=
    String.concat "'" (String.concat s "'")

def dir_child (e : ProcEntry) (name : String) : Path :=
    Store.child e.dir name

// ── meta.json ───────────────────────────────────────────────────────────

def meta_json (command : String) (cwd : String) (started_ns : I64) : String :=
    Json.to_string (Json.make_object
        (Map.insert "command" (Json.make_str command)
        (Map.insert "cwd" (Json.make_str cwd)
        (Map.insert "started_ns" (Json.make_num_int started_ns) BTreeMap.empty))))

def meta_str (obj : BTreeMap String Json) (name : String) : String :=
    match Json.object_get name obj {
        Option.some j => match Json.get_str j { Result.ok s => s, Result.err _ => "" },
        Option.none => "",
    }

def meta_ns (obj : BTreeMap String Json) : I64 :=
    match Json.object_get "started_ns" obj {
        Option.some j => match Json.get_num_i64 (Json.get_num j) { Result.ok n => n, Result.err _ => 0 },
        Option.none => 0,
    }

/// `(command, cwd, started_ns)` from a meta file, or none when missing /
/// unparsable.
pub def Procs.read_meta (p : Path) : IO (Option (Pair String (Pair String I64))) := do {
    let r <- read_opt p;
    match r {
        Option.none => IO.pure Option.none,
        Option.some s => match Json.parse s {
            Result.err _ => IO.pure Option.none,
            Result.ok j => match Json.get_object j {
                Result.err _ => IO.pure Option.none,
                Result.ok obj =>
                    let triple : Pair String (Pair String I64) :=
                        Pair.pair (meta_str obj "command") (Pair.pair (meta_str obj "cwd") (meta_ns obj)) in
                    IO.pure (Option.some triple),
            },
        },
    }
}

// ── status ──────────────────────────────────────────────────────────────

def is_running (pid : I64) : IO Bool := do {
    let code <- exec_cmd "sh" ["-c", String.concat "kill -0 " (I64.to_string pid)];
    IO.pure (I64.beq code 0)
}

def parse_or (text : String) (fallback : I64) : I64 :=
    match parse_i64 (String.trim text) {
        Option.some n => n,
        Option.none => fallback,
    }

def pid_of (dir : Path) : IO I64 := do {
    let r <- read_opt (Store.child dir "pid");
    match r {
        Option.none => IO.pure 0,
        Option.some s => IO.pure (parse_or s 0),
    }
}

def exit_status (text : Option String) : Option ProcStatus :=
    match text {
        Option.none => Option.none,
        Option.some t =>
            match parse_i64 (String.trim t) {
                Option.some code => Option.some (ProcStatus.exited code),
                Option.none => Option.some ProcStatus.lost,
            }
    }

def status_from_liveness (pid : I64) : IO ProcStatus :=
    if pid < 1
    then IO.pure ProcStatus.lost
    else do {
        let alive <- is_running pid;
        IO.pure (if alive then ProcStatus.running else ProcStatus.lost)
    }

def status_after_exit (dir : Path) (pid : I64) : IO ProcStatus := do {
    let killed <- read_opt (Store.child dir "killed");
    match killed {
        Option.some _ => IO.pure ProcStatus.killed,
        Option.none => status_from_liveness pid,
    }
}

pub def Procs.status_of (dir : Path) (pid : I64) : IO ProcStatus := do {
    let exit <- read_opt (Store.child dir "exit");
    match exit_status exit {
        Option.some s => IO.pure s,
        Option.none => status_after_exit dir pid,
    }
}

// ── scan / start / tail / kill ──────────────────────────────────────────

def mk_entry (d : Path) (pid_in : I64) (command_in : String) (cwd_in : String) (started_in : I64) (status_in : ProcStatus) : ProcEntry :=
    let id : String := Path.file_name d in
    let e : ProcEntry := { id := id, pid := pid_in, command := command_in, cwd := cwd_in,
      started_ns := started_in, status := status_in,
      log := Store.child d "log", dir := d } in
    e

def entry_of (d : Path) (command : String) (cwd : String) (started : I64) : IO ProcEntry := do {
    let pid <- pid_of d;
    let status <- Procs.status_of d pid;
    IO.pure (mk_entry d pid command cwd started status)
}

def some_entry (d : Path) (command : String) (cwd : String) (started : I64) : IO (Option ProcEntry) := do {
    let e <- entry_of d command cwd started;
    IO.pure (Option.some e)
}

def scan_one (d : Path) : IO (Option ProcEntry) := do {
    let meta <- Procs.read_meta (Store.child d "meta.json");
    match meta {
        Option.none => IO.pure Option.none,
        Option.some tri =>
            match tri {
                Pair.pair command rest2 => match rest2 {
                    Pair.pair cwd started => some_entry d command cwd started,
                }
            }
    }
}

#[terminating]
def scan_step (d : Path) (rest : List Path) (acc : List ProcEntry) : IO (List ProcEntry) := do {
    let one <- scan_one d;
    match one {
        Option.none => scan_dirs rest acc,
        Option.some e => scan_dirs rest (List.cons e acc),
    }
}

#[partial]
def scan_dirs (dirs : List Path) (acc : List ProcEntry) : IO (List ProcEntry) :=
    match dirs {
        List.empty => IO.pure acc,
        List.cons d rest => scan_step d rest acc,
    }

/// Newest-first by start time (insertion sort; the list is small).
#[partial]
def sort_desc (xs : List ProcEntry) : List ProcEntry :=
    match xs {
        List.empty => List.empty,
        List.cons x rest =>
            match sort_desc rest {
                List.empty => List.cons x List.empty,
                List.cons y ys =>
                    if x.started_ns < y.started_ns
                    then List.cons y (insert_desc x ys)
                    else List.cons x (List.cons y ys),
            },
    }

#[partial]
def insert_desc (x : ProcEntry) (xs : List ProcEntry) : List ProcEntry :=
    match xs {
        List.empty => List.cons x List.empty,
        List.cons y ys =>
            if y.started_ns < x.started_ns
            then List.cons x (List.cons y ys)
            else List.cons y (insert_desc x ys),
    }

pub def Procs.scan_at (root : Path) : IO (List ProcEntry) := do {
    let dirs <- IO.list_dir root;
    let entries <- scan_dirs dirs List.empty;
    IO.pure (sort_desc entries)
}

pub def Procs.list : IO (List ProcEntry) := do {
    let root <- Procs.root;
    Procs.scan_at root
}

/// The detached script. Paths are single-quoted; the command is shell
/// script by contract (the shell tool's own rule), and `< /dev/null`
/// detaches stdin so the child cannot read the terminal.
pub def Procs.detached_script (dir : Path) (cwd : String) (command : String) : String :=
    let log : String := shell_quote (Path.to_string (Store.child dir "log")) in
    let pidp : String := shell_quote (Path.to_string (Store.child dir "pid")) in
    let exitp : String := shell_quote (Path.to_string (Store.child dir "exit")) in
    let cd : String := if String.is_empty cwd then "" else String.concat "cd " (String.concat (shell_quote cwd) " && ") in
    String.concat_list [cd, "{ ( ", command, " ) > ", log,
        " 2>&1 < /dev/null; echo $? > ", exitp, "; } & echo $! > ", pidp]

pub def Procs.start_at (root : Path) (command : String) (cwd : String) : IO (Result String ProcEntry) := do {
    let ok <- Procs.ensure root;
    if Bool.not ok
    then IO.pure (Result.err (String.concat "could not create " (Path.to_string root)))
    else do {
        let now <- IO.current_time_nano;
        let id : String := String.concat "p-" (String.concat (I64.to_string process_id) (String.concat "-" (I64.to_string now)));
        let dir : Path := Store.child root id;
        let _ <- exec_cmd "mkdir" ["-p", Path.to_string dir];
        let _ <- write_text (Store.child dir "meta.json") (meta_json command cwd now);
        let script : String := Procs.detached_script dir cwd command;
        let _ <- exec_cmd "sh" ["-c", script];
        let pid <- pid_of dir;
        if pid < 1
        then IO.pure (Result.err (String.concat "could not start " command))
        else do {
            let status <- Procs.status_of dir pid;
            let e : ProcEntry := { id := id, pid := pid, command := command, cwd := cwd,
                started_ns := now, status := status, log := Store.child dir "log", dir := dir };
            IO.pure (Result.ok e)
        }
    }
}

pub def Procs.start (command : String) (cwd : String) : IO (Result String ProcEntry) := do {
    let root <- Procs.root;
    Procs.start_at root command cwd
}

/// The log's last `n` lines (missing log -> empty).
pub def Procs.tail (e : ProcEntry) (n : I64) : IO (List String) := do {
    let cap : I64 := if n < 1 then 1 else n;
    let script : String := String.concat "tail -n " (String.concat (I64.to_string cap)
        (String.concat " -- " (shell_quote (Path.to_string e.log))));
    let captured <- Proc.capture "sh" ["-c", script];
    match captured {
        Pair.pair _ out =>
            let lines : List String := theme_split_lines_keep out in
            IO.pure (take_last cap lines),
    }
}

/// Split on `\n`, dropping the final empty line `tail` introduces.
def theme_split_lines_keep (s : String) : List String :=
    if String.is_empty s then List.empty else split_keep (String.to_list s) List.empty List.empty

#[terminating]
def split_keep (bs : List U8) (cur : List U8) (acc : List String) : List String :=
    match bs {
        List.empty =>
            match cur {
                List.empty => List.reverse acc,
                List.cons _ _ => List.reverse (List.cons (String.from_list (List.reverse cur)) acc),
            },
        List.cons b rest =>
            if U8.beq b 10u8
            then split_keep rest List.empty (List.cons (String.from_list (List.reverse cur)) acc)
            else split_keep rest (List.cons b cur) acc,
    }

#[partial]
def drop_first (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs { List.empty => xs, List.cons _ rest => drop_first (n - 1) rest }

#[partial]
def len_str (xs : List String) : I64 :=
    match xs { List.empty => 0, List.cons _ rest => 1 + len_str rest }

def take_last (n : I64) (xs : List String) : List String :=
    let len : I64 := len_str xs in
    let cut : I64 := len - n in
    drop_first (if cut < 0 then 0 else cut) xs

def kill_running (e : ProcEntry) : IO (Result String String) := do {
    let script : String := String.concat "kill -TERM " (String.concat (I64.to_string e.pid)
        (String.concat "; sleep 0.2; kill -KILL " (I64.to_string e.pid)));
    let _ <- exec_cmd "sh" ["-c", script];
    let _ <- write_text (dir_child e "killed") "1";
    IO.pure (Result.ok (String.concat "killed " e.id))
}

pub def Procs.kill (e : ProcEntry) : IO (Result String String) :=
    match e.status {
        ProcStatus.running =>
            if e.pid < 1 then IO.pure (Result.err "no pid") else kill_running e,
        _ => IO.pure (Result.err "already exited"),
    }

def shutdown_all : IO Unit := do {
    let entries <- Procs.list;
    shutdown_go entries
}

/// Kill every running entry (normal exit). `WEAVER_PROC_KEEP` keeps them.
pub def Procs.shutdown : IO Unit := do {
    let keep <- IO.get_env "WEAVER_PROC_KEEP";
    match keep {
        Option.some _ => IO.pure unit,
        Option.none => shutdown_all,
    }
}

#[terminating]
def shutdown_step (e : ProcEntry) (rest : List ProcEntry) : IO Unit := do {
    let _ <- Procs.kill e;
    shutdown_go rest
}

#[partial]
def shutdown_go (xs : List ProcEntry) : IO Unit :=
    match xs {
        List.empty => IO.pure unit,
        List.cons e rest => shutdown_step e rest,
    }
