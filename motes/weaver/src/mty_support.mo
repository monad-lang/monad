// weaver / mty_support -- spawn, isolation, gating and assertion helpers
// shared by the pty drivers in `weaver::mty::*`.
//
// The generic harness lives in `motes/mty`; this module is the weaver-specific
// glue (weaver's argv, mock fixtures, per-test roots). Keeping it in weaver's
// `src/` is what lets `use weaver::mty_support` resolve: `use` paths address a
// mote's `src/`, not the `test/` directory.
//
// `WEAVER_MTY=1` enables the suite; unset skips it green, so the ordinary
// `monad test` sweeps stay clean.
use mty::spawn {SpawnConfig, Mty, Output}
use mty::check {Check.enabled, Check.skip, Check.bin_path, Check.value_set}
use mty::grid {Grid}
use std::concurrent::combine {sleepIO}
use std::io {IO.println, IO.get_env, IO.current_time, IO.current_time_nano, IO.read_file}
use std::path {Path, Path.is_absolute}
use std::process {process_id, exec_cmd}
use std::test {Test.write_fixture}
use parsec::number {parse_i64}
use weaver::procs {ProcEntry, Procs.scan_at}
use weaver::theme {theme_split_lines}

def env_or (name : String) (fallback : String) : IO String := do {
    let v <- IO.get_env name;
    match v {
        Option.some s => IO.pure s,
        Option.none => IO.pure fallback
    }
}

pub def repo_root : IO String := do {
    let v <- IO.get_env "MTY_ROOT";
    match v {
        Option.some s => IO.pure s,
        Option.none => env_or "PWD" "."
    }
}

pub def fixture_path (name : String) : IO String := do {
    let root <- repo_root;
    return (String.concat root (String.concat "/motes/weaver/test/fixtures/" name))
}

/// A fresh `/tmp/mty_<label>_<pid>_<nano>` with `sessions/`, `procs/` and
/// `logs/`.
pub def temp_root (label : String) : IO String := do {
    let t <- IO.current_time_nano;
    let root := String.concat "/tmp/mty_" (String.concat label
        (String.concat "_" (String.concat (I64.to_string process_id)
            (String.concat "_" (I64.to_string t)))));
    let sessions := String.concat root "/sessions";
    let procs := String.concat root "/procs";
    let logs := String.concat root "/logs";
    let _ <- exec_cmd "mkdir"
        (List.cons "-p" (List.cons root (List.cons sessions (List.cons procs
            (List.cons logs List.empty)))));
    return root
}

def base_env (root : String) : List (Pair String (Option String)) :=
    List.cons (Pair.pair "HOME" (Option.some root))
        (List.cons (Pair.pair "WEAVER_SESSION_ROOT" (Option.some (String.concat root "/sessions")))
            (List.cons (Pair.pair "WEAVER_PROC_ROOT" (Option.some (String.concat root "/procs")))
                (List.cons (Pair.pair "NO_COLOR" Option.none) List.empty)))

def turns_env (fixture : Option String) : List (Pair String (Option String)) :=
    match fixture {
        Option.some p => List.cons (Pair.pair "SHUTTLE_MOCK_TURNS" (Option.some p)) List.empty,
        Option.none => List.empty
    }

pub def env_of (root : String) (fixture : Option String) (extra : List (Pair String (Option String))) : List (Pair String (Option String)) :=
    List.append (List.append (base_env root) (turns_env fixture)) extra

pub def weaver_args (model : String) : List String :=
    List.cons "--provider" (List.cons "mock" (List.cons "--model" (List.cons model List.empty)))

/// Make a relative `WV_BIN` absolute: the child chdirs to the test root
/// before `execl`, so a relative path would resolve against the wrong cwd.
def absolute_bin (bin : String) : IO String := do {
    if Path.is_absolute (Path.path bin) then IO.pure bin
    else do {
        let root <- repo_root;
        return (String.concat root (String.concat "/" bin))
    }
}

/// Spawn weaver with extra CLI switches (e.g. `--resume <id>`, `--no-color`)
/// and the child's cwd set to the isolated root.
pub def spawn_args (bin : String) (model : String) (extra_args : List String)
    (rows : I64) (cols : I64) (root : String)
    (fixture : Option String)
    (extra : List (Pair String (Option String))) : IO (Result String Mty) := do {
    let abs <- absolute_bin bin;
    let cfg : SpawnConfig := {
        bin := abs,
        args := List.append (weaver_args model) extra_args,
        rows := rows,
        cols := cols,
        env := env_of root fixture extra,
        cwd := Option.some root
    };
    Mty.spawn cfg
}

pub def spawn (bin : String) (model : String) (rows : I64) (cols : I64) (root : String)
    (fixture : Option String) (extra : List (Pair String (Option String))) : IO (Result String Mty) :=
    spawn_args bin model List.empty rows cols root fixture extra

/// `WEAVER_MTY` unset -> print SKIP and return none (green); set -> return
/// the binary path. A missing binary then fails the test through `spawn`.
pub def gate (label : String) : IO (Option String) := do {
    let on <- Check.enabled "WEAVER_MTY";
    if Bool.not on then do {
        let _ <- Check.skip label;
        return Option.none
    } else do {
        let bin <- Check.bin_path "target-monad/release/weaver";
        return (Option.some bin)
    }
}

/// Run `body` with the resolved binary, or skip green when `WEAVER_MTY` is
/// unset. The body owns its temp root (see `with_root`).
pub def run_gated (label : String) (body : String -> IO Bool) : IO Bool := do {
    let g <- gate label;
    match g {
        Option.none => IO.pure true,
        Option.some bin => body bin
    }
}

/// Create a labelled temp root, run `body`, then remove it on success and
/// keep it (named on stdout) on failure.
pub def with_root (label : String) (body : String -> IO Bool) : IO Bool := do {
    let root <- temp_root label;
    let ok <- body root;
    cleanup_if ok root;
    return ok
}

pub def cleanup (root : String) : IO Unit := do {
    let keep <- Check.value_set "WV_SESSION_KEEP";
    if keep then IO.pure unit
    else do {
        let _ <- exec_cmd "rm" (List.cons "-rf" (List.cons root List.empty));
        return unit
    }
}

/// Remove the root on success; keep it (and name it) on failure for logs.
pub def cleanup_if (ok : Bool) (root : String) : IO Unit :=
    if ok then cleanup root
    else do {
        IO.println (String.concat "mty: kept failed test root " root);
        return unit
    }

/// Send Ctrl+C twice and wait for the alt-screen restore.
pub def quit_cleanly (m : Mty) (deadline_ms : I64) : IO Bool := do {
    Mty.send_text m "\u{3}";
    Mty.send_text m "\u{3}";
    Mty.wait_until m (fn (o : Output) => String.contains o.raw "\u{1b}[?1049l") deadline_ms
}

pub def pos_row (p : Pair I64 I64) : I64 :=
    match p { Pair.pair r _ => r }

pub def pos_col (p : Pair I64 I64) : I64 :=
    match p { Pair.pair _ c => c }

pub def found_at_row (o : Output) (needle : String) (row : I64) : Bool :=
    match Output.find o needle {
        Option.some p => I64.beq (pos_row p) row,
        Option.none => false
    }

pub def not_found (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.none => true,
        Option.some _ => false
    }

/// Count non-overlapping occurrences of an ASCII needle.
#[partial]
def count_at (hay : String) (needle : String) (i : I64) (acc : I64) : I64 :=
    if I64.gt (i + String.length needle) (String.length hay) then acc
    else if String.slice hay i (String.length needle) == needle then count_at hay needle (i + 1) (acc + 1)
    else count_at hay needle (i + 1) acc

pub def count_occurrences (hay : String) (needle : String) : I64 :=
    if String.is_empty needle then 0 else count_at hay needle 0 0

#[partial]
def rows_with_go (g : Grid) (needle : String) (r : I64) (to : I64) (acc : I64) : I64 :=
    if Bool.not (I64.lt r to) then acc
    else
        let hit := if String.contains (Grid.row_text g r) needle then acc + 1 else acc in
        rows_with_go g needle (r + 1) to hit

pub def rows_with (g : Grid) (needle : String) (from : I64) (to : I64) : I64 :=
    rows_with_go g needle from to 0

pub def any_row (g : Grid) (needle : String) (from : I64) (to : I64) : Bool :=
    I64.gt (rows_with g needle from to) 0

/// A 1-based SGR mouse report; `x`/`y` are 0-based cell coordinates.
pub def sgr (button : I64) (x : I64) (y : I64) (final : String) : String :=
    String.concat "\u{1b}[<" (I64.to_string button
        ++ ";" ++ I64.to_string (x + 1)
        ++ ";" ++ I64.to_string (y + 1)
        ++ final)

// ── Files, logs and processes ───────────────────────────────────────────

/// Write `<root>/.weaver/config.toml` with `mode = "<mode>"` (bigplan's plan
/// mode). The child cwd is the root, so this is the project config it sees.
pub def write_mode_config (root : String) (mode : String) : IO Unit := do {
    let dir := String.concat root "/.weaver";
    let _ <- exec_cmd "mkdir" (List.cons "-p" (List.cons dir List.empty));
    let body := String.concat "mode = \"" (String.concat mode "\"\n");
    let _ <- Test.write_fixture (Path.path (String.concat dir "/config.toml")) body;
    return unit
}

/// Read a file, or "" when it is absent/unreadable (a log may not exist yet).
pub def read_text (path : String) : IO String := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err _ => IO.pure "",
        Result.ok s => IO.pure s
    }
}

pub def wait_file_contains (path : String) (needle : String) (deadline_ms : I64) : IO Bool := do {
    let start <- IO.current_time;
    wait_file_go path needle (start + deadline_ms)
}

#[partial]
def wait_file_go (path : String) (needle : String) (deadline : I64) : IO Bool := do {
    let text <- read_text path;
    if String.contains text needle then IO.pure true
    else do {
        let now <- IO.current_time;
        if I64.gt now deadline then IO.pure false
        else do { sleepIO 50; wait_file_go path needle deadline }
    }
}

/// `VmRSS` in kB from `/proc/<pid>/status`; -1 when it cannot be read.
///
/// The final `return` is load-bearing. The self-hosted compile gate
/// typechecks only the TARGET module (`check_deps=false`; see
/// `plans/bootstrapping/check-deps-memory-blowup.md`), so an ill-typed
/// helper in a library is not diagnosed when a test imports it. A bare
/// tail expression here compiled to the raw `I64` through the `IO.bind`
/// continuation, and `monad_get_tag` dereferenced that RSS integer -- the
/// historical "fiber/GC SIGSEGV" in the sessions driver. `monad-rs check`
/// and the corpus sweeps catch the shape; keep the `return` anyway.
pub def rss_kb (pid : I64) : IO I64 := do {
    let path := String.concat "/proc/" (String.concat (I64.to_string pid) "/status");
    let text <- read_text path;
    return (rss_of_lines (theme_split_lines text))
}

#[partial]
def rss_of_lines (lines : List String) : I64 :=
    match lines {
        List.empty => 0 - 1,
        List.cons l rest =>
            if String.starts_with "VmRSS:" l then rss_value l else rss_of_lines rest
    }

/// `VmRSS:      1234 kB` -> 1234.
def rss_value (l : String) : I64 :=
    let t := String.trim (String.drop 6 l) in
    let body := if String.ends_with t " kB" then String.slice t 0 (String.length t - 3) else t in
    match parse_i64 body {
        Option.some v => v,
        Option.none => 0 - 1
    }

pub def proc_entries (root : String) : IO (List ProcEntry) :=
    Procs.scan_at (Path.path root)

/// The task list once at least one entry exists, or empty at the deadline.
pub def wait_proc_entries (root : String) (deadline_ms : I64) : IO (List ProcEntry) := do {
    let start <- IO.current_time;
    wait_proc_go root (start + deadline_ms)
}

#[partial]
def wait_proc_go (root : String) (deadline : I64) : IO (List ProcEntry) := do {
    let es <- proc_entries root;
    match es {
        List.cons e rest => IO.pure (List.cons e rest),
        List.empty => do {
            let now <- IO.current_time;
            if I64.gt now deadline then IO.pure List.empty
            else do { sleepIO 50; wait_proc_go root deadline }
        }
    }
}

pub def wait_pid_gone (pid : I64) (deadline_ms : I64) : IO Bool := do {
    let start <- IO.current_time;
    wait_pid_go pid (start + deadline_ms)
}

#[partial]
def wait_pid_go (pid : I64) (deadline : I64) : IO Bool := do {
    let alive <- Mty.pid_alive pid;
    if Bool.not alive then IO.pure true
    else do {
        let now <- IO.current_time;
        if I64.gt now deadline then IO.pure false
        else do { sleepIO 50; wait_pid_go pid deadline }
    }
}

/// Last-resort cleanup for a detached task whose parent was killed.
pub def kill_pid_9 (pid : I64) : IO Unit := do {
    let cmd := String.concat "kill -9 " (I64.to_string pid);
    let _ <- exec_cmd "sh" (List.cons "-c" (List.cons cmd List.empty));
    return unit
}

/// The status bar shows `turns <n>/<budget>`; match on the prefix so the
/// budget value does not matter.
pub def status_turns (o : Output) (n : I64) : Bool :=
    match Output.find o (String.concat "turns " (String.concat (I64.to_string n) "/")) {
        Option.some _ => true,
        Option.none => false
    }

/// The input box's placeholder row (an empty input, after a submit/recall).
pub def input_row (o : Output) : Option I64 :=
    match Output.find o "type a message" {
        Option.some p => Option.some (pos_row p),
        Option.none => Option.none
    }

/// A bracketed paste, chunked so a dialog reading one byte per syscall cannot
/// block the writer.
pub def send_paste (m : Mty) (s : String) : IO Unit := do {
    Mty.send_text m "\u{1b}[200~";
    Mty.send_chunked m s 1024 50;
    Mty.send_text m "\u{1b}[201~";
    return unit
}
