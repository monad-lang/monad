/// Weaver's debug log: one append-only text file per run under
/// `<sessions root>/debug`, with `ev=` event tokens. A run that never
/// writes `ev=process_exit` is a crash; the next launch detects it by
/// scanning the directory (the runtime has no signal handler or atexit).
///
/// Never log API keys, prompts, or file contents -- event summaries,
/// paths, commands, usage and decisions only.
use log::level {LogLevel}
use log::logger {
    Logger, Logger.file, Logger.with_field,
    Logger.debug, Logger.info, Logger.warn, Logger.error,
}
use std::io {IO.get_env, IO.read_file, IO.list_dir, IO.current_time_nano}
use std::path {Path, Path.to_string, Path.with_suffix}
use std::process {process_id, exec_cmd, Proc.capture}
use weaver::store {Store.sessions_root}
use weaver::theme {theme_split_lines}
use std::list {List.intercalate}

pub struct LogSetup {
    log : Option Logger,
    path : String,
    crash : Option String,
}

/// `trace|debug|info|warn|error|off` (trimmed, lowercase). Unknown -> none.
pub def level_of (s : String) : Option LogLevel :=
    if s == "trace" then Option.some LogLevel.trace
    else if s == "debug" then Option.some LogLevel.debug
    else if s == "info" then Option.some LogLevel.info
    else if s == "warn" then Option.some LogLevel.warn
    else if s == "error" then Option.some LogLevel.error
    else if s == "off" then Option.none
    else Option.none

def env_string (name : String) : IO String := do {
    let got <- IO.get_env name;
    match got {
        Option.some s => IO.pure s,
        Option.none => IO.pure "",
    }
}

/// `WEAVER_LOG`, default info.
pub def Logs.level : IO (Option LogLevel) := do {
    let s <- env_string "WEAVER_LOG";
    let t : String := String.trim s;
    IO.pure (if String.is_empty t then Option.some LogLevel.info else level_of t)
}

def dir_of (override : String) (sessions : Option Path) : Path :=
    if Bool.not (String.is_empty (String.trim override))
    then Path.path (String.trim override)
    else match sessions {
        Option.some p => Path.with_suffix p "/debug",
        Option.none => Path.path "/tmp/weaver-debug",
    }

/// `WEAVER_LOG_DIR`, else `<sessions root>/debug`, else /tmp.
pub def Logs.dir : IO Path := do {
    let override <- env_string "WEAVER_LOG_DIR";
    let sessions <- Store.sessions_root;
    IO.pure (dir_of override sessions)
}

/// Wall-clock seconds for the filename: one `date +%s` (the compiled
/// runtime's clock is monotonic, not epoch). Falls back to a monotonic id.
def epoch_fallback : IO String := do {
    let now <- IO.current_time_nano;
    IO.pure (String.concat "m-" (I64.to_string now))
}

def epoch_of (code : I64) (out : String) : IO String :=
    let t : String := String.trim out in
    if Bool.and (I64.beq code 0) (Bool.not (String.is_empty t))
    then IO.pure t
    else epoch_fallback

pub def Logs.epoch : IO String := do {
    let r <- Proc.capture "date" ["+%s"];
    match r {
        Pair.pair code out => epoch_of code out,
    }
}

pub def Logs.current_path (dir : Path) (epoch : String) : IO String := do {
    let override <- env_string "WEAVER_DEBUG_LOG";
    let o : String := String.trim override;
    if Bool.not (String.is_empty o)
    then IO.pure o
    else IO.pure (Path.to_string (Path.with_suffix dir
        (String.concat "/" (String.concat epoch (String.concat "-" (String.concat (I64.to_string process_id) ".log"))))))
}

// ── sanitize ────────────────────────────────────────────────────────────

#[terminating]
def clean_bytes (bs : List U8) (n : I64) (acc : List U8) : List U8 :=
    if n < 1 then acc
    else match bs {
        List.empty => acc,
        List.cons b rest =>
            let b2 : U8 := if Bool.or (U8.beq b 10u8) (U8.beq b 13u8) then 32u8 else b in
            clean_bytes rest (n - 1) (List.cons b2 acc),
    }

/// One line's worth: newlines become spaces, capped at 300 bytes.
pub def Logs.sanitize (s : String) : String :=
    String.from_list (List.reverse (clean_bytes (String.to_list s) 300 List.empty))

// ── crash detection ─────────────────────────────────────────────────────

def first_pid (lines : List String) : I64 :=
    match lines {
        List.empty => 0,
        List.cons l rest =>
            if String.contains l "pid=" then pid_after l 0 else first_pid rest,
    }

#[terminating]
def pid_after (s : String) (i : I64) : I64 :=
    if Bool.not (i + 3 < String.length s)
    then 0
    else if String.slice s i 4 == "pid="
    then parse_digits s (i + 4) 0 0
    else pid_after s (i + 1)

#[terminating]
def parse_digits (s : String) (i : I64) (acc : I64) (n : I64) : I64 :=
    if Bool.not (i < String.length s)
    then acc
    else
        let ch : String := String.slice s i 1 in
        if Bool.and (String.contains "0123456789" ch) (Bool.not (String.is_empty ch))
        then parse_digits s (i + 1) (acc * 10 + char_digit ch) (n + 1)
        else if n < 1 then 0 else acc

def char_digit (ch : String) : I64 :=
    if ch == "0" then 0 else if ch == "1" then 1 else if ch == "2" then 2
    else if ch == "3" then 3 else if ch == "4" then 4 else if ch == "5" then 5
    else if ch == "6" then 6 else if ch == "7" then 7 else if ch == "8" then 8
    else 9

#[terminating]
def last_nonempty (lines : List String) : String :=
    match List.reverse lines {
        List.empty => "",
        List.cons l rest => if String.is_empty (String.trim l) then last_nonempty (List.reverse rest) else l,
    }

def is_alive (pid : I64) : IO Bool :=
    if pid < 1
    then IO.pure false
    else do {
        let code <- exec_cmd "sh" ["-c", String.concat "kill -0 " (String.concat (I64.to_string pid) " 2>/dev/null")];
        IO.pure (I64.beq code 0)
    }

def crash_check (p : Path) (pid : I64) (last : String) : IO (Option String) := do {
    let alive <- is_alive pid;
    if alive
    then IO.pure Option.none
    else
        let msg : String := String.concat "previous session ended unexpectedly (log: "
            (String.concat (Path.to_string p) (String.concat ", last: " (String.concat (Logs.sanitize last) ")"))) in
        IO.pure (Option.some msg)
}

def crash_of (p : Path) : IO (Option String) := do {
    let r <- IO.read_file p;
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok text =>
            let lines : List String := theme_split_lines text in
            let last : String := last_nonempty lines in
            if String.contains last "ev=process_exit"
            then IO.pure Option.none
            else crash_check p (first_pid lines) last,
    }
}

#[terminating]
def detect_one (p : Path) (rest : List Path) (current : String) : IO (Option String) := do {
    let c <- crash_of p;
    detect_go rest current c
}

#[partial]
def detect_go (files : List Path) (current : String) (acc : Option String) : IO (Option String) :=
    match files {
        List.empty => IO.pure acc,
        List.cons p rest =>
            if Path.to_string p == current
            then detect_go rest current acc
            else match acc {
                Option.some _ => IO.pure acc,
                Option.none => detect_one p rest current,
            },
    }

/// The first dead, unclosed log in `dir` other than `current`, as a
/// human warning. `None` when there is nothing to report.
pub def Logs.detect_crash (dir : Path) (current : String) : IO (Option String) := do {
    let files <- IO.list_dir dir;
    detect_go files current Option.none
}

// ── setup / events / queries ────────────────────────────────────────────

def log_crash (log : Logger) (crash : Option String) : IO Unit :=
    match crash {
        Option.none => IO.pure unit,
        Option.some msg => Logger.warn log (String.concat "ev=crash_detected " (Logs.sanitize msg)),
    }

def setup_with (level : LogLevel) : IO LogSetup := do {
    let dir <- Logs.dir;
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string dir];
    let epoch <- Logs.epoch;
    let path <- Logs.current_path dir epoch;
    let crash <- Logs.detect_crash dir path;
    let base : Logger := Logger.file level path;
    let log1 : Logger := Logger.with_field base "pid" (I64.to_string process_id);
    let log2 : Logger := Logger.with_field log1 "run" (String.concat epoch (String.concat "-" (I64.to_string process_id)));
    let _ <- log_crash log2 crash;
    let out : LogSetup := { log := Option.some log2, path := path, crash := crash };
    IO.pure out
}

pub def Logs.setup : IO LogSetup := do {
    let lvl <- Logs.level;
    match lvl {
        Option.none =>
            let out : LogSetup := { log := Option.none, path := "", crash := Option.none } in
            IO.pure out,
        Option.some level => setup_with level,
    }
}

/// A clean exit marker. A run that dies before this line is a crash.
pub def Logs.finish (log : Option Logger) (code : I64) : IO Unit :=
    match log {
        Option.none => IO.pure unit,
        Option.some l => Logger.info l (String.concat "ev=process_exit exit=" (I64.to_string code)),
    }

pub def Logs.info (log : Option Logger) (msg : String) : IO Unit :=
    match log { Option.some l => Logger.info l (Logs.sanitize msg), Option.none => IO.pure unit }

pub def Logs.debug (log : Option Logger) (msg : String) : IO Unit :=
    match log { Option.some l => Logger.debug l (Logs.sanitize msg), Option.none => IO.pure unit }

pub def Logs.warn (log : Option Logger) (msg : String) : IO Unit :=
    match log { Option.some l => Logger.warn l (Logs.sanitize msg), Option.none => IO.pure unit }

pub def Logs.error (log : Option Logger) (msg : String) : IO Unit :=
    match log { Option.some l => Logger.error l (Logs.sanitize msg), Option.none => IO.pure unit }

/// The newest log's path for `/log` (this run's file ends `-<pid>.log`).
#[partial]
def latest_go (files : List Path) (best : String) : String :=
    match files {
        List.empty => best,
        List.cons p rest =>
            let s : String := Path.to_string p in
            let best2 : String := if String.is_empty best then s else if String.lt best s then s else best in
            latest_go rest best2,
    }

pub def Logs.latest_path : IO (Option String) := do {
    let dir <- Logs.dir;
    let files <- IO.list_dir dir;
    let best : String := latest_go files "";
    IO.pure (if String.is_empty best then Option.none else Option.some best)
}

def drop_trailing_empty (xs : List String) : List String :=
    match List.reverse xs {
        List.cons l rest => if String.is_empty l then List.reverse rest else xs,
        List.empty => xs,
    }

def tail_of (text : String) (n : I64) : IO String := do {
    let lines : List String := drop_trailing_empty (theme_split_lines text);
    let kept : List String := Logs.take_last n lines;
    IO.pure (List.intercalate "\n" kept)
}

/// The file's last `n` lines, joined.
pub def Logs.tail (path : String) (n : I64) : IO String := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err _ => IO.pure "",
        Result.ok text => tail_of text n,
    }
}

#[partial]
def count_lines (xs : List String) : I64 :=
    match xs { List.empty => 0, List.cons _ rest => 1 + count_lines rest }

#[partial]
def drop_lines (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs { List.empty => xs, List.cons _ rest => drop_lines (n - 1) rest }

pub def Logs.take_last (n : I64) (xs : List String) : List String :=
    let cut : I64 := count_lines xs - n in
    drop_lines (if cut < 0 then 0 else cut) xs
