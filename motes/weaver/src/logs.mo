/// Weaver's debug log: one append-only text file per run under
/// `<sessions root>/debug`, with `ev=` event tokens. A run that never
/// writes `ev=process_exit` is a crash; the next launch detects it by
/// scanning the directory (the runtime has no signal handler or atexit).
///
/// Never log API keys, prompts, or file contents -- event summaries,
/// paths, commands, usage and decisions only.
use log::level {LogLevel}
use log::logger {
    LogFormat, Logger, Logger.file, Logger.with_field, Logger.with_format,
    Logger.debug, Logger.info, Logger.warn, Logger.error,
}
use std::io {IO.get_env, IO.read_file, IO.list_dir, IO.epoch_time_nano, IO.write_stderr}
use std::path {Path, Path.to_string, Path.with_suffix}
use std::process {process_id, exec_cmd}
use weaver::store {Store.sessions_root}
use weaver::theme {theme_split_lines}
use std::list {List.intercalate, List.sort_by}

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

/// `WEAVER_LOG_FORMAT`: `json` (also `jsonl`/`json_lines`) selects one
/// JSON object per line; anything else is the human text form.
pub def format_of (s : String) : LogFormat :=
    let t : String := String.trim s in
    if Bool.or (t == "json") (Bool.or (t == "jsonl") (t == "json_lines"))
    then LogFormat.json_lines
    else LogFormat.plain_text

pub def Logs.format : IO LogFormat := do {
    let s <- env_string "WEAVER_LOG_FORMAT";
    IO.pure (format_of s)
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

/// Wall-clock seconds since the Unix epoch, for the filename.
pub def Logs.epoch : IO String := do {
    let now <- IO.epoch_time_nano;
    IO.pure (I64.to_string (I64.div now 1000000000))
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

/// One line's worth: newlines become spaces, capped at `n` bytes.
pub def Logs.sanitize_n (s : String) (n : I64) : String :=
    String.from_list (List.reverse (clean_bytes (String.to_list s) n List.empty))

/// The usual cap for paths, commands and summaries.
pub def Logs.sanitize (s : String) : String :=
    Logs.sanitize_n s 300

// ── memory sampling ─────────────────────────────────────────────────────

#[terminating]
def digit_at (s : String) (i : I64) : I64 :=
    if Bool.not (i < String.length s) then 0 - 1
    else
        let ch : String := String.slice s i 1 in
        if Bool.and (String.contains "0123456789" ch) (Bool.not (String.is_empty ch)) then i else digit_at s (i + 1)

def number_from (line : String) (key : String) : I64 :=
    if String.starts_with key line
    then
        let i : I64 := digit_at line (String.length key) in
        if I64.lt i 0 then 0 else parse_digits line i 0 0
    else 0

#[partial]
def find_status (lines : List String) (key : String) : I64 :=
    match lines {
        List.empty => 0,
        List.cons l rest =>
            let v : I64 := number_from (String.trim l) key in
            if I64.gt v 0 then v else find_status rest key,
    }

def rss_of_text (text : String) : Pair I64 I64 :=
    let lines : List String := theme_split_lines text in
    Pair.pair (find_status lines "VmRSS:") (find_status lines "VmHWM:")

/// `(VmRSS, VmHWM)` in kB; `(0, 0)` off Linux or on a read failure.
pub def Logs.rss : IO (Pair I64 I64) := do {
    let r <- IO.read_file (Path.path "/proc/self/status");
    match r {
        Result.err _ => IO.pure (Pair.pair 0 0),
        Result.ok text => IO.pure (rss_of_text text),
    }
}

#[partial]
def digits_value (s : String) (i : I64) : I64 :=
    if I64.lt i (String.length s)
    then
        let ch : String := String.slice s i 1 in
        if Bool.and (String.contains "0123456789" ch) (Bool.not (String.is_empty ch))
        then parse_digits s i 0 0
        else digits_value s (i + 1)
    else 0

def env_i64 (name : String) : IO I64 := do {
    let s <- env_string name;
    let t : String := String.trim s;
    if String.is_empty t then IO.pure 0 else IO.pure (digits_value t 0)
}

/// One RSS sample. `ev=rss_high` fires above `WEAVER_RSS_WARN_MB`
/// (default 1536); the hard stop is deliberately not wired until the
/// memory repro names the 28 GB owner.
def log_rss_values (log : Option Logger) (label : String) (rss : I64) (hwm : I64) : IO Unit := do {
    Logs.info log (String.concat "ev=rss label=" (String.concat label
        (String.concat " kb=" (String.concat (I64.to_string rss)
            (String.concat " hwm_kb=" (I64.to_string hwm))))));
    let warn_mb <- env_i64 "WEAVER_RSS_WARN_MB";
    let limit : I64 := if I64.lt warn_mb 1 then 1536 else warn_mb;
    if I64.gt (rss / 1024) limit
    then Logs.warn log (String.concat "ev=rss_high label=" (String.concat label
        (String.concat " mb=" (I64.to_string (rss / 1024)))))
    else IO.pure unit
}

def log_rss_pair (log : Option Logger) (label : String) (p : Pair I64 I64) : IO Unit :=
    match p {
        Pair.pair rss hwm => if I64.lt rss 1 then IO.pure unit else log_rss_values log label rss hwm,
    }

pub def Logs.log_rss (log : Option Logger) (label : String) : IO Unit := do {
    let p <- Logs.rss;
    log_rss_pair log label p
}

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

/// The newest log path other than `current`, by its `epoch-pid.log` name
/// (the epoch is seconds, so the names sort like their run times).
/// `IO.list_dir`'s order is the filesystem's, not time's -- scanning for the
/// first dead file reported whichever old log the directory happened to
/// list first, on every launch, and hid the crash that had just happened.
#[partial]
def newest_go (files : List Path) (current : String) (best : String) : String :=
    match files {
        List.empty => best,
        List.cons p rest =>
            let s : String := Path.to_string p in
            if s == current
            then newest_go rest current best
            else if Bool.or (String.is_empty best) (String.lt best s)
            then newest_go rest current s
            else newest_go rest current best,
    }

/// The newest run's log when it has no exit marker, as a human warning.
/// `None` when there is nothing to report -- including when the newest run
/// is clean: an older dead log is not "the previous session", and one run's
/// crash should not be reported forever.
pub def Logs.detect_crash (dir : Path) (current : String) : IO (Option String) := do {
    let files <- IO.list_dir dir;
    let newest : String := newest_go files current "";
    if String.is_empty newest
    then IO.pure Option.none
    else crash_of (Path.path newest)
}

// ── crash markers and retention ─────────────────────────────────────────

#[terminating]
def signal_after (s : String) (i : I64) : I64 :=
    if Bool.not (i + 6 < String.length s) then 0
    else if String.slice s i 7 == "signal=" then parse_digits s (i + 7) 0 0
    else signal_after s (i + 1)

#[partial]
def crash_files_go (files : List Path) (acc : List String) : List String :=
    match files {
        List.empty => acc,
        List.cons p rest =>
            let s : String := Path.to_string p in
            if Bool.and (Bool.or (String.contains s "/crash-") (String.contains s "/monad-crash-"))
                (String.ends_with s ".log")
            then crash_files_go rest (List.cons s acc)
            else crash_files_go rest acc,
    }

def crash_message (sig : I64) (pid : I64) : String :=
    String.concat "previous session was killed by signal "
        (String.concat (I64.to_string sig) (String.concat " (pid "
            (String.concat (I64.to_string pid) ")")))

/// The marker text's message, or none when it is not a signal marker.
def crash_marker_text (text : String) : Option String :=
    let sig : I64 := signal_after text 0 in
    if I64.lt sig 1
    then Option.none
    else Option.some (crash_message sig (first_pid (theme_split_lines text)))

def crash_remove_at (p : Path) (m : String) : IO (Option String) := do {
    let _ <- exec_cmd "rm" ["-f", Path.to_string p];
    IO.pure (Option.some m)
}

def crash_remove (p : Path) (msg : Option String) : IO (Option String) :=
    match msg {
        Option.none => IO.pure Option.none,
        Option.some m => crash_remove_at p m,
    }

/// Read and REMOVE one crash marker; the message names the signal.
def crash_marker_of (p : Path) : IO (Option String) := do {
    let r <- IO.read_file p;
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok text => crash_remove p (crash_marker_text text),
    }
}

def crash_in_dir (dir : Path) : IO (Option String) := do {
    let files <- IO.list_dir dir;
    let names : List String := crash_files_go files List.empty;
    match names {
        List.empty => IO.pure Option.none,
        List.cons p _ => crash_marker_of (Path.path p),
    }
}

def crash_signal_elsewhere : IO (Option String) := do {
    let home <- IO.get_env "HOME";
    let h <- match home {
        Option.some h => crash_in_dir (Path.path (String.concat h "/.weaver")),
        Option.none => IO.pure Option.none,
    };
    match h {
        Option.some m => IO.pure (Option.some m),
        Option.none => crash_in_dir (Path.path "/tmp"),
    }
}

/// The newest marker among the debug dir, `$HOME/.weaver` and `/tmp`.
pub def Logs.detect_crash_signal (dir : Path) : IO (Option String) := do {
    let here <- crash_in_dir dir;
    match here {
        Option.some m => IO.pure (Option.some m),
        Option.none => crash_signal_elsewhere,
    }
}

#[partial]
def take_strings (n : I64) (xs : List String) : List String :=
    if I64.lt n 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_strings (n - 1) rest),
    }

#[partial]
def exec_cmds (paths : List String) : IO Unit :=
    match paths {
        List.empty => IO.pure unit,
        List.cons p rest => do { let _ <- exec_cmd "rm" ["-f", p]; exec_cmds rest },
    }

#[partial]
def run_logs (names : List String) (current : String) (acc : List String) : List String :=
    match names {
        List.empty => List.reverse acc,
        List.cons n rest =>
            if Bool.and (String.ends_with n ".log")
                (Bool.and (Bool.not (String.contains n "/crash-")) (Bool.not (String.beq n current)))
            then run_logs rest current (List.cons n acc)
            else run_logs rest current acc,
    }

/// Keep the newest `keep` run logs, never the current one and never a
/// crash marker. A run log's name is `<epoch>-<pid>.log`, so lexical
/// order is time order.
pub def Logs.prune (dir : Path) (current : String) (keep : I64) : IO Unit := do {
    let files <- IO.list_dir dir;
    let names : List String := List.map Path.to_string files;
    let logs : List String := run_logs names current List.empty;
    let sorted : List String := List.sort_by (fn (a : String) (b : String) => String.lt a b) logs;
    let excess : I64 := List.length sorted - keep;
    let _ <- (if I64.lt excess 1 then IO.pure unit else exec_cmds (take_strings excess sorted));
    IO.pure unit
}

// ── setup / events / queries ────────────────────────────────────────────

def log_crash_kind (log : Logger) (kind : String) (crash : Option String) : IO Unit :=
    match crash {
        Option.none => IO.pure unit,
        Option.some msg => Logger.warn log (String.concat kind (Logs.sanitize msg)),
    }

def log_crash (log : Logger) (crash : Option String) : IO Unit :=
    log_crash_kind log "ev=crash_detected " crash

def setup_with (level : LogLevel) : IO LogSetup := do {
    let dir <- Logs.dir;
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string dir];
    let epoch <- Logs.epoch;
    let path <- Logs.current_path dir epoch;
    let crash <- Logs.detect_crash dir path;
    let sig <- Logs.detect_crash_signal dir;
    let crash2 : Option String := match sig {
        Option.some m => Option.some m,
        Option.none => crash,
    };
    let keep_raw <- env_i64 "WEAVER_LOG_KEEP";
    let keep : I64 := if I64.lt keep_raw 1 then 50 else keep_raw;
    let _ <- Logs.prune dir path keep;
    let fmt <- Logs.format;
    let base : Logger := Logger.with_format (Logger.file level path) fmt;
    let log1 : Logger := Logger.with_field base "pid" (I64.to_string process_id);
    let log2 : Logger := Logger.with_field log1 "run" (String.concat epoch (String.concat "-" (I64.to_string process_id)));
    let _ <- (match sig {
        Option.some _ => log_crash_kind log2 "ev=crash_signal " crash2,
        Option.none => log_crash log2 crash2,
    });
    let out : LogSetup := { log := Option.some log2, path := path, crash := crash2 };
    IO.pure out
}

pub def Logs.setup : IO LogSetup := do {
    let raw <- env_string "WEAVER_LOG";
    let t : String := String.trim raw;
    let lvl : Option LogLevel := if String.is_empty t then Option.some LogLevel.info else level_of t;
    let unknown : Bool := Bool.and (Bool.not (String.is_empty t))
        (Bool.and (Bool.not (String.beq t "off")) (match lvl { Option.some _ => false, Option.none => true }));
    let _ <- (if unknown
        then IO.write_stderr "weaver: unknown WEAVER_LOG value; expected trace|debug|info|warn|error|off\n"
        else IO.pure unit);
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
    match log { Option.some l => Logger.error l (Logs.sanitize_n msg 2000), Option.none => IO.pure unit }

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
