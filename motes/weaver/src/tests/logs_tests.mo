/// The debug log's pure pieces and its crash detector.
use weaver::logs {
    level_of, format_of, Logs.sanitize, Logs.detect_crash, Logs.tail, Logs.take_last, Logs.finish,
}
use log::level {LogLevel}
use log::logger {LogFormat, Logger}
use std::path {Path, Path.to_string}
use std::io {IO.read_file, IO.write_file}
use std::process {process_id, exec_cmd}

def temp_dir (suffix : String) : String :=
    String.concat "/tmp/weaver_logs_test_"
        (String.concat (I64.to_string process_id) (String.concat "_" suffix))

def write_at (dir : String) (name : String) (text : String) : IO Unit := do {
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let _ <- IO.write_file (Path.path (String.concat dir (String.concat "/" name))) text;
    IO.pure unit
}

def read_at (path : String) : IO String := do {
    let r <- IO.read_file (Path.path path);
    match r { Result.ok s => IO.pure s, Result.err _ => IO.pure "" }
}

/// `WEAVER_LOG_FORMAT` names: json/jsonl/json_lines select JSON lines;
/// anything else, including unset, is the text form.
#[test]
def test_format_of_json_names : Bool :=
    (match format_of "json" { LogFormat.json_lines => true, _ => false })
        && (match format_of " jsonl " { LogFormat.json_lines => true, _ => false })
        && (match format_of "json_lines" { LogFormat.json_lines => true, _ => false })
        && (match format_of "" { LogFormat.plain_text => true, _ => false })
        && (match format_of "text" { LogFormat.plain_text => true, _ => false })

#[test]
def test_level_parsing : Bool :=
    (match level_of "debug" { Option.some l => LogLevel.name l == "DEBUG", Option.none => false })
        && (match level_of "error" { Option.some l => LogLevel.name l == "ERROR", Option.none => false })
        && (match level_of "off" { Option.none => true, Option.some _ => false })
        && (match level_of "bogus" { Option.none => true, Option.some _ => false })

#[test]
def test_sanitize_flattens_newlines : Bool :=
    Logs.sanitize "a\nb\rc" == "a b c"

#[test]
def test_take_last_keeps_the_tail : Bool :=
    match Logs.take_last 2 ["a", "b", "c"] {
        List.cons x rest => x == "b" && (match rest { List.cons y _ => y == "c", List.empty => false }),
        List.empty => false,
    }

#[test]
def test_crash_detector_flags_an_unclosed_log : IO Bool := do {
    let dir : String := temp_dir "crash";
    let _ <- exec_cmd "rm" ["-rf", dir];
    let log : String := String.concat dir "/100-999999.log";
    let _ <- write_at dir "100-999999.log" "100 INFO ev=process_start pid=999999\n101 INFO ev=turn_start turn=1\n";
    let found <- Logs.detect_crash (Path.path dir) "";
    let _ <- exec_cmd "rm" ["-rf", dir];
    IO.pure (match found {
        Option.some msg => String.contains msg "previous session ended unexpectedly",
        Option.none => false,
    })
}

#[test]
def test_crash_detector_accepts_a_clean_log : IO Bool := do {
    let dir : String := temp_dir "clean";
    let _ <- exec_cmd "rm" ["-rf", dir];
    let _ <- write_at dir "100-999999.log" "100 INFO ev=process_start pid=999999\n101 INFO ev=process_exit exit=0\n";
    let found <- Logs.detect_crash (Path.path dir) "";
    let _ <- exec_cmd "rm" ["-rf", dir];
    IO.pure (match found { Option.none => true, Option.some _ => false })
}

#[test]
def test_finish_writes_the_exit_marker : IO Bool := do {
    let dir : String := temp_dir "finish";
    let _ <- exec_cmd "rm" ["-rf", dir];
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let path : String := String.concat dir "/run.log";
    let log : Logger := Logger.file LogLevel.info path;
    Logs.finish (Option.some log) 0;
    let text <- read_at path;
    let _ <- exec_cmd "rm" ["-rf", dir];
    IO.pure (String.contains text "ev=process_exit exit=0")
}

#[test]
def test_tail_reads_the_last_lines : IO Bool := do {
    let dir : String := temp_dir "tail";
    let _ <- exec_cmd "rm" ["-rf", dir];
    let path : String := String.concat dir "/run.log";
    let _ <- write_at dir "run.log" "a\nb\nc\n";
    let text <- Logs.tail path 2;
    let _ <- exec_cmd "rm" ["-rf", dir];
    IO.pure (text == "b\nc")
}
