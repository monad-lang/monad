/// Logger behavior: the exact line shape, level filtering, structured
/// fields, and the append-mode file sink. Each file test owns a
/// PID-qualified path (a fixed /tmp name collides across runs).
use log::level {LogLevel}
use log::logger {Logger}
use std::io {IO.read_file}
use std::path {Path}
use std::process {process_id, exec_cmd}

def temp_path (suffix : String) : String :=
    String.concat "/tmp/monad_log_test_"
        (String.concat (I64.to_string process_id) (String.concat "_" suffix))

def read_or_empty (path : String) : IO String := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err _ => IO.pure "",
        Result.ok s => IO.pure s,
    }
}

#[test]
def test_format_line_shape : Bool :=
    Logger.format_line LogLevel.info "hello" List.empty 42 == "42 INFO hello\n"

#[test]
def test_format_line_fields_keep_added_order : Bool :=
    // `with_field` prepends internally; the formatter reverses, so fields
    // read in the order the caller added them.
    let fs : List (Pair String String) := [Pair.pair "b" "2", Pair.pair "a" "1"] in
    Logger.format_line LogLevel.warn "hi" fs 7 == "7 WARN hi a=1 b=2\n"

#[test]
def test_should_emit_boundaries : IO Bool := do {
    let logger := Logger.with_sink LogLevel.warn (fn (_ : String) => IO.pure unit);
    return (Bool.not (Logger.should_emit logger LogLevel.debug)
        && Logger.should_emit logger LogLevel.warn
        && Logger.should_emit logger LogLevel.error)
}

#[test]
def test_file_sink_appends_and_filters : IO Bool := do {
    let path : String := temp_path "append";
    let _ <- exec_cmd "rm" ["-f", path];
    let logger := Logger.file LogLevel.warn path;
    Logger.debug logger "below the minimum";
    Logger.warn logger "kept one";
    Logger.error logger "kept two";
    let text <- read_or_empty path;
    let _ <- exec_cmd "rm" ["-f", path];
    return (Bool.not (String.contains text "below the minimum")
        && String.contains text "kept one"
        && String.contains text "kept two")
}

#[test]
def test_with_field_reaches_the_sink : IO Bool := do {
    let path : String := temp_path "field";
    let _ <- exec_cmd "rm" ["-f", path];
    let logger := Logger.with_field (Logger.file LogLevel.info path) "run" "r-1";
    Logger.info logger "started";
    let text <- read_or_empty path;
    let _ <- exec_cmd "rm" ["-f", path];
    return (String.contains text "run=r-1" && String.contains text "started")
}
