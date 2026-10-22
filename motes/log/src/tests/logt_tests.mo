/// `LogT`: the logger rides the environment, so a bind chain logs without
/// a `log` parameter. Every test EXECUTES the instance -- instance
/// resolution is a run-time step in Monad, so `check` alone cannot see a
/// missing one (transformers_tests.mo's recorded reason).
use log::level {LogLevel}
use log::logger {Logger, Logger.info}
use log::logt {
    LogT, LogT.run, LogT.lift, LogT.ask, LogT.local, LogT.with_field, LogT.debug, LogT.info,
}
use std::io {IO.read_file}
use std::path {Path}
use std::process {process_id}

def temp_path (suffix : String) : String :=
    String.concat "/tmp/monad_logt_test_"
        (String.concat (I64.to_string process_id) (String.concat "_" suffix))

def read_or_empty (path : String) : IO String := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err _ => IO.pure "",
        Result.ok s => IO.pure s,
    }
}

/// A do-block over `LogT IO` binds through the transformer, and the same
/// logger reaches every call.
#[test]
def test_logt_threads_the_logger : IO Bool := do {
    let path := temp_path "thread";
    let logger := Logger.file LogLevel.trace path;
    let action : LogT IO Unit := do {
        LogT.info "one";
        LogT.debug "two";
    };
    let _ <- LogT.run action logger;
    let out <- read_or_empty path;
    return (String.contains out "INFO one" && String.contains out "DEBUG two")
}

/// `with_field` changes the logger only for the wrapped computation.
#[test]
def test_logt_with_field_carries : IO Bool := do {
    let path := temp_path "field";
    let logger := Logger.file LogLevel.info path;
    let action : LogT IO Unit := LogT.with_field "k" "v" (LogT.info "x");
    let _ <- LogT.run action logger;
    let out <- read_or_empty path;
    return (String.contains out "x k=v")
}

/// `local` swaps the environment, not the computation.
#[test]
def test_logt_local_swaps_the_logger : IO Bool := do {
    let path := temp_path "local";
    let quiet := Logger.file LogLevel.error path;
    let chatter := Logger.with_field (Logger.file LogLevel.trace path) "scope" "test";
    let action : LogT IO Unit := LogT.local (fn (_l : Logger) => chatter) (LogT.info "hello");
    let _ <- LogT.run action quiet;
    let out <- read_or_empty path;
    return (String.contains out "INFO hello" && String.contains out "scope=test")
}

/// `lift` runs an underlying action unchanged.
#[test]
def test_logt_lift_runs_the_underlying_monad : IO Bool := do {
    let logger := Logger.file LogLevel.error (temp_path "lift-unused");
    let v <- LogT.run (LogT.lift (IO.pure 42)) logger;
    return (I64.beq v 42)
}

/// `ask` yields the environment's logger.
#[test]
def test_logt_ask_yields_the_logger : IO Bool := do {
    let path := temp_path "ask";
    let logger := Logger.file LogLevel.info path;
    let action : LogT IO Unit := do {
        let l <- LogT.ask;
        LogT.lift (Logger.info l "asked");
    };
    let _ <- LogT.run action logger;
    let out <- read_or_empty path;
    return (String.contains out "INFO asked")
}

/// The logger's own minimum level still filters.
#[test]
def test_logt_respects_filtering : IO Bool := do {
    let path := temp_path "filter";
    let logger := Logger.file LogLevel.warn path;
    let _ <- LogT.run (LogT.info "dropped") logger;
    let out <- read_or_empty path;
    return (out == "")
}
