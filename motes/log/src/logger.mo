/// `Logger`: a minimum level, a sink (`String -> IO Unit`), and the
/// structured fields every line carries. A log call below the minimum is
/// a pure no-op; at or above it, the line is formatted once and handed to
/// the sink exactly once.
///
/// The file sink appends with `FdStream.append_mode` (O_APPEND): each line
/// is one open/write/close, so a process crash cannot tear a previously
/// written line. There is no fsync -- process-crash safe, not power-loss
/// safe, the same contract as weaver's session store.
use std::io {IO.write_stdout, IO.write_stderr, IO.current_time}
use std::path {Path}
use std::bytebuf {ByteBuf, ByteBuf.of_string, ByteBuf.free}
use std::stream {FdStream, FdStream.open_file, FdStream.append_mode, Stream}
use log::level {LogLevel}

pub struct Logger {
    min_level : LogLevel,
    sink : String -> IO Unit,
    fields : List (Pair String String),
}

/// A logger writing to stdout (`write_stdout` does not append a newline;
/// the formatter supplies it).
pub def Logger.stdout (min_level : LogLevel) : Logger :=
    { min_level := min_level, sink := IO.write_stdout, fields := List.empty }

/// A logger writing to stderr; `IO.write_stderr` flushes every write.
pub def Logger.stderr (min_level : LogLevel) : Logger :=
    { min_level := min_level, sink := IO.write_stderr, fields := List.empty }

/// A logger writing through any sink -- a file, an in-memory test seam, a
/// forwarder.
pub def Logger.with_sink (min_level : LogLevel) (sink : String -> IO Unit) : Logger :=
    { min_level := min_level, sink := sink, fields := List.empty }

/// Append one already-formatted line to `path`. A failed open or write is
/// dropped: logging must never take down the program it observes.
def append_line (path : String) (line : String) : IO Unit := do {
    let opened <- FdStream.open_file (Path.path path) FdStream.append_mode;
    match opened {
        Result.err _ => IO.pure unit,
        Result.ok s => do {
            let buf <- ByteBuf.of_string line;
            let _ <- Stream.write s buf;
            let _ <- ByteBuf.free buf;
            Stream.close s
        },
    }
}

/// A logger appending each line to `path`. The caller creates the parent
/// directory; a write failure is silent.
pub def Logger.file (min_level : LogLevel) (path : String) : Logger :=
    Logger.with_sink min_level (fn (line : String) => append_line path line)

/// A new logger carrying one more `key=value` field. Immutable builder:
/// fields added later print later (the formatter walks the reverse of the
/// prepend list).
pub def Logger.with_field (logger : Logger) (key : String) (value : String) : Logger :=
    { logger with fields := List.cons (Pair.pair key value) logger.fields }

/// One field's rendered piece, ` key=value`.
def field_piece (p : Pair String String) : String :=
    match p {
        Pair.pair k v => String.concat " " (String.concat k (String.concat "=" v)),
    }

#[terminating]
def field_pieces (fs : List (Pair String String)) (acc : List String) : List String :=
    match fs {
        List.empty => List.reverse acc,
        List.cons p rest => field_pieces rest (List.cons (field_piece p) acc),
    }

/// The line format: `<ts> <LEVEL> <msg> [key=value ...]\n`. Pure, so tests
/// assert the exact shape without a sink. `ts` is `IO.current_time` --
/// monotonic milliseconds on the compiled backend, epoch on the
/// interpreter; callers use it for ordering, not calendar time.
pub def Logger.format_line (level : LogLevel) (msg : String) (fields : List (Pair String String)) (ts : I64) : String :=
    let head : String := String.concat (I64.to_string ts)
        (String.concat " " (String.concat (LogLevel.name level) (String.concat " " msg))) in
    let fs : List String := field_pieces (List.reverse fields) List.empty in
    String.concat (String.concat head (String.concat_list fs)) "\n"

/// Whether `level` clears the logger's minimum.
pub def Logger.should_emit (logger : Logger) (level : LogLevel) : Bool :=
    Bool.not (I64.lt (LogLevel.rank level) (LogLevel.rank logger.min_level))

/// Filter, format, sink. Below the minimum this is `IO.pure unit`.
def Logger.log (logger : Logger) (level : LogLevel) (msg : String) : IO Unit :=
    if Bool.not (Logger.should_emit logger level)
    then IO.pure unit
    else do {
        let ts <- IO.current_time;
        let line : String := Logger.format_line level msg logger.fields ts;
        logger.sink line
    }

pub def Logger.trace (logger : Logger) (msg : String) : IO Unit := Logger.log logger LogLevel.trace msg
pub def Logger.debug (logger : Logger) (msg : String) : IO Unit := Logger.log logger LogLevel.debug msg
pub def Logger.info (logger : Logger) (msg : String) : IO Unit := Logger.log logger LogLevel.info msg
pub def Logger.warn (logger : Logger) (msg : String) : IO Unit := Logger.log logger LogLevel.warn msg
pub def Logger.error (logger : Logger) (msg : String) : IO Unit := Logger.log logger LogLevel.error msg
