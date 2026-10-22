// The log mote's library root -- bare `use log` resolves here.
//
// Explicit re-exports, no globs: consumers name `LogLevel` and `Logger`
// or import the module they need directly (`use log::logger {...}`).
pub use lib::level {LogLevel}
pub use lib::logger {
    LogFormat,
    Logger,
    Logger.stdout,
    Logger.stderr,
    Logger.with_sink,
    Logger.file,
    Logger.with_field,
    Logger.with_format,
    Logger.format_line,
    Logger.format_json_line,
    Logger.should_emit,
    Logger.trace,
    Logger.debug,
    Logger.info,
    Logger.warn,
    Logger.error,
}
pub use lib::logt {
    LogT,
    LogT.run,
    LogT.lift,
    LogT.ask,
    LogT.local,
    LogT.with_field,
    LogT.trace,
    LogT.debug,
    LogT.info,
    LogT.warn,
    LogT.error,
}
