// The log mote's library root -- bare `use log` resolves here.
//
// Explicit re-exports, no globs: consumers name `LogLevel` and `Logger`
// or import the module they need directly (`use log::logger {...}`).
pub use lib::level {LogLevel}
pub use lib::logger {
    Logger,
    Logger.stdout,
    Logger.stderr,
    Logger.with_sink,
    Logger.file,
    Logger.with_field,
    Logger.format_line,
    Logger.should_emit,
    Logger.trace,
    Logger.debug,
    Logger.info,
    Logger.warn,
    Logger.error,
}
