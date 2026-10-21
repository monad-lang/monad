/// The logging levels and their two renderings: a numeric rank for
/// filtering and the uppercase name a log line carries. Constructors are
/// always written qualified (`LogLevel.error`) -- whole-program scope
/// already has a `LineClass.error`, and the repo records constructor
/// collisions as load-order-dependent.
pub type LogLevel {
    trace,
    debug,
    info,
    warn,
    error,
}

/// The filter rank: higher is more severe.
pub def LogLevel.rank (l : LogLevel) : I64 :=
    match l {
        LogLevel.trace => 0,
        LogLevel.debug => 1,
        LogLevel.info => 2,
        LogLevel.warn => 3,
        LogLevel.error => 4,
    }

/// The uppercase name a formatted line carries.
pub def LogLevel.name (l : LogLevel) : String :=
    match l {
        LogLevel.trace => "TRACE",
        LogLevel.debug => "DEBUG",
        LogLevel.info => "INFO",
        LogLevel.warn => "WARN",
        LogLevel.error => "ERROR",
    }
