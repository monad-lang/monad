/// The level enum's two renderings: the filter rank is strictly ordered
/// and the names are the uppercase tokens a log line carries.
use log::level {LogLevel}

#[test]
def test_level_rank_is_strictly_ordered : Bool :=
    I64.lt (LogLevel.rank LogLevel.trace) (LogLevel.rank LogLevel.debug)
        && I64.lt (LogLevel.rank LogLevel.debug) (LogLevel.rank LogLevel.info)
        && I64.lt (LogLevel.rank LogLevel.info) (LogLevel.rank LogLevel.warn)
        && I64.lt (LogLevel.rank LogLevel.warn) (LogLevel.rank LogLevel.error)

#[test]
def test_level_names_are_uppercase : Bool :=
    LogLevel.name LogLevel.trace == "TRACE"
        && LogLevel.name LogLevel.debug == "DEBUG"
        && LogLevel.name LogLevel.info == "INFO"
        && LogLevel.name LogLevel.warn == "WARN"
        && LogLevel.name LogLevel.error == "ERROR"
