/// `$/setTrace` values as the session logger's minimum level.
///
/// Asserted through `Logger.should_emit`, which is what every log call is gated on:
/// `off` keeps errors and drops the rest, `messages` adds info, `verbose` adds debug,
/// and a value the specification does not name is `off`.
use log::level {LogLevel}
use log::logger {Logger.should_emit}
use lsp::server {lsp_logger, lsp_trace_level}

def logs_at (value : String) (level : LogLevel) : Bool :=
    Logger.should_emit (lsp_logger (lsp_trace_level value)) level

#[test]
def test_off_keeps_only_errors : Bool :=
    logs_at "off" LogLevel.error && Bool.not (logs_at "off" LogLevel.info)

#[test]
def test_messages_is_info : Bool :=
    logs_at "messages" LogLevel.info && Bool.not (logs_at "messages" LogLevel.debug)

#[test]
def test_verbose_is_debug : Bool :=
    logs_at "verbose" LogLevel.debug

/// A client that reached for the knob and missed is asking for less log, not more.
#[test]
def test_a_value_the_specification_does_not_name_means_off : Bool :=
    Bool.not (logs_at "noisy" LogLevel.info) && Bool.not (logs_at "" LogLevel.info)
