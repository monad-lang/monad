/// The server's own log: one line per event, on stderr, at a level the
/// client chooses.
///
/// STDERR, AND NOTHING BUT STDERR. This is `server.mo`'s one rule for
/// anything it wants to say, and this module exists so the rule is kept in
/// one place rather than re-decided at every call site: stdout carries
/// protocol frames, so a log line written there would be a malformed frame
/// a client rejects while trying to read a reply, and the client's complaint
/// would be about the protocol rather than about the print. Every writer
/// here goes to `IO.write_stderr`, prefixed `monad-lsp:` so that an editor's
/// captured log names the process the line came from when several servers
/// share one stderr.
///
/// THREE LEVELS, AND THE CLIENT HOLDS THE KNOB. The specification's own
/// mechanism is the `$/setTrace` notification, whose value is one of
/// "off", "messages" or "verbose"; `server.mo` routes that notification
/// into this module's `TraceLevel`. The mapping is total and quiet: an
/// absent or unreadable value answers `trace_off`, because a client that
/// reached for the knob and missed is asking for less log, not more.
///
/// THE DEFAULT IS `messages`, and that is a decision about who this log is
/// for. A session against a live editor is the only way to answer most of
/// the questions this server's development actually raises -- did the
/// `didChange` arrive, was the file rechecked, how long did the hover take
/// -- and none of it exists if the log is off until someone remembers to
/// turn it on. So a session tells its own story by default, and a client
/// that wants silence says so once with `$/setTrace`.
///
/// WHAT EACH LEVEL IS FOR:
/// - `log_error`, ungated: misbehaviour and endings -- an unreadable
///   message, a malformed `didOpen`, a bad frame, a request before the
///   handshake. These are the lines a bug report is made of.
/// - `log_info`, at `messages`: the session's story, one line per message
///   handled -- the handshake and its negotiated facts, each request with
///   its method and id, each document notification with its uri.
/// - `log_verbose`: the story's arithmetic -- how long a frame took to
///   handle, how many diagnostics a check published. Loud, and the first
///   thing a `$/setTrace "off"` silences.
///
/// THIS MODULE HAS NO OPINION ABOUT THE SERVER, deliberately. It formats a
/// line and holds the level rule; `server.mo` decides what the events are
/// and composes the strings. That is what keeps the level semantics in one
/// file and the event vocabulary in another, and it is why nothing here
/// imports a protocol type.
pub type TraceLevel {
  trace_off,
  trace_messages,
  trace_verbose,
}

/// The level a session starts at, before any `$/setTrace` arrives.
///
/// `trace_messages`, and the reason is in the module doc: a session that
/// logs nothing by default answers none of the questions this server's
/// development asks of it.
pub def trace_default : TraceLevel := TraceLevel.trace_messages

/// The level the specification's `TraceValue` string names.
///
/// AN UNKNOWN STRING IS `trace_off`, not an error and not the old level
/// kept. A client that sends a value this server cannot read has reached
/// for the volume knob and missed; keeping the old level would leave the
/// log on when the client most likely meant to move it, while quiet is
/// both the safe reading and the one a misspelling of "off" lands on
/// anyway.
pub def trace_of_str (s : String) : TraceLevel :=
  if String.beq s "off"
  then TraceLevel.trace_off
  else if String.beq s "messages"
  then TraceLevel.trace_messages
  else if String.beq s "verbose"
  then TraceLevel.trace_verbose
  else TraceLevel.trace_off

/// Whether the level includes the session's story: everything but off.
pub def trace_at_messages (t : TraceLevel) : Bool :=
  match t {
    trace_off => false,
    trace_messages => true,
    trace_verbose => true,
  }

/// Whether the level includes the arithmetic: verbose only.
pub def trace_at_verbose (t : TraceLevel) : Bool :=
  match t {
    trace_off => false,
    trace_messages => false,
    trace_verbose => true,
  }

/// One line, to the only stream this server may speak on.
///
/// The prefix and the newline live here and nowhere else, so that no call
/// site can compose a line that reaches the client without them.
pub def log_line (msg : String) : IO Unit :=
  IO.write_stderr ("monad-lsp: " ++ msg ++ "\n")

/// An event the log is FOR: misbehaviour and endings, always written.
///
/// The name says what the line means, not that the server is failing: an
/// unknown request is a client's mistake worth recording even though the
/// server carries on.
pub def log_error (msg : String) : IO Unit := log_line msg

/// One line of the session's story: written unless the client silenced it.
pub def log_info (t : TraceLevel) (msg : String) : IO Unit :=
  if trace_at_messages t
  then log_line msg
  else IO.pure Unit.unit

/// One line of the story's arithmetic: written at verbose only.
pub def log_verbose (t : TraceLevel) (msg : String) : IO Unit :=
  if trace_at_verbose t
  then log_line msg
  else IO.pure Unit.unit
