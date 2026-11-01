/// Trace-level tests: which string names which level, what an unreadable string
/// answers, and what each level includes.
///
/// WHAT IS NOT TESTED HERE, deliberately: that `log_line` writes to stderr. Asserting
/// that would mean reading the server's own error stream back, which this test
/// corpus has no plumbing for -- the session replay script is where stderr is
/// exercised, end to end, by a real process. What a unit test CAN pin is the half of
/// the rule that is pure, and the half that decides everything else: the mapping from
/// the specification's `TraceValue` strings to levels, the default a session starts
/// at, and the predicates the writers are gated on. A wrong mapping cannot be seen
/// from a session log, because a session log is the thing the mapping controls.
///
/// THE ASSERTIONS ARE ON PREDICATES AND NOT ON CONSTRUCTORS because there is nothing
/// to compare a `TraceLevel` with: the type has no `Eq`, and adding one for the sake
/// of a test would put a class instance in the mote's public surface. The two
/// predicates together are exact -- they distinguish all three levels -- so nothing
/// is lost by asserting through them.
use lsp::log {trace_at_messages, trace_at_verbose, trace_default, trace_of_str}

// --- The three names the specification gives ---

#[test]
def test_off_names_off : Bool :=
  Bool.not (trace_at_messages (trace_of_str "off"))

#[test]
def test_messages_names_messages : Bool :=
  trace_at_messages (trace_of_str "messages")
    && Bool.not (trace_at_verbose (trace_of_str "messages"))

#[test]
def test_verbose_names_verbose : Bool :=
  trace_at_verbose (trace_of_str "verbose")

// --- The mapping's misses ---

/// A string the specification does not name is a client that reached for the knob and
/// missed, and the answer is quiet: keeping the old level would leave the log on when
/// the client meant to move it, and any guess at what "noisy" means is a guess about
/// someone else's stderr.
#[test]
def test_a_value_the_specification_does_not_name_means_off : Bool :=
  Bool.not (trace_at_messages (trace_of_str "noisy"))

#[test]
def test_an_empty_value_means_off : Bool :=
  Bool.not (trace_at_messages (trace_of_str ""))

// --- The default ---

/// `messages`, so that a session tells its own story without being asked: the log
/// this server is for is the one that answers "did the edit arrive, was the file
/// rechecked" -- questions asked after the fact, when turning the trace on is too
/// late.
#[test]
def test_a_session_starts_at_messages : Bool :=
  trace_at_messages trace_default && Bool.not (trace_at_verbose trace_default)
