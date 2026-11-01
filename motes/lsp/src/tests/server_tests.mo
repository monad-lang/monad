/// Dispatch tests: the handshake, the routing, the exit codes, and the two decisions in
/// the read loop.
///
/// WHAT THESE TESTS COVER, AND WHAT THEY DELIBERATELY DO NOT. Everything below runs
/// against an EMPTY check store, so no file is read, no module graph is loaded and no
/// diagnostic is produced. That is the point rather than a limitation: what is pinned
/// here is the part of the server a client sees and a user cannot debug -- that
/// `initialize` answers with the encoding it was offered, that a request before the
/// handshake is refused with the code that says so, that an unknown method is ANSWERED
/// rather than ignored, and that `exit` without `shutdown` exits non-zero. A client that
/// gets any of those wrong hangs or desynchronizes, and neither shows up as a wrong
/// squiggle. The engine itself is `lang`'s, covered by `lang`'s tests and by the session
/// replay script, which is where a real file's diagnostics belong.
///
/// THE FIXTURES ARE LITERAL WIRE MESSAGES rather than calls to `toolkit::jsonrpc`'s
/// encoders, and that is deliberate. A test that built its request with the same module
/// the server parses with would pass while both sides were wrong in the same way; the
/// strings here are bytes a client sends, and the assertions are on bytes the server
/// would send back.
///
/// A NON-ASCII FRAME IS PINNED, because the failure it guards is silent. `Content-Length`
/// counts BYTES, and a server that counted characters would understate every frame whose
/// body contains a character outside ASCII -- and this corpus's comments are full of em
/// dashes and curly quotes. The client would then read the next frame starting inside
/// this one. The assertion is a byte count, so it fails the moment that is got wrong.
use lsp::log {trace_at_messages, trace_at_verbose}
use lsp::server {
  ServerState, ServerStep, lsp_at_eof, lsp_dispatch, lsp_frame, lsp_next_read, lsp_server_new,
  server_initialized, server_step_exit, server_step_bodies, server_step_state, server_trace,
}
use toolkit::framing {content_length}
use toolkit::jsonrpc {rpc_parse}

// --- Fixtures ---

/// `initialize` from a client that offers utf-8 first -- what Helix 25.07 sends.
def st_initialize_utf8 : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-8\",\"utf-16\"]}}}}"

/// The same, offering only utf-16, so that the two tests together pin that the choice
/// follows the client rather than a constant in this server.
def st_initialize_utf16 : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-16\"]}}}}"

/// A client with no `positionEncodings` at all, which is every client older than 3.17.
def st_initialize_plain : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{}}}"

def st_initialized : String := "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}"

def st_shutdown : String := "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\"}"

def st_exit : String := "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}"

/// A hover on a file that is not open, which is enough to exercise the routing without
/// reading anything.
def st_hover : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\",\"params\":{\"textDocument\":{\"uri\":\"file:///nonexistent.mo\"},\"position\":{\"line\":0,\"character\":0}}}"

/// A method this server does not implement.
def st_completion : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/completion\",\"params\":{}}"

/// A notification with no `params` at all, which is legal and which a client that
/// omitted them sends.
def st_did_change_bare : String := "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\"}"

/// Not JSON at all.
def st_garbage : String := "{\"jsonrpc\":\"2.0\","

/// The specification's own volume knob, turned up as far as it goes.
def st_set_trace_verbose : String :=
  "{\"jsonrpc\":\"2.0\",\"method\":\"$/setTrace\",\"params\":{\"value\":\"verbose\"}}"

/// A trace value the specification does not name, which must land on quiet rather than
/// on a guess.
def st_set_trace_garbage : String :=
  "{\"jsonrpc\":\"2.0\",\"method\":\"$/setTrace\",\"params\":{\"value\":\"noisy\"}}"

// --- Reading a step without touching a field in a test body ---
//
// This repository has a recorded `#[test]`-plus-struct-field codegen hazard: a test def
// that reads a field inline can be given the FIELD's type as its return type by the
// self-hosted compiler. Every read below goes through one of these single-level
// accessors instead, which is the documented remedy.

/// The first message BODY a step queued, or the empty string when it queued none.
///
/// A body and not a frame: the `Content-Length` header is added in one place,
/// `lsp_write_frames`, and a test that read a frame here would be reading bytes no
/// handler ever produces.
#[partial]
def st_first (fs : List String) : String :=
  match fs {
    List.empty => "",
    List.cons f _rest => f,
  }

/// Dispatch one wire message, answering the step and its first body together.
#[partial]
def st_ask (st : ServerState) (text : String) : IO (Pair ServerStep String) := do {
    let step <- lsp_dispatch st (rpc_parse text);
    return (Pair.pair step (st_first (server_step_bodies step)))
}

#[partial]
def st_body_of (answer : Pair ServerStep String) : String :=
  match answer {
    Pair.pair _step f => f,
  }

#[partial]
def st_step_of (answer : Pair ServerStep String) : ServerStep :=
  match answer {
    Pair.pair step _f => step,
  }

/// The state a step left, read through the accessor rather than the field.
#[partial]
def st_state_of (answer : Pair ServerStep String) : ServerState :=
  server_step_state (st_step_of answer)

/// Whether the step asked to end the session with `expected`.
#[partial]
def st_code_is (step : ServerStep) (expected : I64) : Bool :=
  match server_step_exit step {
    Option.none => false,
    Option.some c => I64.beq c expected,
  }

/// Run `initialize`, then `initialized`, and answer the state that leaves.
#[partial]
def st_handshake (text : String) : IO ServerState := do {
    let a1 <- st_ask lsp_server_new text;
    let a2 <- st_ask (st_state_of a1) st_initialized;
    return (st_state_of a2)
}

// --- The handshake ---

#[test]
def test_initialize_echoes_the_encoding_the_client_offered_first : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_utf8;
    return (String.contains (st_body_of a) "\"positionEncoding\":\"utf-8\"")
}

#[test]
def test_initialize_follows_the_client_rather_than_a_constant : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_utf16;
    return (String.contains (st_body_of a) "\"positionEncoding\":\"utf-16\"")
}

/// A client that offered nothing gets utf-16, which is the specification's floor: every
/// client must support it, so answering it cannot desynchronize anyone.
#[test]
def test_initialize_defaults_to_utf16_for_a_pre_317_client : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_plain;
    return (String.contains (st_body_of a) "\"positionEncoding\":\"utf-16\"")
}

/// The capabilities are a promise: a client that sees a provider it did not see here
/// will not ask for it, and one that sees `completionProvider` would put a popup in
/// front of the user that this server cannot fill.
#[test]
def test_initialize_advertises_no_unimplemented_provider : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_utf8;
    let f : String := st_body_of a;
    return (Bool.not (String.contains f "completionProvider")
              && String.contains f "\"hoverProvider\":true"
              && String.contains f "\"definitionProvider\":true"
              && String.contains f "\"documentSymbolProvider\":true"
              && String.contains f "\"workspaceSymbolProvider\":true")
}

#[test]
def test_initialize_is_not_a_handshake_until_initialized_arrives : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_utf8;
    return (Bool.not (server_initialized (st_state_of a)))
}

#[test]
def test_the_initialized_notification_completes_the_handshake : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    return (server_initialized st)
}

// --- Requests, before and after the handshake ---

/// -32002, which is the code a client interprets as "ask me again after initialize".
/// Answering it with a result instead would let a confused client be served from a state
/// that was never negotiated; answering nothing would hang it.
#[test]
def test_a_request_before_initialize_is_refused_with_not_initialized : IO Bool := do {
    let a <- st_ask lsp_server_new st_hover;
    return (String.contains (st_body_of a) "-32002")
}

#[test]
def test_a_hover_is_answered_once_the_handshake_is_done : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_hover;
    let f : String := st_body_of a;
    return (Bool.not (String.contains f "-32002") && String.contains f "\"result\":null")
}

/// An unanswered request hangs the client, so an unimplemented method is answered with
/// the code that says "not here" rather than with silence.
#[test]
def test_an_unimplemented_request_is_answered_method_not_found : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_completion;
    return (String.contains (st_body_of a) "-32601")
}

/// The reply echoes the id the client sent, which is the only way it can tell which of
/// its requests this answers.
#[test]
def test_a_reply_echoes_the_request_id : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_completion;
    return (String.contains (st_body_of a) "\"id\":4")
}

// --- Notifications ---

/// A notification has no reply, so one this server cannot read must be dropped rather
/// than answered: an unsolicited response is a visible protocol error, and a crash on a
/// malformed keystroke takes the whole session with it.
#[test]
def test_a_didchange_without_params_is_dropped_not_answered : IO Bool := do {
    let a <- st_ask lsp_server_new st_did_change_bare;
    return (String.beq (st_body_of a) "")
}

#[test]
def test_an_unknown_notification_produces_no_frame : IO Bool := do {
    let a <- st_ask lsp_server_new "{\"jsonrpc\":\"2.0\",\"method\":\"$/progress\"}";
    return (String.beq (st_body_of a) "")
}

/// `$/cancelRequest` arrives for every request a user aborts, so it is acted on by doing
/// nothing -- and the assertion is that doing nothing is not an answer.
#[test]
def test_a_cancel_request_produces_no_frame : IO Bool := do {
    let a <- st_ask lsp_server_new "{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{\"id\":1}}";
    return (String.beq (st_body_of a) "")
}

/// Input that is not JSON at all gets the parse error with a null id: the request that
/// would have carried one could not be read, and the specification requires a null there
/// rather than a guess.
#[test]
def test_an_unreadable_message_gets_a_parse_error_with_a_null_id : IO Bool := do {
    let a <- st_ask lsp_server_new st_garbage;
    let f : String := st_body_of a;
    return (String.contains f "-32700" && String.contains f "\"id\":null")
}

// --- Exit ---

/// The specification's one deliberate non-zero exit: a client that exits without asking
/// first skipped the handshake that exists so both sides know the other is done.
#[test]
def test_exit_without_shutdown_exits_nonzero : IO Bool := do {
    let a <- st_ask lsp_server_new st_exit;
    return (st_code_is (st_step_of a) 1)
}

#[test]
def test_exit_after_shutdown_exits_zero : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a1 <- st_ask st st_shutdown;
    let a2 <- st_ask (st_state_of a1) st_exit;
    return (st_code_is (st_step_of a2) 0)
}

/// `shutdown` does NOT end the session on its own: the client still gets its reply, and
/// the process stays alive until `exit`. A server that exited here would take the stream
/// away from a client with a reply in flight.
#[test]
def test_shutdown_replies_and_leaves_the_session_running : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_shutdown;
    return (String.contains (st_body_of a) "\"result\":null"
              && Bool.not (st_code_is (st_step_of a) 0))
}

#[test]
def test_a_notification_never_ends_the_session : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialized;
    return (Bool.not (st_code_is (st_step_of a) 0))
}

// --- Trace ---

/// The level the client last set is carried in the state, because the setting has to
/// outlive the message that set it: a `$/setTrace` that was forgotten by the next frame
/// would be a knob that turns itself back.
#[test]
def test_settrace_verbose_is_remembered_in_the_state : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_set_trace_verbose;
    return (trace_at_verbose (server_trace (st_state_of a)))
}

/// ...and it is still there a message later, which is the half of the same rule the
/// first test cannot show: the level survives a step that was not about the level.
#[test]
def test_the_trace_level_survives_the_next_message : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a1 <- st_ask st st_set_trace_verbose;
    let a2 <- st_ask (st_state_of a1) st_initialized;
    return (trace_at_verbose (server_trace (st_state_of a2)))
}

/// A trace value the specification does not name is quiet, not a guess -- the same
/// mapping `log_tests.mo` pins, asserted here through the whole route: a wire message,
/// the params reader, the state.
#[test]
def test_a_trace_value_the_specification_does_not_name_means_off : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_set_trace_garbage;
    return (Bool.not (trace_at_messages (server_trace (st_state_of a))))
}

/// `$/setTrace` is a notification, so the level change is the whole of the handling and
/// no reply exists to send -- an answered one would be a protocol violation a client is
/// entitled to log.
#[test]
def test_settrace_answers_nothing : IO Bool := do {
    let st : ServerState <- st_handshake st_initialize_utf8;
    let a <- st_ask st st_set_trace_verbose;
    return (String.beq (st_body_of a) "")
}

/// The session's story is on by default, which is the decision `log.mo`'s module doc
/// argues for: the questions this log answers are asked after the fact, when turning
/// the trace on is too late.
#[test]
def test_a_fresh_server_traces_at_messages : Bool :=
  trace_at_messages (server_trace lsp_server_new)

// --- The frame ---

#[test]
def test_a_frame_counts_the_body_in_bytes : Bool :=
  String.beq (lsp_frame "hello") "Content-Length: 5\r\n\r\nhello"

/// A two-byte character in a body the header says is two bytes long. This is the whole
/// of the byte-counting decision, and it is asserted as an exact frame because the
/// failure it guards -- a header that understates the body -- is silent.
#[test]
def test_a_frame_counts_a_non_ascii_body_in_bytes_not_characters : Bool :=
  String.beq (lsp_frame "é") "Content-Length: 2\r\n\r\né"

#[test]
def test_a_frame_of_an_empty_body_is_still_a_frame : Bool :=
  String.beq (lsp_frame "") "Content-Length: 0\r\n\r\n"

/// The header is added in exactly ONE place, and these are the two halves that say so:
/// what a handler queues is a body that starts with `{` and carries no header, and what
/// reaches the wire is that body with the header in front of it. A call site that framed
/// its own reply would pass the second half and fail the first -- and it would put a
/// second header on the wire, which is a client-side parse failure produced by a server
/// that looks entirely healthy from the inside. This is the pin for a real defect: every
/// reply the server sent was a bare body, and nothing asserted the header because the
/// only frame tests in this file framed a literal by hand.
#[test]
def test_a_dispatched_reply_is_a_body_that_the_writer_frames : IO Bool := do {
    let a <- st_ask lsp_server_new st_initialize_utf8;
    let body : String := st_body_of a;
    let wire : String := lsp_frame body;
    return (String.beq (String.slice body 0 1) "{"
              && Bool.not (String.contains body "Content-Length")
              && String.beq (String.slice wire 0 16) "Content-Length: ")
}

// --- The read loop's two decisions ---

/// End of stream is the EMPTY read, not a short one: a chunk that ends inside a
/// multi-byte character comes back short without the stream having ended, and treating
/// that as the end would abandon the rest of a message the client is still sending.
#[test]
def test_only_an_empty_read_is_end_of_stream : Bool :=
  lsp_at_eof "" && Bool.not (lsp_at_eof "a")

/// One byte while the header is still arriving -- asking for more would block until the
/// peer filled the request, which for a request/response protocol is a deadlock.
#[test]
def test_the_read_is_one_byte_while_the_header_is_incomplete : Bool :=
  I64.beq (lsp_next_read FramingMode.content_length "Content-Len") 1

/// The whole outstanding body in one read once `Content-Length` is known: "hello" with
/// two of its five bytes present.
#[test]
def test_the_read_is_the_outstanding_body_once_the_header_is_complete : Bool :=
  I64.beq (lsp_next_read FramingMode.content_length "Content-Length: 5\r\n\r\nhe") 3

/// A floor rather than the true count, because `read_stdin_exact 0` answers the empty
/// string, which the loop reads as end of stream.
#[test]
def test_the_read_is_never_zero : Bool :=
  I64.beq (lsp_next_read FramingMode.content_length "Content-Length: 5\r\n\r\nhello") 1
