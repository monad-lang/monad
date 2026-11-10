/// The loop, the state it threads, and the routing that turns a message into a reply.
///
/// THE LOOP IS SYNCHRONOUS AND THERE IS NO DEBOUNCE, and that is a decision with two
/// reasons behind it rather than an omission. The first is that a fiber timer cannot
/// work here: under the Rust host fibers do not overlap by design
/// (`std/src/concurrent/combine_test.mo` records that the concurrency test "fails on
/// any implementation that serializes fibers"), `fork_io` is a deferred thunk and
/// `sleep_io` a blocking sleep, so a fiber that sleeps to debounce a keystroke blocks
/// the very thread that has to keep reading messages. The second is that the debounce
/// this server actually needs is cheaper and cannot be wrong: `documents.mo` compares
/// the incoming text against the buffer it holds, and a change that does not move the
/// text costs nothing further. Anything more elaborate would be a timer that is worse
/// than the comparison it replaced.
///
/// STDOUT CARRIES PROTOCOL FRAMES AND NOTHING ELSE. This is the one invariant the
/// whole file is written around, and it is why every log line goes through the
/// session's `Logger`, whose one sink (`lsp_log_sink`) writes `IO.write_stderr`,
/// rather than through a print of its own. The check path this server drives
/// prints eagerly to stdout in `lang`'s loaders, so a path that reached one of
/// those with verbose output on would write a diagnostic into the middle of the
/// protocol stream, and the client's complaint would be about a malformed frame
/// rather than about the print. So the check is driven with `verbose := false`
/// throughout (see `checks.mo`), and anything this file wants to say it says on
/// fd 2.
///
/// TWO DIFFERENT READS, AND THE DIFFERENCE IS A SYSCALL PER BYTE OF EVERY MESSAGE.
/// `IO.read_stdin_exact` answers a short read only at end of stream, so a caller
/// cannot simply ask for a large chunk and take what arrives -- it would block until
/// the chunk filled, which for a request/response protocol is a deadlock. What it CAN
/// do is ask for exactly the number of bytes the frame still needs, and
/// `framing_needed` is what answers that: while the header is still incomplete the
/// count is unknown and the reader takes one byte, and the moment `Content-Length` is
/// in hand it takes the body in a single read. So a message costs one read per header
/// byte plus one for the body, instead of one read per byte of everything.
///
/// END OF STREAM IS NOT AN ERROR. A client that closes the pipe -- an editor the user
/// quit, an editor that crashed -- has nothing left for this server to do, and a
/// server that exits non-zero because its peer went away turns every editor crash
/// into a failing build step. The one non-zero exit in the whole loop is the
/// specification's own: `exit` WITHOUT a preceding `shutdown` is a client that did not
/// get what it asked for, and it exits 1.
///
/// A MALFORMED FRAME DOES NOT END THE LOOP. The frame is answered with
/// `rpc_code_parse_error` and a null id, the buffer is dropped, and the stream is
/// resynchronized by consuming it one byte at a time -- which is the only resync
/// available, since a frame whose header could not be read does not say how long its
/// body is. A broken peer therefore spins the loop and terminates at end of stream,
/// while a well-behaved one never takes this path at all.
use json::json {Json}
use lang::module {ranged_file_diagnostics}
use lsp::checks {
    Check, CheckStore, check_result, checkstore_close, checkstore_empty, checkstore_lookup,
    checkstore_recheck,
}
use lsp::diagnostics {lsp_clear_notification, lsp_publish_notification}
use lsp::formatting {lsp_formatting}
use lsp::documents {
    DocumentEdit, document_change, document_close, document_edit_changed, document_edit_store,
    document_edit_uri, document_open, document_uri,
}
use lsp::lifecycle {
    lsp_choose_encoding, lsp_initialize_result, lsp_no_encodings, lsp_offered_encodings,
    lsp_root_path,
}
use log::level {LogLevel}
use log::logger {Logger, Logger.debug, Logger.error, Logger.info, Logger.with_sink}
use lsp::navigation {lsp_definition, lsp_document_symbol, lsp_hover, lsp_workspace_symbol}
use lsp::params {lsp_param_str}
use std::bench {Bench.now, Bench.since}
use std::list {}
use toolkit::docstore {DocStore, docstore_empty, docstore_text, docstore_version}
use toolkit::framing {
    FramingMode, bad_header, frame, framing_needed, framing_read, need_more,
}
use toolkit::jsonrpc {
    RpcMessage, rpc_code_method_not_found, rpc_code_parse_error, rpc_encode_error,
    rpc_encode_error_no_id, rpc_encode_result, rpc_object, rpc_parse,
}
use toolkit::position {PositionEncoding, position_encoding_name}

// --- The state ---

/// Everything the loop carries from one message to the next.
///
/// The two stores are separate because they have different lifetimes and the
/// difference is load-bearing: `docs` is what the client has open, and `checks` holds
/// a warm `ModuleInfoCache` that outlives any one document -- `checkstore_close` drops
/// a document's check and keeps the cache it warmed, deliberately, because the cache
/// is the loaded closure of the project rather than anything about a document.
///
/// `encoding` is fixed at `initialize` and never negotiated again, because the client
/// picks its encoding in the handshake and a server that changed it mid-session would
/// move every position after a non-ASCII character without either side noticing.
///
/// `initialized` is the handshake's second half and it is load-bearing for one rule:
/// a request that arrives before `initialize` is answered with
/// `rpc_code_server_not_initialized`, which is what the specification says and what
/// stops a confused client from being served from a state that was never negotiated.
/// `shutdown` is only ever read to decide the exit code.
///
/// `logger` filters at the level the client last set with `$/setTrace`, and it is
/// carried in the state because the setting outlives any one message: a server that logged at
/// a fixed level could not be quieted by a client that finds the log noisy, and one
/// that read it from the message would forget it on the next frame. stderr is the
/// only place anything is written, never stdout, which is the protocol channel.
pub struct ServerState {
    docs : DocStore,
    checks : CheckStore,
    encoding : PositionEncoding,
    root : Option String,
    initialized : Bool,
    shutdown : Bool,
    logger : Logger,
}

/// A fresh server: no documents, no checks, the default encoding, no root, and
/// neither half of the handshake done.
///
/// The encoding starts at whatever `lsp_choose_encoding` answers for a client that
/// offered nothing, which is the same value a client that offered nothing would get
/// -- so the state before `initialize` is the same shape as the state after a
/// pre-3.17 handshake rather than a third, invented one.
def lsp_server_new : ServerState :=
    ServerState.mk docstore_empty checkstore_empty lsp_default_encoding lsp_no_root false false
    (lsp_logger lsp_default_log_level)

def lsp_default_encoding : PositionEncoding := lsp_choose_encoding lsp_no_encodings

/// The empty root, as a named def: `Option.none` in a field position has to infer its
/// element type, and this repository's `Map.empty` bug is the recorded case of that
/// inference going wrong somewhere other than where it was written.
def lsp_no_root : Option String := Option.none

pub def server_docs (st : ServerState) : DocStore := st.docs

pub def server_checks (st : ServerState) : CheckStore := st.checks

pub def server_encoding (st : ServerState) : PositionEncoding := st.encoding

pub def server_root (st : ServerState) : Option String := st.root

pub def server_initialized (st : ServerState) : Bool := st.initialized

pub def server_shutdown (st : ServerState) : Bool := st.shutdown

pub def server_logger (st : ServerState) : Logger := st.logger

/// The server's log: stderr only, each line prefixed `monad-lsp: ` so an editor's
/// captured log names the process when several servers share one stderr.
pub def lsp_logger (level : LogLevel) : Logger := Logger.with_sink level lsp_log_sink

def lsp_log_sink (line : String) : IO Unit := IO.write_stderr ("monad-lsp: " ++ line)

/// A session logs its requests and document traffic until a client says otherwise:
/// most questions about a live session are asked after the fact.
def lsp_default_log_level : LogLevel := LogLevel.info

/// The minimum level a `$/setTrace` value names. `off` still writes errors; `messages`
/// is info and `verbose` is debug. A value the specification does not name is `off`:
/// a client that reached for the knob and missed is asking for less log.
pub def lsp_trace_level (value : String) : LogLevel :=
    if String.beq value "messages"
    then LogLevel.info
    else if String.beq value "verbose"
    then LogLevel.debug
    else LogLevel.error

/// The state after `$/setTrace`: everything the session negotiated, and a new level.
def lsp_server_traced (st : ServerState) (level : LogLevel) : ServerState :=
    ServerState.mk st.docs st.checks st.encoding st.root st.initialized st.shutdown (lsp_logger level)

/// The state after a document edit: new buffers, and the checks that go with them.
def lsp_server_edited (st : ServerState) (docs : DocStore) (checks : CheckStore) : ServerState :=
    ServerState.mk docs checks st.encoding st.root st.initialized st.shutdown st.logger

/// The state after `initialize`: the negotiated encoding, the workspace root, and the
/// first half of the handshake done.
def lsp_server_started (st : ServerState) (root : Option String) (enc : PositionEncoding)
    : ServerState :=
    ServerState.mk st.docs st.checks enc root st.initialized st.shutdown st.logger

/// The state after the `initialized` notification.
def lsp_server_ready (st : ServerState) : ServerState :=
    ServerState.mk st.docs st.checks st.encoding st.root true st.shutdown st.logger

/// The state after `shutdown`.
def lsp_server_marked_shutdown (st : ServerState) : ServerState :=
    ServerState.mk st.docs st.checks st.encoding st.root st.initialized true st.logger

// --- One step of the loop ---

/// What handling one message produced: the state to carry on with, the message bodies
/// to write to stdout, and the exit code if this message ended the session.
///
/// THE BODIES ARE RETURNED RATHER THAN WRITTEN so that the decision and the delivery
/// are separable -- the tests in `src/tests/server_tests.mo` assert on the exact bytes
/// a message is answered with, which a handler that wrote them itself could not offer.
/// `exit_code` being `Option I64` rather than a sentinel is the same idea: a step that
/// does not end the session says so, and no exit code is a legal exit code.
///
/// THEY ARE BODIES AND NOT FRAMES, which is a distinction this field's old name blurred
/// to the point of a real defect: each one is JSON that still needs its `Content-Length`
/// header, and for a while none of them got one, so the server answered every message
/// with bytes no client can parse. The header is added in exactly one place,
/// `lsp_write_frames`, which is also the only place any byte reaches stdout. Framing at
/// the call sites instead would be twenty-odd chances to forget it, and a server that
/// forgot on one of them would look to a client exactly like a server that had hung.
pub struct ServerStep {
    state : ServerState,
    bodies : List String,
    exit_code : Option I64,
}

pub def server_step_state (s : ServerStep) : ServerState := s.state

pub def server_step_bodies (s : ServerStep) : List String := s.bodies

pub def server_step_exit (s : ServerStep) : Option I64 := s.exit_code

/// Continue with the same state and say nothing.
def lsp_step_quiet (st : ServerState) : ServerStep :=
    ServerStep.mk st lsp_no_bodies lsp_no_exit

/// Continue with the state a document edit left behind.
def lsp_step_edited (st : ServerState) (docs : DocStore) (checks : CheckStore) : ServerStep :=
    ServerStep.mk (lsp_server_edited st docs checks) lsp_no_bodies lsp_no_exit

/// Continue with edited state, having said one thing.
def lsp_step_says (st : ServerState) (docs : DocStore) (checks : CheckStore) (body : String)
    : ServerStep :=
    ServerStep.mk (lsp_server_edited st docs checks) (List.cons body lsp_no_bodies) lsp_no_exit

/// Continue with the same state, having said one thing.
def lsp_step_reply (st : ServerState) (body : String) : ServerStep :=
    ServerStep.mk st (List.cons body lsp_no_bodies) lsp_no_exit

/// End the session. The state is carried out with the code so a caller can still see
/// what it was serving, which is what a test asserting on the exit path wants.
def lsp_step_exit (st : ServerState) (code : I64) : ServerStep :=
    ServerStep.mk st lsp_no_bodies (Option.some code)

/// The empty body list, named for the `Map.empty` reason.
def lsp_no_bodies : List String := List.empty

/// No exit code, for the same reason.
def lsp_no_exit : Option I64 := Option.none

// --- Dispatch ---

/// Handle one parsed message.
///
/// The three message shapes that are not a request or a notification are handled here
/// rather than falling through to the routers, and each for its own reason: an
/// `unparseable` message gets the specification's parse error and a null id, because
/// there is nothing to answer; a `response` is a protocol violation (this server never
/// sends a request) and is logged and dropped, since answering a response is what
/// would actually confuse the peer; a `failure` cannot be built by `rpc_parse` at all
/// and is handled so that the case is not silently unhandled.
#[partial]
pub def lsp_dispatch (st : ServerState) (m : RpcMessage) : IO ServerStep :=
    match m {
        RpcMessage.unparseable reason => do {
            Logger.error (server_logger st) ("unreadable message: " ++ reason);
            return (lsp_step_reply st (rpc_encode_error_no_id rpc_code_parse_error reason))
        },
        RpcMessage.response _id _result => do {
            Logger.error (server_logger st) "ignoring a response the client sent";
            return (lsp_step_quiet st)
        },
        RpcMessage.failure _id _code _message => do {
            Logger.error (server_logger st) "ignoring a failure message the client sent";
            return (lsp_step_quiet st)
        },
        RpcMessage.request id method params => do {
            lsp_log_request st id method;
            lsp_request st id method params
        },
        RpcMessage.notification method params => do {
            lsp_log_notification st method params;
            lsp_notification st method params
        },
    }

// --- Trace logging ---

/// Say that a request arrived, at the level the client last set. The id is in the line
/// because a client that sends requests concurrently interleaves the replies, and a
/// log line that cannot be paired with its reply is a log line that cannot answer
/// "which request did this come from".
#[partial]
def lsp_log_request (st : ServerState) (id : Json) (method : String) : IO Unit :=
    Logger.info (server_logger st) ("request " ++ method ++ " (id " ++ Json.to_string id ++ ")")

/// Say that a notification arrived. `$/`-prefixed notifications are protocol plumbing
/// (keepalives, cancelations) and are logged only at verbose; the rest are the
/// document-sync traffic that a session's timeline is made of, and carry the document
/// uri when there is one so the line names what changed.
#[partial]
def lsp_log_notification (st : ServerState) (method : String) (params : Option Json) : IO Unit :=
    if String.starts_with "$/" method
    then Logger.debug (server_logger st) ("notification " ++ method)
    else Logger.info (server_logger st)
        ("notification " ++ method ++ lsp_notification_where params)

/// The ` params.uri` suffix of a notification log line, or nothing when the message
/// carries no uri -- `exit` and `$/setTrace` arrive bare, and a line that said
/// "notification exit " would be noise, not information.
#[partial]
def lsp_notification_where (params : Option Json) : String :=
    match document_uri (lsp_params_or_empty params) {
        Option.none => "",
        Option.some uri => " " ++ uri,
    }

/// The trace level named by a `$/setTrace` message's `value`, or `off` when the value
/// is missing or not one of the specification's three names -- a level the server
/// cannot understand is a level it must not guess at.
#[partial]
def lsp_trace_of_params (params : Option Json) : LogLevel :=
    match lsp_param_str "value" (lsp_params_or_empty params) {
        Option.none => LogLevel.error,
        Option.some value => lsp_trace_level value,
    }

/// `$/setTrace`: remember the level, say nothing. The reply to a notification would be
/// a protocol violation, so the level change is the whole of the handling. The `do` is
/// the same adapter `lsp_step_quiet_io` is: the notification router speaks `IO
/// ServerStep` and this step is computed rather than run.
#[partial]
def lsp_set_trace (st : ServerState) (params : Option Json) : IO ServerStep := do {
    return (lsp_step_quiet (lsp_server_traced st (lsp_trace_of_params params)))
}

/// The root as a log line can show it, `Option String` and all.
#[partial]
def lsp_root_show (root : Option String) : String :=
    match root {
        Option.none => "(none)",
        Option.some path => path,
    }

/// Say what a message was and how long handling it took, at verbose only: the timing
/// line is for a session being diagnosed, and a session being diagnosed is one where
/// the client has already asked for everything the server can say.
#[partial]
def lsp_log_frame (st : ServerState) (m : RpcMessage) (ms : I64) : IO Unit :=
    match m {
        RpcMessage.request _id method _params =>
            Logger.debug (server_logger st) (method ++ " in " ++ I64.to_string ms ++ "ms"),
        RpcMessage.notification method _params =>
            Logger.debug (server_logger st) (method ++ " in " ++ I64.to_string ms ++ "ms"),
        _ => IO.pure Unit.unit,
    }

/// The request router.
///
/// The handshake gate is here and not in `lsp_dispatch` because the rule is about
/// REQUESTS: the specification says a request before `initialize` is answered
/// `ServerNotInitialized`, while notifications that arrive early are ignored rather
/// than answered -- `exit` above all, which a client that never initialized may still
/// send and which must never be refused.
#[partial]
def lsp_request (st : ServerState) (id : Json) (method : String) (params : Option Json)
    : IO ServerStep :=
    if String.beq method "initialize"
    then lsp_initialize st id params
    else if server_initialized st
    then lsp_request_ready st id method params
    else lsp_not_initialized st id method

/// The request router, for a session that has completed the handshake.
#[partial]
def lsp_request_ready (st : ServerState) (id : Json) (method : String) (params : Option Json)
    : IO ServerStep :=
    if String.beq method "shutdown" then lsp_shutdown st id
    else if String.beq method "textDocument/hover" then lsp_hover_request st id params
    else if String.beq method "textDocument/definition" then lsp_definition_request st id params
    else if String.beq method "textDocument/documentSymbol" then lsp_symbols_request st id params
    else if String.beq method "workspace/symbol" then lsp_workspace_request st id params
    else if String.beq method "textDocument/formatting" then lsp_formatting_request st id params
    else lsp_unknown_request st id method

// --- The handshake ---

/// `initialize`: negotiate the encoding, read the root, advertise what exists.
///
/// The negotiation happens HERE rather than being deferred to the first request that
/// needs it, because the answer has to be in the reply: `positionEncoding` tells the
/// client which encoding the server will speak, and a client that is not told assumes
/// utf-16. Storing it and answering with it is also why `lsp_initialize_result` takes
/// the encoding as an argument rather than choosing one itself -- there is exactly one
/// place the choice is made.
#[partial]
def lsp_initialize (st : ServerState) (id : Json) (params : Option Json) : IO ServerStep := do {
    let p : Json := lsp_params_or_empty params;
    let enc : PositionEncoding := lsp_choose_encoding (lsp_offered_encodings p);
    Logger.info (server_logger st)
        ("initialize: encoding " ++ position_encoding_name enc
            ++ ", root " ++ lsp_root_show (lsp_root_path p));
    return (lsp_step_reply (lsp_server_started st (lsp_root_path p) enc)
        (rpc_encode_result id (lsp_initialize_result enc)))
}

/// `shutdown`: stop accepting work, answer null, and stay alive until `exit`.
///
/// The two-message ending is the specification's, and the reason it is two is worth
/// keeping rather than collapsing: `shutdown` says the client is done and expects
/// nothing further, and `exit` says the process may go. A server that exited on
/// `shutdown` would take the stream away from a client that still had a reply in
/// flight.
#[partial]
def lsp_shutdown (st : ServerState) (id : Json) : IO ServerStep := do {
    return (lsp_step_reply (lsp_server_marked_shutdown st) (rpc_encode_result id Json.make_null))
}

/// A request before `initialize`, which the specification answers with -32002.
///
/// It gets a reply rather than a log line because a client is entitled to an answer
/// for every request it sends, and the id it sent back is the whole point: a client
/// that receives no answer waits forever.
#[partial]
def lsp_not_initialized (st : ServerState) (id : Json) (method : String) : IO ServerStep := do {
    Logger.error (server_logger st) ("request before initialize: " ++ method);
    return (lsp_step_reply st
        (rpc_encode_error id lsp_code_not_initialized
            ("server not initialized: " ++ method)))
}

/// -32002, `ServerNotInitialized`.
///
/// Spelled out here rather than in `toolkit::jsonrpc` because it is the only code this
/// server uses that the toolkit does not: the four in `jsonrpc` are the transport's own
/// error codes, and this one is LSP's. Putting it beside them would invite the next
/// protocol's lifecycle code into a module that is deliberately protocol-independent.
def lsp_code_not_initialized : I64 := 0 - 32002

/// A request this server does not implement.
///
/// `method_not_found` rather than silence: an unanswered request hangs the client, and
/// a client that asked for `textDocument/completion` deserves to be told the feature is
/// absent rather than to wait for a popup that will never open. The method name is
/// logged, so a session that hits this leaves a record of what was asked for.
#[partial]
def lsp_unknown_request (st : ServerState) (id : Json) (method : String) : IO ServerStep := do {
    Logger.error (server_logger st) ("unknown request: " ++ method);
    return (lsp_step_reply st
        (rpc_encode_error id rpc_code_method_not_found ("unknown method: " ++ method)))
}

// --- Notifications ---

/// The notification router.
///
/// THE LAST ARM IS THE POINT: a notification has no reply, so an unrecognized one
/// cannot be reported to the sender and the only correct thing to do with it is
/// nothing. Everything named before the last arm is a method this server acts on; the
/// three `$/`-prefixed and configuration methods are named explicitly rather than
/// swept into the fallback, so that the log line for a genuinely unknown method means
/// something.
#[partial]
def lsp_notification (st : ServerState) (method : String) (params : Option Json) : IO ServerStep :=
    if String.beq method "initialized" then lsp_initialized st
    else if String.beq method "exit" then lsp_exit st
    else if String.beq method "textDocument/didOpen" then lsp_did_open st params
    else if String.beq method "textDocument/didChange" then lsp_did_change st params
    else if String.beq method "textDocument/didClose" then lsp_did_close st params
    else if String.beq method "textDocument/didSave" then lsp_did_save st params
    else if String.beq method "$/cancelRequest" then lsp_step_quiet_io st
    else if String.beq method "$/setTrace" then lsp_set_trace st params
    else if String.beq method "workspace/didChangeConfiguration" then lsp_step_quiet_io st
    else lsp_unknown_notification st method

/// `initialized`: the handshake's second half, which carries no payload and asks for
/// nothing.
#[partial]
def lsp_initialized (st : ServerState) : IO ServerStep := do {
    return (lsp_step_quiet (lsp_server_ready st))
}

/// `exit`: end the session, with the exit code the specification gives it.
///
/// Non-zero without a preceding `shutdown`, which is the one place this server
/// deliberately reports failure: a client that exits without asking first has skipped
/// the handshake that exists so both sides know the other is finished, and the code is
/// how a wrapper script finds out. The line is logged because `exit` is the last thing
/// a session says and a log that stops before it cannot show why the process ended.
#[partial]
def lsp_exit (st : ServerState) : IO ServerStep := do {
    let code : I64 := if server_shutdown st then 0 else 1;
    Logger.info (server_logger st) ("exit (code " ++ I64.to_string code ++ ")");
    return (lsp_step_exit st code)
}

/// A notification this server does not act on, which is most of them.
#[partial]
def lsp_unknown_notification (st : ServerState) (method : String) : IO ServerStep := do {
    Logger.error (server_logger st) ("ignoring notification: " ++ method);
    return (lsp_step_quiet st)
}

/// Say nothing, from a non-`do` position.
#[partial]
def lsp_step_quiet_io (st : ServerState) : IO ServerStep := do {
    return (lsp_step_quiet st)
}

// --- The document notifications ---

/// `didOpen`: record the buffer and check it.
#[partial]
def lsp_did_open (st : ServerState) (params : Option Json) : IO ServerStep :=
    lsp_open_params st (lsp_params_or_empty params)

/// The body of `didOpen`, with the params normalized before the match.
///
/// THE SPLIT IS NOT COSMETIC. A `do` block whose first statement is a `let` and whose
/// last is a `match` cannot have a trailing comma after that match -- the parser takes
/// it as the end of the block and fails on the following brace -- and this file's
/// handlers all used to have that shape. Lifting the params read into the caller leaves
/// each handler a `def` whose BODY is the match, which is the shape `checkstore_recheck`
/// and `lsp_write_frames` already use and the one this parser is happy with.
#[partial]
def lsp_open_params (st : ServerState) (p : Json) : IO ServerStep :=
    match document_open p (server_docs st) {
        Option.none => lsp_log_quiet st "malformed didOpen",
        Option.some e => lsp_after_edit st e,
    }

/// `didChange`: record the buffer, and check it only if the text moved.
#[partial]
def lsp_did_change (st : ServerState) (params : Option Json) : IO ServerStep :=
    lsp_change_params st (lsp_params_or_empty params)

#[partial]
def lsp_change_params (st : ServerState) (p : Json) : IO ServerStep :=
    match document_change p (server_docs st) {
        Option.none => lsp_log_quiet st "malformed didChange",
        Option.some e => lsp_after_edit st e,
    }

/// `didClose`: forget the document, clear its markers, and keep the warm cache.
///
/// The clear is published HERE and not left to the client, because a client keeps the
/// last set of diagnostics it was sent: a document closed with three squiggles in it
/// would leave those squiggles in the problems list of a file that is no longer open,
/// and nothing would ever remove them.
#[partial]
def lsp_did_close (st : ServerState) (params : Option Json) : IO ServerStep :=
    lsp_close_params st (lsp_params_or_empty params)

#[partial]
def lsp_close_params (st : ServerState) (p : Json) : IO ServerStep :=
    match document_close p (server_docs st) {
        Option.none => lsp_log_quiet st "malformed didClose",
        Option.some e => lsp_close_edit st e,
    }

#[partial]
def lsp_close_edit (st : ServerState) (e : DocumentEdit) : IO ServerStep := do {
    let uri : String := document_edit_uri e;
    let checks : CheckStore := checkstore_close uri (server_checks st);
    return (lsp_step_says st (document_edit_store e) checks (lsp_clear_notification uri))
}

/// `didSave`: publish the current diagnostics again.
///
/// NOT A RECHECK, and the difference is worth stating because the call looks like one.
/// The buffer this server holds is the text the client last sent, so a save cannot
/// change it, and `checkstore_recheck` short-circuits to the store it was given. What
/// the save DOES mean is that the user has reached a point they consider a result, so
/// the diagnostics are re-sent rather than left in whatever state the last edit left
/// them -- which is what makes a save a way to recover markers a client dropped.
#[partial]
def lsp_did_save (st : ServerState) (params : Option Json) : IO ServerStep :=
    lsp_save_params st (lsp_params_or_empty params)

#[partial]
def lsp_save_params (st : ServerState) (p : Json) : IO ServerStep :=
    match document_uri p {
        Option.none => lsp_log_quiet st "malformed didSave",
        Option.some uri => lsp_recheck_document st (server_docs st) uri,
    }

/// Say something on stderr, and answer nothing.
///
/// One def for the four malformed-notification paths, so that the answer to "the client
/// sent something this server could not read" is written once. It cannot be reported to
/// the client -- a notification has no reply -- so the log line is the whole of what
/// happens, and a crash from a malformed keystroke is the thing being avoided.
#[partial]
def lsp_log_quiet (st : ServerState) (msg : String) : IO ServerStep := do {
    Logger.error (server_logger st) msg;
    return (lsp_step_quiet st)
}

/// Act on a document edit: recheck when the text moved, and otherwise only record it.
///
/// The two arms are the whole debounce. A client sends a `didChange` for edits that
/// change nothing a checker can see, and `documents.mo` has already compared the
/// incoming text against the buffer it held -- so by the time this is reached the
/// question "is there anything to do" has been answered, and the expensive path is
/// taken only when the answer is yes.
#[partial]
def lsp_after_edit (st : ServerState) (e : DocumentEdit) : IO ServerStep :=
    if document_edit_changed e
    then lsp_recheck_document st (document_edit_store e) (document_edit_uri e)
    else lsp_step_edited_io st (document_edit_store e)

/// Record an edit that did not move the text.
#[partial]
def lsp_step_edited_io (st : ServerState) (docs : DocStore) : IO ServerStep := do {
    return (lsp_step_edited st docs (server_checks st))
}

/// Check a document if its text is not already covered, then publish what came of it.
#[partial]
def lsp_recheck_document (st : ServerState) (docs : DocStore) (uri : String) : IO ServerStep := do {
    match docstore_text uri docs {
        Option.none => return (lsp_step_edited st docs (server_checks st)),
        Option.some text => do {
            let checks <- checkstore_recheck uri text (server_checks st);
            let step <- lsp_publish_check st docs checks uri;
            return step
        },
    }
}

/// Publish the diagnostics for a document, from the check that covers it.
///
/// A document with no check publishes nothing. That is not a fallback: it means either
/// the URI names no file (so there was nothing to check) or the document was closed,
/// and in both cases the client holds no markers from this server that need clearing.
#[partial]
def lsp_publish_check (st : ServerState) (docs : DocStore) (checks : CheckStore) (uri : String)
    : IO ServerStep :=
    match checkstore_lookup uri checks {
        Option.none => lsp_step_edited_io st docs,
        Option.some ch => lsp_emit_diagnostics st docs checks uri ch,
    }

/// The publish itself: the notification an editor renders as squiggles.
///
/// The version comes from `docstore_version`, so it is the CLIENT's label for its own
/// text or nothing at all -- see `diagnostics.mo`, which is the module that decides
/// what to do about that. The count is logged at verbose because it is the one number
/// a session's log cannot do without: "published 0" after an edit is the difference
/// between a document that is clean and a check that never ran.
#[partial]
def lsp_emit_diagnostics (st : ServerState) (docs : DocStore) (checks : CheckStore)
    (uri : String) (ch : Check) : IO ServerStep := do {
    let frame : String :=
        lsp_publish_notification uri (docstore_version uri docs) (server_encoding st) ch;
    let n : I64 := List.length (ranged_file_diagnostics (check_result ch));
    Logger.debug (server_logger st)
        ("published " ++ I64.to_string n ++ " diagnostic(s) for " ++ uri);
    return (lsp_step_says st docs checks frame)
}

// --- The navigation requests ---
//
// Each of these is a thin adapter over `navigation.mo`, and the thinness is the
// point: which text a position is converted against, what a name resolves to, and
// what a range means are all decided there, so that a request handler here cannot
// decide them differently from the next one. What this file owns is the routing, the
// state, and the encoding.

#[partial]
def lsp_hover_request (st : ServerState) (id : Json) (params : Option Json) : IO ServerStep := do {
    let result : Json :=
        lsp_hover (server_checks st) (server_encoding st) (lsp_params_or_empty params);
    return (lsp_step_reply st (rpc_encode_result id result))
}

#[partial]
def lsp_definition_request (st : ServerState) (id : Json) (params : Option Json) : IO ServerStep := do {
    let result <- lsp_definition (server_checks st) (server_encoding st) (lsp_params_or_empty params);
    return (lsp_step_reply st (rpc_encode_result id result))
}

#[partial]
def lsp_symbols_request (st : ServerState) (id : Json) (params : Option Json) : IO ServerStep := do {
    let result : Json :=
        lsp_document_symbol (server_checks st) (server_encoding st) (lsp_params_or_empty params);
    return (lsp_step_reply st (rpc_encode_result id result))
}

/// `textDocument/formatting`. A buffer the formatter refuses (it does not lex) answers
/// null, which a client reads as "no edits", and the reason goes to the log.
#[partial]
def lsp_formatting_request (st : ServerState) (id : Json) (params : Option Json)
    : IO ServerStep :=
    match lsp_formatting (server_docs st) (server_encoding st) (lsp_params_or_empty params) {
        Result.ok edits => do { return (lsp_step_reply st (rpc_encode_result id edits)) },
        Result.err reason => do {
            Logger.info (server_logger st) reason;
            return (lsp_step_reply st (rpc_encode_result id Json.make_null))
        },
    }

/// `workspace/symbol`, which reads the document store as well as the check store.
///
/// The docstore is here because the scan prefers an open buffer to the file on disk --
/// see `navigation.mo`'s `lsp_file_text` -- and the root is the one this session
/// negotiated rather than anything per-request, since a symbol picker is about the
/// workspace the server was started for.
#[partial]
def lsp_workspace_request (st : ServerState) (id : Json) (params : Option Json) : IO ServerStep := do {
    let result <- lsp_workspace_symbol (server_docs st) (server_root st) (server_encoding st)
        (lsp_params_or_empty params);
    return (lsp_step_reply st (rpc_encode_result id result))
}

// --- Parameters ---

/// The params node, or an empty object when the client omitted it.
///
/// AN EMPTY OBJECT AND NOT `null`, which is a choice about which mistake is available.
/// Every reader in this mote goes through `toolkit::jsonrpc`'s `rpc_field`, so an
/// absent key and a key in an empty object are the same answer -- but a `null` params
/// node is a value some of those readers would have to be told about, and the one that
/// forgot would raise a type error rather than report an absent field. So the absent
/// case is normalized once, here, into the shape that reads the same as an omitted one.
///
/// The alternative -- threading `Option Json` into every handler -- was rejected for a
/// different reason: it would put the same three lines at the top of ten handlers, and
/// the one that forgot would be the one that crashed on a client that omits params,
/// which is legal for `initialize` and for every notification.
#[partial]
def lsp_params_or_empty (params : Option Json) : Json :=
    match params {
        Option.none => lsp_empty_params,
        Option.some j => j,
    }

/// An empty `params` object.
def lsp_empty_params : Json := rpc_object lsp_no_fields

/// The empty field list, named for the `Map.empty` reason.
def lsp_no_fields : List (Pair String Json) := List.empty

// --- The transport loop ---

/// How many bytes the reader asks for when the frame's size is not yet known.
///
/// One, and the number is not a tuning knob: `IO.read_stdin_exact` returns a short
/// result only at end of stream, so asking for a large chunk would block until the
/// chunk filled -- for a client that is waiting on the reply to the message it just
/// sent, that is a deadlock. The moment `Content-Length` has been read the reader stops
/// asking one byte at a time; see `lsp_next_read`.
def lsp_header_step : I64 := 1

/// How many bytes to read next: the frame's outstanding count when it is known, and
/// one byte while the header is still being read.
///
/// The floor is in `framing_needed` rather than here on purpose -- a zero there would
/// be a `read_stdin_exact 0`, whose empty result this loop reads as end of stream. What
/// this def adds is the unknown case, which `framing_needed` reports as `Option.none`
/// because a `newline_delimited` frame and an incomplete header have no declared size.
#[partial]
def lsp_next_read (mode : FramingMode) (buf : String) : I64 :=
    match framing_needed mode buf {
        Option.none => lsp_header_step,
        Option.some n => n,
    }

/// End of stream, as the empty read.
///
/// THE TEST IS EMPTINESS AND NOT SHORTNESS, which is subtler than it looks. The
/// native's contract makes a short read mean end of stream, but the result it hands
/// over is a `String`, and a chunk that ends in the middle of a multi-byte character
/// comes back one to three bytes shorter than was read -- the native holds those bytes
/// for the next call rather than handing over an invalid character. So a short
/// non-empty result can be a full read with a character straddling the boundary, and
/// treating it as end of stream would abandon the rest of a message the client is
/// still sending. Only an empty result is unambiguous, and the carry makes it so: the
/// next read starts with the bytes that were held back.
#[partial]
def lsp_at_eof (chunk : String) : Bool :=
    String.is_empty chunk

/// One frame, as the bytes to write.
///
/// `String.length` is BYTE length in both backends, which is what makes this one line
/// correct: `Content-Length` counts bytes of the encoded body, and a server that used
/// a character count would understate every frame containing a non-ASCII character --
/// this corpus's comments are full of em dashes -- and the client would read the next
/// frame starting inside this one.
#[partial]
pub def lsp_frame (body : String) : String :=
    "Content-Length: " ++ I64.to_string (String.length body) ++ "\r\n\r\n" ++ body

/// Write every message BODY, framed, in order, and no flush.
///
/// THIS IS WHERE THE `Content-Length` HEADER IS ADDED, and it is the only place any byte
/// is written to stdout at all -- one `IO.write_stdout` call site, for one reason: a
/// frame whose header each caller had to remember is a frame with twenty ways to be
/// wrong and nothing to catch it from the inside. Here the composition is the only path
/// a body can take to the wire.
///
/// The flush is the caller's, and it is separate because it must happen ONCE per
/// message rather than once per body: a message that produces two notifications (a
/// clear and a publish, say) should reach the client as one write's worth of bytes,
/// and a flush between them would show the client half a reply.
#[partial]
def lsp_write_frames (bs : List String) : IO Unit :=
    match bs {
        List.empty => IO.pure Unit.unit,
        List.cons b rest => do {
            IO.write_stdout (lsp_frame b);
            lsp_write_frames rest
        }
    }

/// The session loop: one frame in, whatever it produced out, and then again.
///
/// The exit code is the loop's result, so the three ways out are visible in one place:
/// end of stream (0), the `exit` notification (its code), and the `bad_header` path
/// (which does not exit at all -- see the module doc).
///
/// THE FRAME ARM TIMES THE DISPATCH, with one clock reading on each side, so that a
/// slow session can be read from its own log: which message took how long is the
/// first question about a server that hangs or lags, and the answer has to be
/// gathered while the message is being handled, not reconstructed afterwards. The
/// readings are `IO` and bound in order, which is the discipline `Bench.now`'s type
/// exists to enforce.
#[partial]
pub def lsp_loop (st : ServerState) (buf : String) : IO I64 := do {
    match framing_read FramingMode.content_length buf {
        FrameRead.need_more => do {
            let k : I64 := lsp_next_read FramingMode.content_length buf;
            let chunk <- IO.read_stdin_exact k;
            if lsp_at_eof chunk
            then do {
                Logger.info (server_logger st) "end of input";
                return lsp_eof_code
            }
            else lsp_loop st (buf ++ chunk)
        },
        FrameRead.bad_header reason => do {
            Logger.error (server_logger st) ("bad frame: " ++ reason);
            let body : String := rpc_encode_error_no_id rpc_code_parse_error reason;
            lsp_write_frames (List.cons body lsp_no_bodies);
            IO.flush_stdout;
            lsp_loop st ""
        },
        FrameRead.frame body rest => do {
            let m : RpcMessage := rpc_parse body;
            let started : I64 <- Bench.now;
            let step <- lsp_dispatch st m;
            let elapsed : I64 <- Bench.since started;
            lsp_log_frame st m elapsed;
            lsp_write_frames (server_step_bodies step);
            IO.flush_stdout;
            lsp_after_step rest step
        },
    }
}

/// Carry on after a handled message: recurse, or return the exit code it asked for.
///
/// A separate def rather than a `match` inside the loop's arm, for the reason
/// `lsp_open_params` gives: a nested `match` statement in an arm's `do` block cannot be
/// followed by a comma, and the one that ends the block needs the comma removed -- which
/// is easy to get wrong and hard to see. Hoisting it makes the loop's arms read as the
/// three plain things they are.
#[partial]
def lsp_after_step (rest : String) (step : ServerStep) : IO I64 :=
    match server_step_exit step {
        Option.some code => lsp_pure_code code,
        Option.none => lsp_loop (server_step_state step) rest,
    }

/// An `IO I64` that is just a value, so the exit arm above needs no `do` block.
#[partial]
def lsp_pure_code (code : I64) : IO I64 := IO.pure code

/// The code to exit with when the client simply went away.
///
/// Zero, whether or not the handshake got as far as `shutdown`, and the reason is which
/// failure this code is for. A client that closes the stream is finished with this
/// server; it may have crashed, it may have been killed, and in neither case is a
/// non-zero status from the server useful information for whoever reads it -- while a
/// wrapper script that treats it as a build failure is a real cost. The one dishonest
/// exit the specification distinguishes is `exit` without `shutdown`, and that is
/// answered on its own path in `lsp_exit`. `server_shutdown` is deliberately not
/// consulted: the state it would report says what the client did, and this code says
/// what this server thinks of it.
def lsp_eof_code : I64 := 0

/// Run a session on stdin and stdout.
#[partial]
pub def lsp_serve : IO I64 := lsp_loop lsp_server_new ""
