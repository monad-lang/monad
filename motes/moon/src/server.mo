/// HTTP/1.1 server — `moon` mote, Layer 1 (sequential).
///
/// Listens on a port, accepts connections one at a time, parses each
/// request, dispatches to a handler, formats the response, and closes.
/// Concurrency (fiber-per-request) is Phase 7; the sequential server here
/// keeps a connection open between requests and serves a pipelined request
/// out of the bytes the previous read left behind.
///
/// Three API styles:
///
///   Production:  `Server.serve handler port` — infinite accept loop.
///                Never returns. One connection at a time, kept alive.
///
///   Connection:  `Server.serve_connection handler sock carry served` —
///                serve one socket until it must end. This is the loop the
///                accept loop runs, and the one tests exercise directly when
///                they need more than one request on a connection.
///
///   Testing:     `Server.handle_connection handler sock` — read exactly one
///                request, respond, close. Tests interleave client-side writes
///                and reads around this call in the same thread, which only
///                terminates if it stops after the one request.
///
/// Static file serving: `Server.static root` returns a handler that reads
/// files from `root` + request path; `static_files.mo` owns the traversal
/// guard, MIME type, ETag and range handling.
///
/// The read timeout is a known gap: a peer that opens a connection and then
/// says nothing holds it until it closes. `Server.max_keep_alive_requests`
/// bounds how many requests one connection may serve, which is a different
/// thing -- it stops a *talking* client from holding the connection forever,
/// not a silent one. A real fix means a socket read deadline, which the IO
/// layer does not expose yet.

use std::concurrent::fiber {
    Fiber, FiberError, FiberError.message, await_fiber, cancel_fiber, forkIO,
    pollFiber,
}
use std::concurrent::combine {sleepIO}
use std::list {}
use std::ref {Ref, Ref.get, Ref.new, Ref.set, Ref.update}
use std::stream {Stream, FdStream, FdStream.set_timeout}
use http::types {
    Transport, Transport.close, Transport.read_bytes, Transport.wait_read,
    Transport.write_bytes, Body, Body.is_stream, Framing, Headers, Headers.get,
    Headers.get_all, Method, Request, Response, Status.bad_request,
    Status.expectation_failed, Status.internal_server_error, Status.not_found,
    Status.payload_too_large, Status.request_header_fields_too_large,
    Status.request_timeout, http1_0, http1_1,
}
use http::strings {Strings.drop_bytes, Strings.parse_i64, Strings.split_on}
use http::wire {
    Wire.chunk_step, Wire.concat_chunks, Wire.continue_response, Wire.find_body_start,
    Wire.format_response, Wire.format_response_head, Wire.frame_request,
    Wire.head_headers, Wire.parse_request, Wire.parse_request_head_strict,
    Wire.request_framing, Wire.response_has_body, Wire.response_head_chunked,
    Wire.take_bytes,
}
use lib::handler {Handler.try}
use lib::handler_t {HandlerT, HandlerT.run_io, HttpError, HttpError.to_response}
use http::body_io {Body.write_chunked}
use lib::static_files {Static.handler, StaticConfig, StaticConfig.default}

// ── socket bytes ────────────────────────────────────────────────────────

/// One read of at most `max` bytes, as a list (`Transport.read_bytes`
/// over a bare socket).
def Server.read_bytes (sock : FdStream) (max : I64) : IO (Result String (List U8)) :=
    let t : Transport := Transport.plain sock in
    Transport.read_bytes t max

/// Write all of `bytes` (`Transport.write_bytes` over a bare socket).
def Server.write_bytes (sock : FdStream) (bytes : List U8) : IO (Result String U64) :=
    let t : Transport := Transport.plain sock in
    Transport.write_bytes t bytes

// ── error responses ─────────────────────────────────────────────────────

def Server.bad_request_response : Response :=
    { status := Status.bad_request, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Bad Request" }

def Server.not_found_response : Response :=
    { status := Status.not_found, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Not Found" }

def Server.internal_error_response : Response :=
    { status := Status.internal_server_error, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Internal Server Error" }

/// Serialise a response the server builds itself. These bodies are `Body.text`,
/// which always serialises, so the fallback is unreachable -- but a total
/// function has to answer something, and a bodiless 500 is a better answer
/// than no bytes, which would leave the peer waiting until it gave up.
def Server.canned_bytes (res : Response) : List U8 :=
    match Wire.format_response (Server.with_connection_header true res) {
        Result.ok bytes => bytes,
        Result.err _ => String.to_list "HTTP/1.1 500 \r\ncontent-length: 0\r\nconnection: close\r\n\r\n"
    }

// ── reading one request ─────────────────────────────────────────────────
//
// Reading is frame-first: bytes are buffered until `Wire.frame_request` can
// read a `Content-Length` off the head and see that many body bytes, and only
// then is a message returned. The buffer is never truncated, because what is
// left over after a frame is a pipelined request rather than garbage.

/// Read one whole message: buffer from `sock` until `frame_of` sees a complete
/// message in the buffer, then return it along with the remainder.
///
/// `frame_of` is the framing rule -- `Wire.frame_request` for a request,
/// `Wire.frame_response bytes method` for a response -- so the loop is written
/// once and a message is "what the framing says", not "what a particular
/// reader guessed". It answers `ok none` while more bytes are needed and `err`
/// when the buffer cannot be framed at all.
///
/// `Ok Option.none` means the peer closed without starting a message: the end
/// of the connection, and not an error. EOF *inside* a message is an error --
/// reporting a half-arrived message as a complete one is how a truncated
/// request becomes a successful parse, and it is checked below.
#[terminating]
def Server.read_message (frame_of : List U8 -> Result String (Option I64)) (sock : FdStream) (carry : List U8) : IO (Result String (Option (Pair (List U8) (List U8)))) := do {
    let frame : Result String (Option I64) := frame_of carry;
    match frame {
        Result.err e => return (Result.err e),
        Result.ok opt =>
            match opt {
                Option.some n => return (Result.ok (Option.some (Pair.pair (Wire.take_bytes n carry) (Strings.drop_bytes n carry)))),
                Option.none => do {
                    let read_res <- Server.read_bytes sock 4096;
                    Server.read_message_step frame_of sock carry read_res
                }
            }
    }
}

/// One read result, while the message is still incomplete.
#[terminating]
def Server.read_message_step (frame_of : List U8 -> Result String (Option I64)) (sock : FdStream) (carry : List U8) (read_res : Result String (List U8)) : IO (Result String (Option (Pair (List U8) (List U8)))) :=
    match read_res {
        Result.err e => return (Result.err e),
        Result.ok chunk =>
            if List.is_empty chunk
            then
                // The peer closed. With nothing buffered that ends the connection;
                // with an unfinished message in hand it is a truncation, and it must
                // not be handed on as a short message.
                if List.is_empty carry
                then return (Result.ok Option.none)
                else return (Result.err "connection closed mid-message")
            else Server.read_message frame_of sock (List.append carry chunk)
    }

/// Read one whole request. The framing rule is `Wire.frame_request`, so a
/// request body ends at its `Content-Length` and whatever follows it is kept
/// for the next message rather than being read as part of this one.
///
/// The caps are enforced before every read: a peer cannot make the server
/// buffer an unbounded header block or body. `Content-Length` is checked as
/// soon as the headers are complete, so an oversized declared body is
/// rejected without waiting for its bytes.
def Server.read_request (sock : FdStream) (carry : List U8) : IO (Result String (Option (Pair (List U8) (List U8)))) :=
    Server.read_message (fn bytes => Server.frame_request_capped bytes) sock carry

def Server.frame_request_capped (bytes : List U8) : Result String (Option I64) :=
    if Server.request_exceeds_caps bytes
    then Result.err "request too large"
    else Wire.frame_request bytes

/// The most header bytes a request may buffer.
pub def Server.max_header_bytes : I64 := 32768i64

/// The most body bytes a request may declare or buffer (chunked bodies have
/// no declared length, so the total cap below bounds them).
pub def Server.max_body_bytes : I64 := 8388608i64

def Server.max_request_bytes : I64 := I64.add Server.max_header_bytes Server.max_body_bytes

def Server.request_exceeds_caps (bytes : List U8) : Bool :=
    if I64.gt (List.length bytes) Server.max_request_bytes
    then true
    else
        match Wire.find_body_start bytes {
            Option.none => I64.gt (List.length bytes) Server.max_header_bytes,
            Option.some hs =>
                if I64.gt hs Server.max_header_bytes
                then true
                else
                    match Wire.head_headers hs bytes {
                        Result.err _ => false,
                        Result.ok headers => Server.declared_too_large (Headers.get_all "content-length" headers)
                    }
        }

#[terminating]
def Server.declared_too_large (values : List String) : Bool :=
    match values {
        List.empty => false,
        List.cons v rest =>
            match Strings.parse_i64 (String.trim v) {
                Option.none => Server.declared_too_large rest,
                Option.some n => if I64.gt n Server.max_body_bytes then true else Server.declared_too_large rest
            }
    }

// ── keep-alive ──────────────────────────────────────────────────────────

/// The most requests one connection will serve before the server closes it.
/// A bound on a chatty client, not a read timeout -- see the module note.
pub def Server.max_keep_alive_requests : I64 := 100

/// True when a header carries `token` as a value, compared case-insensitively.
/// A comma-separated list is not split, so `Connection: close, Foo` is not
/// recognised as a close; a single token is what clients send.
def Server.header_has_token (name : String) (token : String) (headers : Headers) : Bool :=
    Server.list_has_token (Headers.get_all name headers) token

#[terminating]
def Server.any_token (parts : List String) (token : String) : Bool :=
    match parts {
        List.empty => false,
        List.cons p rest =>
            if String.beq (String.to_lowercase (String.trim p)) token
            then true
            else Server.any_token rest token
    }

/// Split comma-separated token lists: `Connection: close, Foo` still says
/// close, which a whole-value comparison misses.
#[terminating]
def Server.list_has_token (values : List String) (token : String) : Bool :=
    match values {
        List.empty => false,
        List.cons v rest =>
            if Server.any_token (Strings.split_on "," v) token
            then true
            else Server.list_has_token rest token
    }

/// Whether the connection may serve another request after this one. `served`
/// counts this request.
///
/// HTTP/1.1 keeps the connection unless the peer says otherwise; HTTP/1.0
/// closes it unless the peer asks for keep-alive. An explicit
/// `Connection: close` wins in either version, and the request cap closes
/// regardless.
pub def Server.keep_alive_with (max_keep_alive : I64) (req : Request) (served : I64) : Bool :=
    if Bool.not (I64.gt max_keep_alive served)
    then false
    else if Server.header_has_token "connection" "close" req.headers
    then false
    else
        match req.version {
            HttpVersion.http1_1 => true,
            HttpVersion.http1_0 => Server.header_has_token "connection" "keep-alive" req.headers
        }

def Server.keep_alive (req : Request) (served : I64) : Bool :=
    Server.keep_alive_with Server.max_keep_alive_requests req served

/// Mark a response as the last one on its connection.
///
/// Worth saying explicitly rather than letting the close imply it: a response
/// framed without a `Content-Length` ends at the connection's end, so a peer
/// that assumed keep-alive would wait for a message that is not coming.
def Server.with_connection_header (closing : Bool) (res : Response) : Response :=
    if closing
    then { status := res.status, headers := Headers.set "Connection" "close" res.headers, version := res.version, body := res.body }
    else res

// ── connection handling ─────────────────────────────────────────────────

/// Parse and serve one framed request, reporting whether the connection should
/// stay open. A request that does not parse gets a 400 and reports `false`:
/// the framing of whatever follows a malformed message cannot be trusted, so
/// the connection ends there rather than being read as more requests.
def Server.serve_one (handler : Request -> IO Response) (sock : FdStream) (bytes : List U8) (served : I64) : IO Bool :=
    match Wire.parse_request bytes {
        Result.err _ => do {
            Server.send_error sock;
            return false
        },
        Result.ok req => do {
            let closing := Bool.not (Server.keep_alive req served);
            let res <- handler req;
            Server.write_response_for sock req.method closing res
        }
    }

/// Write a response and report whether the connection stays open.
///
/// A response that cannot be serialised -- a `Body.stream`, which has no pure
/// byte form -- becomes a 500 and ends the connection. Ending it is the point:
/// the peer was promised a body and there is none, so a response it could read
/// as complete would be a claim about bytes that do not exist.
def Server.write_response (sock : FdStream) (closing : Bool) (res : Response) : IO Bool :=
    if Body.is_stream res.body
    then Server.write_stream_response sock closing res
    else
        match Wire.format_response (Server.with_connection_header closing res) {
            Result.err _ => do {
                Server.write_bytes sock (Server.canned_bytes Server.internal_error_response);
                return false
            },
            Result.ok bytes => do {
                Server.write_bytes sock bytes;
                return (Bool.not closing)
            }
        }

/// A streamed response: a chunked head, then the body's chunks and terminal
/// chunk. A write failure ends the connection (the peer is gone or the body
/// could not be produced).
def Server.write_stream_response (sock : FdStream) (closing : Bool) (res : Response) : IO Bool := do {
    match Wire.response_head_chunked (Server.with_connection_header closing res) {
        Result.err _ => return false,
        Result.ok head => do {
            let head_res <- Server.write_bytes sock head;
            match head_res {
                Result.err _ => return false,
                Result.ok _ => do {
                    let t : Transport := Transport.plain sock;
                    let body_res <- Body.write_chunked t res.body;
                    match body_res {
                        Result.err _ => return false,
                        Result.ok _ => return (Bool.not closing)
                    }
                }
            }
        }
    }
}

/// Write a response for `method`: `HEAD`, 204 and 304 send the head (with
/// the representation's `Content-Length`) but no body, so a HEAD fallback to
/// a GET route is correct on the wire. Everything else uses the ordinary
/// framed writer.
pub def Server.write_response_for (sock : FdStream) (method : Method) (closing : Bool) (res : Response) : IO Bool :=
    if Bool.not (Wire.response_has_body method res.status)
    then Server.write_response_head sock closing res
    else Server.write_response sock closing res

/// The head-only writer used by `write_response_for`. A streamed
/// representation gets the chunked head (no body); everything else gets the
/// representation's `Content-Length`.
def Server.write_response_head (sock : FdStream) (closing : Bool) (res : Response) : IO Bool :=
    if Body.is_stream res.body
    then
        match Wire.response_head_chunked (Server.with_connection_header closing res) {
            Result.err _ => IO.pure false,
            Result.ok head => do {
                let _ <- Server.write_bytes sock head;
                return (Bool.not closing)
            }
        }
    else
        match Wire.format_response_head (Server.with_connection_header closing res) {
            Result.err _ => do {
                Server.write_bytes sock (Server.canned_bytes Server.internal_error_response);
                return false
            },
            Result.ok bytes => do {
                Server.write_bytes sock bytes;
                return (Bool.not closing)
            }
        }

/// Serve one socket until it must end, starting from `carry` -- whatever the
/// previous read left over -- with `served` counting the request about to be
/// served.
///
/// The remainder matters: those bytes are a request the peer already put on
/// the wire, so re-reading would block waiting for something already delivered,
/// and discarding them would silently drop it.
#[terminating]
pub def Server.serve_connection (handler : Request -> IO Response) (sock : FdStream) (carry : List U8) (served : I64) : IO Unit := do {
    let msg_res <- Server.read_request sock carry;
    match msg_res {
        Result.err _ => do {
            Server.send_error sock;
            Stream.close sock
        },
        Result.ok msg =>
            match msg {
                Option.none => Stream.close sock,
                Option.some pr =>
                    match pr {
                        Pair.pair bytes rest => do {
                            let keep : Bool <- Server.serve_one handler sock bytes served;
                            if keep
                            then Server.serve_connection handler sock rest (I64.add served 1)
                            else Stream.close sock
                        }
                    }
            }
    }
}

/// Read exactly one request, dispatch it, write the response, and close.
/// This is the testable entry point -- tests interleave client writes and
/// reads around it in the same thread, which terminates only because it stops
/// after the one request. Anything pipelined after it is dropped with the
/// socket; `Server.serve_connection` is the loop that keeps it.
pub def Server.handle_connection (handler : Request -> IO Response) (sock : FdStream) : IO Unit := do {
    let msg_res <- Server.read_request sock List.empty;
    match msg_res {
        Result.err _ => do {
            Server.send_error sock;
            Stream.close sock
        },
        Result.ok msg =>
            match msg {
                Option.none => Stream.close sock,
                Option.some pr =>
                    match pr {
                        Pair.pair bytes _rest => do {
                            let _keep <- Server.serve_one handler sock bytes 1;
                            Stream.close sock
                        }
                    }
            }
    }
}

/// Write a 400 Bad Request. The caller closes: a malformed request ends the
/// connection, so this always says so.
def Server.send_error (sock : FdStream) : IO Unit := do {
    Server.write_bytes sock (Server.canned_bytes Server.bad_request_response);
    return unit
}

// ── serve loop ──────────────────────────────────────────────────────────

/// Listen on `port` and serve connections forever. One connection at a
/// time, kept alive across requests. Never returns.
#[terminating]
pub def Server.serve (handler : Request -> IO Response) (port : U16) : IO Unit := do {
    let listen_res <- IO.tcp_listen port;
    match listen_res {
        Result.err _ => return unit,
        Result.ok listener => do {
            Server.serve_loop handler listener;
            Stream.close listener
        }
    }
}

/// Serve with the error-aware handler type: an `Err` becomes the canned 500.
/// The existing `serve` remains for total handlers; `Handler.of_response`
/// adapts one to this shape.
pub def Server.serve_result (handler : Request -> IO (Result String Response)) (port : U16) : IO Unit :=
    Server.serve (Handler.try Server.internal_error_response handler) port

// ── lifecycle ───────────────────────────────────────────────────────────
//
// `run` reports a bind/accept failure instead of the old silent `unit`;
// `start` hands back a handle whose listener can be closed to stop the
// accept loop. `host` is honoured by `tcp_listen_on`; header/body caps are
// module constants (`max_header_bytes`/`max_body_bytes`) applied by
// `read_request`.

pub struct ServerConfig {
    host : String,
    port : U16,
    max_in_flight : I64,
    max_keep_alive : I64,
    /// The whole head must arrive within this many milliseconds.
    head_timeout_ms : I64,
    /// The whole body must arrive within this many milliseconds.
    body_timeout_ms : I64,
    /// A keep-alive connection may sit idle this long before it is closed.
    idle_timeout_ms : I64,
    /// Backstop for a blocked write (SO_SNDTIMEO).
    write_timeout_ms : I64,
    max_header_bytes : I64,
    max_header_count : I64,
    max_body_bytes : I64,
    /// When false, an `HttpError`'s detail body is replaced by a canned one.
    expose_errors : Bool,
    dev_mode : Bool
}

pub def ServerConfig.default : ServerConfig :=
    let cfg : ServerConfig :=
        { host := "0.0.0.0", port := 8080u16, max_in_flight := 32i64,
            max_keep_alive := 100i64, head_timeout_ms := 10000i64,
            body_timeout_ms := 30000i64, idle_timeout_ms := 15000i64,
            write_timeout_ms := 30000i64, max_header_bytes := 32768i64,
            max_header_count := 100i64, max_body_bytes := 8388608i64,
            expose_errors := false, dev_mode := false } in
    cfg

pub def ServerConfig.on (port : U16) : ServerConfig :=
    let base := ServerConfig.default in
    let cfg : ServerConfig := { base with port := port } in
    cfg

pub def ServerConfig.with_host (host : String) (cfg : ServerConfig) : ServerConfig :=
    let cfg2 : ServerConfig := { cfg with host := host } in cfg2

pub def ServerConfig.with_timeouts (head_ms : I64) (body_ms : I64)
    (idle_ms : I64) (write_ms : I64) (cfg : ServerConfig) : ServerConfig :=
    let cfg2 : ServerConfig :=
        { cfg with head_timeout_ms := head_ms, body_timeout_ms := body_ms,
            idle_timeout_ms := idle_ms, write_timeout_ms := write_ms } in
    cfg2

pub def ServerConfig.with_limits (header_bytes : I64) (header_count : I64)
    (body_bytes : I64) (cfg : ServerConfig) : ServerConfig :=
    let cfg2 : ServerConfig :=
        { cfg with max_header_bytes := header_bytes, max_header_count := header_count,
            max_body_bytes := body_bytes } in
    cfg2

pub def ServerConfig.dev (cfg : ServerConfig) : ServerConfig :=
    let cfg2 : ServerConfig :=
        { cfg with expose_errors := true, dev_mode := true } in
    cfg2

/// A running server: the listener to close for shutdown and the accept-loop
/// fiber to await.
pub struct ServerHandle {
    listener : FdStream,
    fiber : Fiber Unit
}

/// Run a server and report a bind/accept failure. Sequential (one connection
/// at a time); returns only when the listener fails.
#[terminating]
pub def Server.run (cfg : ServerConfig) (handler : Request -> IO Response) : IO (Result String Unit) := do {
    let listen_res <- IO.tcp_listen_on cfg.host cfg.port;
    match listen_res {
        Result.err e => return (Result.err e.message),
        Result.ok listener => do {
            Server.serve_loop handler listener;
            Stream.close listener;
            return (Result.ok unit)
        }
    }
}

/// `run` for the error-aware handler type.
#[terminating]
pub def Server.run_response (cfg : ServerConfig) (handler : Request -> IO (Result String Response)) : IO (Result String Unit) :=
    Server.run cfg (Handler.try Server.internal_error_response handler)

/// Start the accept loop on a fiber and return a handle. `shutdown` closes
/// the listener; the loop then exits on the next accept failure.
pub def Server.start (cfg : ServerConfig) (handler : Request -> IO Response) : IO (Result String ServerHandle) := do {
    let listen_res <- IO.tcp_listen_on cfg.host cfg.port;
    match listen_res {
        Result.err e => return (Result.err e.message),
        Result.ok listener => do {
            let fiber <- forkIO (fn (_ : Unit) => Server.serve_loop handler listener);
            let h : ServerHandle := { listener := listener, fiber := fiber };
            return (Result.ok h)
        }
    }
}

/// Wait for the server's accept loop to stop. An `err` means the loop's
/// fiber never ran (no thread could be created) or was cancelled.
pub def Server.wait (h : ServerHandle) : IO (Result FiberError Unit) := await_fiber h.fiber

pub def Server.shutdown (h : ServerHandle) : IO Unit := Stream.close h.listener

/// Accept one connection, serve it to completion, then recurse. On an
/// accept error the loop ends without closing the listener: `shutdown`
/// (which closed or shut it down) owns that fd, and closing it here would be
/// a second close of a number that may already have been reused.
#[terminating]
def Server.serve_loop (handler : Request -> IO Response) (listener : FdStream) : IO Unit := do {
    let accept_res <- IO.tcp_accept listener;
    match accept_res {
        Result.err _ => return unit,
        Result.ok sock => do {
            Server.serve_connection handler sock List.empty 1;
            Server.serve_loop handler listener
        }
    }
}

// ── static file serving ─────────────────────────────────────────────────

/// Serve static files from `root`. Byte-exact, with MIME, `ETag`,
/// `If-None-Match`, a single `Range`, and a traversal guard
/// (`static_files.mo`). Prefer constructing a `Static.handler` with a
/// `StaticConfig` when you need an index file, cache policy or an exact
/// root.
pub def Server.static (root : String) (req : Request) : IO Response := do {
    let r <- Static.handler (StaticConfig.default root) req;
    match r {
        Result.ok res => return res,
        Result.err _ => return Server.internal_error_response
    }
}

/// Serve `cfg.root` with one fiber per connection, on `host:port`: the
/// preview server behind `moon static`.
///
/// `Server.run` is sequential, so a browser's parallel requests wait out the
/// first connection's keep-alive; each accepted socket gets its own fiber
/// with bounded idle/write timeouts instead. A local preview does not cap
/// in-flight connections; Ctrl-C stops it (there is no signal native to
/// catch, and the accept loop never returns on its own).
#[terminating]
def Server.serve_static_loop (handler : Request -> IO Response) (listener : FdStream) : IO (Result String Unit) := do {
    let accept_res <- IO.tcp_accept listener;
    match accept_res {
        Result.err e => return (Result.err e.message),
        Result.ok sock => do {
            let _ <- forkIO (fn (_ : Unit) => Server.serve_static_socket handler sock);
            Server.serve_static_loop handler listener
        }
    }
}

/// One connection: bounded idle and write waits, then the ordinary
/// keep-alive loop.
def Server.serve_static_socket (handler : Request -> IO Response) (sock : FdStream) : IO Unit := do {
    let _ <- FdStream.set_timeout sock 15000 30000;
    Server.serve_connection handler sock List.empty 1
}

/// Print where the preview listens, then serve until Ctrl-C.
pub def Server.serve_static (cfg : StaticConfig) (host : String) (port : U16) : IO (Result String Unit) := do {
    let listen_res <- IO.tcp_listen_on host port;
    match listen_res {
        Result.err e => return (Result.err e.message),
        Result.ok listener => do {
            IO.println (String.concat "moon static: serving " (String.concat cfg.root (String.concat " on http://" (String.concat host (String.concat ":" (String.concat (U16.to_string port) "/  (Ctrl-C to stop)"))))));
            Server.serve_static_loop (Handler.try Server.internal_error_response (Static.handler cfg)) listener
        }
    }
}

// ── concurrent server (Phase 7) ────────────────────────────────────────
//
// Fiber-per-request dispatch using forkIO. `forkIO` is NOT lazy: it starts
// the fiber immediately, so the accept loop really does run handlers
// concurrently with the next accept. `serve_concurrent_loop` still drains by
// batch rather than waiting for handlers at the end, which is the backpressure
// bound: at most `max_in_flight` connections are open at once.

/// Fork a fiber to handle exactly one connection: read one request, respond,
/// close. This is the entry point the connection-level tests use.
def Server.handle_connection_fiber (handler : Request -> IO Response) (sock : FdStream) : IO (Fiber Unit) :=
    forkIO (fn _ => Server.handle_connection handler sock)

/// Fork a fiber that serves a connection to completion, keeping it alive
/// across requests. `serve_concurrent` uses this, not the one-request
/// helper: a response that advertises keep-alive must be followed by the
/// loop, not by a close.
def Server.serve_connection_fiber (handler : Request -> IO Response) (sock : FdStream) : IO (Fiber Unit) :=
    forkIO (fn _ => Server.serve_connection handler sock List.empty 1)

/// Await all pending fibers in order. A connection's own failures are
/// handled inside `serve_connection`; a fiber error here means the
/// connection was never served, which is reported on stderr because the
/// accept loop has no caller to return it to.
#[terminating]
def Server.drain_fibers (fibers : List (Fiber Unit)) : IO Unit :=
    match fibers {
        List.empty => return unit,
        List.cons f rest => do {
            let r <- await_fiber f;
            Server.report_fiber_error r;
            Server.drain_fibers rest
        }
    }

def Server.report_fiber_error (r : Result FiberError Unit) : IO Unit :=
    match r {
        Result.ok _ => return unit,
        Result.err e => IO.write_stderr (String.concat "moon: connection not served: "
            (String.concat (FiberError.message e) "\n"))
    }

/// Listen on `port` and serve connections with fiber-per-request dispatch.
/// Accepts up to `max_in_flight` connections, forking a handler fiber for
/// each, then drains all fibers before accepting more. Never returns.
#[terminating]
pub def Server.serve_concurrent (handler : Request -> IO Response) (port : U16) (max_in_flight : I64) : IO Unit := do {
    let listen_res <- IO.tcp_listen port;
    match listen_res {
        Result.err _ => return unit,
        Result.ok listener => Server.serve_concurrent_loop handler listener max_in_flight 0 List.empty
    }
}

/// Internal accept loop: collect fibers until `max_in_flight`, then drain.
#[terminating]
def Server.serve_concurrent_loop (handler : Request -> IO Response) (listener : FdStream) (max_in_flight : I64) (count : I64) (pending : List (Fiber Unit)) : IO Unit := do {
    let accept_res <- IO.tcp_accept listener;
    match accept_res {
        Result.err _ => do {
            Server.drain_fibers pending;
            Stream.close listener
        },
        Result.ok sock => do {
            let fiber <- Server.serve_connection_fiber handler sock;
            let new_pending := List.cons fiber pending;
            let new_count := I64.add count 1;
            if Bool.not (I64.lt new_count max_in_flight)
            then do {
                Server.drain_fibers new_pending;
                Server.serve_concurrent_loop handler listener max_in_flight 0 List.empty
            }
            else Server.serve_concurrent_loop handler listener max_in_flight new_count new_pending
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// Transformer server (HandlerT) — the hardened path.
//
// The original `serve`/`run`/`start` above stay exactly as they were. This
// path adds what they cannot: per-request deadlines, a head-first reader
// (so `Expect: 100-continue` works and a body is read exactly once), strict
// Host/target parsing, a `Transport` factory (TLS is a hook, not a
// dependency), and continuous acceptance instead of batch draining.
//
// Every `let x <- ...` sits at the top level of a def, never inside a match
// arm: that shape is what the parser rejects (and the checker mis-handles).
// ════════════════════════════════════════════════════════════════════════

pub struct ServerHandleT {
    listener : FdStream,
    fiber : Fiber Unit,
    stop : Ref Bool,
    live : Ref (List (Fiber Unit))
}

// ── deadlines ───────────────────────────────────────────────────────────

/// One read, waiting until `deadline` (absolute milliseconds). `ok none` is
/// EOF; `err "timeout"` is a missed deadline.
def Server.read_some (t : Transport) (max : I64) (deadline : I64) :
    IO (Result String (Option (List U8))) := do {
    let now <- IO.current_time;
    let remaining := I64.sub deadline now;
    if I64.lt remaining 1i64
    then IO.pure (Result.err "timeout")
    else do {
        let ready <- Transport.wait_read t remaining;
        match ready {
            Result.err e => IO.pure (Result.err e.message),
            Result.ok is_ready =>
                if Bool.not is_ready
                then IO.pure (Result.err "timeout")
                else do {
                    let r <- Transport.read_bytes t max;
                    match r {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok bytes => IO.pure (Result.ok (Option.some bytes))
                    }
                }
        }
    }
}

// ── head-first request reader ──────────────────────────────────────────

def Server.head_eof (carry : List U8) :
    IO (Result String (Option (Pair (List U8) (List U8)))) :=
    if List.is_empty carry
    then IO.pure (Result.ok Option.none)
    else IO.pure (Result.err "connection closed mid-head")

#[terminating]
def Server.read_head_more (t : Transport) (carry : List U8) (deadline : I64)
    (max_bytes : I64) : IO (Result String (Option (Pair (List U8) (List U8)))) := do {
    let read <- Server.read_some t 4096i64 deadline;
    match read {
        Result.err e => IO.pure (Result.err e),
        Result.ok opt =>
            match opt {
                Option.none => Server.head_eof carry,
                Option.some chunk =>
                    if List.is_empty chunk
                    then Server.head_eof carry
                    else Server.read_head t (List.append carry chunk) deadline max_bytes
            }
    }
}

/// Read through the CRLFCRLF. The head is capped small, so the append here
/// is bounded; the body is handled separately and never re-parsed.
#[terminating]
def Server.read_head (t : Transport) (carry : List U8) (deadline : I64)
    (max_bytes : I64) : IO (Result String (Option (Pair (List U8) (List U8)))) :=
    match Wire.find_body_start carry {
        Option.some n =>
            let head := Wire.take_bytes n carry in
            let rest := Strings.drop_bytes n carry in
            IO.pure (Result.ok (Option.some (Pair.pair head rest))),
        Option.none =>
            if I64.gt (List.length carry) max_bytes
            then IO.pure (Result.err "header block too large")
            else Server.read_head_more t carry deadline max_bytes
    }

/// Read exactly `n` body bytes, consuming from `carry` first. Chunks are
/// accumulated in reverse and flattened once, so a large body is O(n).
#[terminating]
def Server.read_exact_loop (t : Transport) (rest : List U8) (remaining : I64)
    (deadline : I64) (chunks : List (List U8)) :
    IO (Result String (Pair (List U8) (List U8))) :=
    if I64.lt remaining 1i64
    then
        let body := Wire.concat_chunks (List.reverse chunks) in
        IO.pure (Result.ok (Pair.pair body rest))
    else do {
        let max_read := if I64.lt 65536i64 remaining then remaining else 65536i64;
        let read <- Server.read_some t max_read deadline;
        match read {
            Result.err e => IO.pure (Result.err e),
            Result.ok opt =>
                match opt {
                    Option.none => IO.pure (Result.err "connection closed before Content-Length bytes"),
                    Option.some chunk =>
                        if List.is_empty chunk
                        then IO.pure (Result.err "connection closed before Content-Length bytes")
                        else
                            let n := List.length chunk in
                            Server.read_exact_loop t rest (I64.sub remaining n) deadline
                                (List.cons chunk chunks)
                }
        }
    }

def Server.read_exact_body (t : Transport) (carry : List U8) (n : I64)
    (deadline : I64) : IO (Result String (Pair Body (List U8))) := do {
    let have := List.length carry;
    let take_n := if I64.lt have n then have else n;
    let part := Wire.take_bytes take_n carry;
    let rest := Strings.drop_bytes take_n carry;
    let remaining := I64.sub n take_n;
    let chunks : List (List U8) :=
        if List.is_empty part then List.empty else List.cons part List.empty;
    let r <- Server.read_exact_loop t rest remaining deadline chunks;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok pr =>
            match pr {
                Pair.pair bytes rest2 =>
                    let body : Body :=
                        if List.is_empty bytes then Body.empty else Body.bytes bytes in
                    IO.pure (Result.ok (Pair.pair body rest2))
            }
    }
}

/// Continue a chunked decode after a read. Kept out of `read_chunked_loop`'s
/// match so every bind stays at a def's top level.
#[terminating]
def Server.read_chunked_more (t : Transport) (pending : List U8)
    (chunks : List (List U8)) (total : I64) (encoded : I64) (deadline : I64)
    (max_body : I64) : IO (Result String (Pair Body (List U8))) := do {
    let read <- Server.read_some t 65536i64 deadline;
    match read {
        Result.err e => IO.pure (Result.err e),
        Result.ok opt =>
            match opt {
                Option.none => IO.pure (Result.err "chunked body ended before terminal chunk"),
                Option.some chunk =>
                    if List.is_empty chunk
                    then IO.pure (Result.err "chunked body ended before terminal chunk")
                    else
                        let encoded2 := I64.add encoded (List.length chunk) in
                        if I64.gt encoded2 max_body
                        then IO.pure (Result.err "body too large")
                        else Server.read_chunked_loop t pending chunk chunks total encoded2
                            deadline max_body
            }
    }
}

/// Decode a chunked body incrementally. `pending` is the previous step's
/// undecoded tail; `incoming` is what was just read. The encoded and decoded
/// totals are both capped, so chunk metadata cannot buy unbounded buffering.
#[terminating]
def Server.read_chunked_loop (t : Transport) (pending : List U8) (incoming : List U8)
    (chunks : List (List U8)) (total : I64) (encoded : I64) (deadline : I64)
    (max_body : I64) : IO (Result String (Pair Body (List U8))) :=
    match Wire.chunk_step pending incoming {
        Result.err e => IO.pure (Result.err e),
        Result.ok pr =>
            match pr {
                Pair.pair state leftover =>
                    match state {
                        Pair.pair done out =>
                            let total2 := I64.add total (List.length out) in
                            let chunks2 := List.cons out chunks in
                            if I64.gt total2 max_body
                            then IO.pure (Result.err "body too large")
                            else if done
                            then
                                let bytes := Wire.concat_chunks (List.reverse chunks2) in
                                let body : Body :=
                                    if List.is_empty bytes then Body.empty else Body.bytes bytes in
                                IO.pure (Result.ok (Pair.pair body leftover))
                            else Server.read_chunked_more t leftover chunks2 total2 encoded deadline max_body
                    }
            }
    }

def Server.expectation (headers : Headers) : Option String :=
    match Headers.get "expect" headers {
        Option.none => Option.none,
        Option.some v => Option.some (String.to_lowercase (String.trim v))
    }

def Server.expect_continue (headers : Headers) : Bool :=
    match Server.expectation headers {
        Option.some v => String.beq v "100-continue",
        Option.none => false
    }

def Server.expect_unsupported (headers : Headers) : Bool :=
    match Server.expectation headers {
        Option.some v => Bool.not (String.beq v "100-continue"),
        Option.none => false
    }

def Server.maybe_continue (t : Transport) (headers : Headers) : IO Unit := do {
    if Server.expect_continue headers
    then do {
        let _ <- Transport.write_bytes t Wire.continue_response;
        return unit
    }
    else return unit
}

def Server.with_body (req : Request) (body : Body) (rest : List U8) :
    Result String (Option (Pair Request (List U8))) :=
    let req2 : Request := { req with body := body } in
    Result.ok (Option.some (Pair.pair req2 rest))

def Server.read_cl_request (cfg : ServerConfig) (t : Transport) (req : Request)
    (carry : List U8) (n : I64) (deadline : I64) :
    IO (Result String (Option (Pair Request (List U8)))) := do {
    Server.maybe_continue t req.headers;
    let r <- Server.read_exact_body t carry n deadline;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok pr =>
            match pr {
                Pair.pair body rest => IO.pure (Server.with_body req body rest)
            }
    }
}

def Server.read_chunked_request (cfg : ServerConfig) (t : Transport) (req : Request)
    (carry : List U8) (deadline : I64) :
    IO (Result String (Option (Pair Request (List U8)))) := do {
    Server.maybe_continue t req.headers;
    let encoded := List.length carry;
    let r <- Server.read_chunked_loop t List.empty carry List.empty 0i64 encoded
        deadline cfg.max_body_bytes;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok pr =>
            match pr {
                Pair.pair body rest => IO.pure (Server.with_body req body rest)
            }
    }
}

def Server.read_request_body (cfg : ServerConfig) (t : Transport) (req : Request)
    (framing : Framing) (carry : List U8) :
    IO (Result String (Option (Pair Request (List U8)))) := do {
    if Server.expect_unsupported req.headers
    then IO.pure (Result.err "expectation failed")
    else do {
        let now <- IO.current_time;
        let deadline := I64.add now cfg.body_timeout_ms;
        match framing {
            Framing.no_body =>
                IO.pure (Result.ok (Option.some (Pair.pair req carry))),
            Framing.until_eof =>
                IO.pure (Result.err "request body cannot be read-to-close"),
            Framing.content_length n =>
                if I64.gt n cfg.max_body_bytes
                then IO.pure (Result.err "body too large")
                else Server.read_cl_request cfg t req carry n deadline,
            Framing.chunked =>
                Server.read_chunked_request cfg t req carry deadline
        }
    }
}

def Server.read_request_t (cfg : ServerConfig) (t : Transport) (carry : List U8) :
    IO (Result String (Option (Pair Request (List U8)))) := do {
    let now <- IO.current_time;
    let deadline := I64.add now cfg.head_timeout_ms;
    let head_res <- Server.read_head t carry deadline cfg.max_header_bytes;
    match head_res {
        Result.err e => IO.pure (Result.err e),
        Result.ok opt =>
            match opt {
                Option.none => IO.pure (Result.ok Option.none),
                Option.some pr =>
                    match pr {
                        Pair.pair head rest =>
                            match Wire.parse_request_head_strict head {
                                Result.err e => IO.pure (Result.err e),
                                Result.ok req =>
                                    match Wire.request_framing req.headers {
                                        Result.err e => IO.pure (Result.err e),
                                        Result.ok framing =>
                                            Server.read_request_body cfg t req framing rest
                                    }
                            }
                    }
            }
    }
}

// ── responses ───────────────────────────────────────────────────────────

def Server.reason_of (status : U16) : String :=
    if U16.beq status Status.bad_request then "Bad Request"
    else if U16.beq status Status.not_found then "Not Found"
    else if U16.beq status Status.internal_server_error then "Internal Server Error"
    else if U16.beq status Status.request_timeout then "Request Timeout"
    else if U16.beq status Status.payload_too_large then "Payload Too Large"
    else if U16.beq status Status.request_header_fields_too_large
    then "Request Header Fields Too Large"
    else if U16.beq status Status.expectation_failed then "Expectation Failed"
    else "Error"

def Server.error_status (msg : String) : U16 :=
    if String.beq msg "timeout" then Status.request_timeout
    else if String.beq msg "header block too large"
        || String.beq msg "too many header fields"
        || String.beq msg "header line too long"
    then Status.request_header_fields_too_large
    else if String.beq msg "body too large" then Status.payload_too_large
    else if String.beq msg "expectation failed" then Status.expectation_failed
    else Status.bad_request

/// A response for a handler error. Without `expose_errors`, the detail body
/// is replaced by a canned phrase; status and headers are kept.
def Server.error_response (cfg : ServerConfig) (e : HttpError) : Response :=
    if cfg.expose_errors
    then HttpError.to_response e
    else
        let r : Response := HttpError.to_response e in
        match r {
            { status, headers, version, .. } =>
                let res : Response :=
                    { status := status, headers := headers, version := version,
                        body := Body.text (Server.reason_of status) } in
                res
        }

def Server.dispatch_t (cfg : ServerConfig) (handler : HandlerT IO Response)
    (req : Request) : IO Response := do {
    let r <- HandlerT.run_io handler req;
    match r {
        Result.ok res => IO.pure res,
        Result.err e => IO.pure (Server.error_response cfg e)
    }
}

def Server.write_stream_body_t (t : Transport) (res : Response)
    (closing : Bool) : IO Bool := do {
    let bw <- Body.write_chunked t res.body;
    match bw {
        Result.err _ => IO.pure false,
        Result.ok _ => IO.pure (Bool.not closing)
    }
}

def Server.write_stream_head_t (t : Transport) (head : List U8)
    (res : Response) (closing : Bool) : IO Bool := do {
    let hw <- Transport.write_bytes t head;
    match hw {
        Result.err _ => IO.pure false,
        Result.ok _ => Server.write_stream_body_t t res closing
    }
}

def Server.write_stream_response_t (t : Transport) (closing : Bool)
    (res : Response) : IO Bool :=
    match Wire.response_head_chunked (Server.with_connection_header closing res) {
        Result.err _ => IO.pure false,
        Result.ok head => Server.write_stream_head_t t head res closing
    }

def Server.write_canned_t (t : Transport) : IO Bool := do {
    let _ <- Transport.write_bytes t (Server.canned_bytes Server.internal_error_response);
    IO.pure false
}

def Server.write_formatted_t (t : Transport) (bytes : List U8)
    (closing : Bool) : IO Bool := do {
    let w <- Transport.write_bytes t bytes;
    match w {
        Result.err _ => IO.pure false,
        Result.ok _ => IO.pure (Bool.not closing)
    }
}

def Server.write_response_t (t : Transport) (closing : Bool)
    (res : Response) : IO Bool :=
    if Body.is_stream res.body
    then Server.write_stream_response_t t closing res
    else
        match Wire.format_response (Server.with_connection_header closing res) {
            Result.err _ => Server.write_canned_t t,
            Result.ok bytes => Server.write_formatted_t t bytes closing
        }

def Server.write_head_canned_t (t : Transport) : IO Bool := do {
    let _ <- Transport.write_bytes t (Server.canned_bytes Server.internal_error_response);
    IO.pure false
}

def Server.write_head_bytes_t (t : Transport) (bytes : List U8)
    (closing : Bool) : IO Bool := do {
    let _ <- Transport.write_bytes t bytes;
    IO.pure (Bool.not closing)
}

def Server.write_response_head_t (t : Transport) (closing : Bool)
    (res : Response) : IO Bool :=
    if Body.is_stream res.body
    then
        match Wire.response_head_chunked (Server.with_connection_header closing res) {
            Result.err _ => IO.pure false,
            Result.ok head => Server.write_head_bytes_t t head closing
        }
    else
        match Wire.format_response_head (Server.with_connection_header closing res) {
            Result.err _ => Server.write_head_canned_t t,
            Result.ok bytes => Server.write_head_bytes_t t bytes closing
        }

def Server.write_response_for_t (t : Transport) (method : Method)
    (closing : Bool) (res : Response) : IO Bool :=
    if Bool.not (Wire.response_has_body method res.status)
    then Server.write_response_head_t t closing res
    else Server.write_response_t t closing res

def Server.wait_idle (t : Transport) (ms : I64) : IO (Result String Bool) := do {
    let r <- Transport.wait_read t ms;
    match r {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok b => IO.pure (Result.ok b)
    }
}

// ── connection loop ─────────────────────────────────────────────────────

#[terminating]
def Server.serve_framed_t (cfg : ServerConfig) (handler : HandlerT IO Response)
    (t : Transport) (req : Request) (rest : List U8) (served : I64) : IO Unit := do {
    let keep := Server.keep_alive_with cfg.max_keep_alive req served;
    let closing := Bool.not keep;
    let res <- Server.dispatch_t cfg handler req;
    let stay <- Server.write_response_for_t t req.method closing res;
    if stay
    then Server.serve_connection_t cfg handler t rest (I64.add served 1)
    else Transport.close t
}

def Server.serve_parse_error_t (t : Transport) (e : String) : IO Unit := do {
    let status := Server.error_status e;
    let res : Response := Response.text status (Server.reason_of status);
    let _ <- Transport.write_bytes t (Server.canned_bytes res);
    Transport.close t
}

def Server.serve_request_t (cfg : ServerConfig) (handler : HandlerT IO Response)
    (t : Transport) (msg : Result String (Option (Pair Request (List U8))))
    (carry : List U8) (served : I64) : IO Unit :=
    match msg {
        Result.err e => Server.serve_parse_error_t t e,
        Result.ok opt =>
            match opt {
                Option.none => Transport.close t,
                Option.some pr =>
                    match pr {
                        Pair.pair req rest => Server.serve_framed_t cfg handler t req rest served
                    }
            }
    }

#[terminating]
def Server.serve_connection_t (cfg : ServerConfig) (handler : HandlerT IO Response)
    (t : Transport) (carry : List U8) (served : I64) : IO Unit := do {
    let idle_ok <-
        if List.is_empty carry
        then Server.wait_idle t cfg.idle_timeout_ms
        else IO.pure (Result.ok true);
    if Bool.not (Server.idle_ready idle_ok)
    then Transport.close t
    else do {
        let msg <- Server.read_request_t cfg t carry;
        Server.serve_request_t cfg handler t msg carry served
    }
}

def Server.idle_ready (r : Result String Bool) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok b => b
    }

// ── acceptance and lifecycle ────────────────────────────────────────────

#[terminating]
def Server.reap_one (f : Fiber Unit) (rest : List (Fiber Unit))
    (live : List (Fiber Unit)) : IO (List (Fiber Unit)) := do {
    let p <- pollFiber f;
    match p {
        Option.none => Server.reap_fibers rest (List.cons f live),
        Option.some _ => Server.reap_fibers rest live
    }
}

#[terminating]
def Server.reap_fibers (fibers : List (Fiber Unit)) (live : List (Fiber Unit)) :
    IO (List (Fiber Unit)) :=
    match fibers {
        List.empty => IO.pure (List.reverse live),
        List.cons f rest => Server.reap_one f rest live
    }

#[terminating]
def Server.cancel_one (f : Fiber Unit) (rest : List (Fiber Unit)) : IO Unit := do {
    cancel_fiber f;
    Server.cancel_fibers rest
}

#[terminating]
def Server.cancel_fibers (fibers : List (Fiber Unit)) : IO Unit :=
    match fibers {
        List.empty => IO.pure unit,
        List.cons f rest => Server.cancel_one f rest
    }

def Server.accept_stop (listener : FdStream) (live : Ref (List (Fiber Unit))) : IO Unit := do {
    let fibers <- Ref.get live;
    Server.cancel_fibers fibers;
    Stream.close listener
}

#[terminating]
def Server.accept_continue (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) : IO Unit := do {
    sleepIO 5i64;
    Server.accept_loop_with cfg listener stop live mk_transport handler
}

#[terminating]
def Server.accept_factory_failed (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) (sock : FdStream) : IO Unit := do {
    Stream.close sock;
    Server.accept_loop_with cfg listener stop live mk_transport handler
}

#[terminating]
def Server.accept_fork (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) (t : Transport) : IO Unit := do {
    let fiber <- forkIO (fn (_ : Unit) =>
        Server.serve_connection_t cfg handler t List.empty 1i64);
    let _ <- Ref.update live (fn (xs : List (Fiber Unit)) => List.cons fiber xs);
    Server.accept_loop_with cfg listener stop live mk_transport handler
}

#[terminating]
def Server.accept_one (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) (sock : FdStream) : IO Unit := do {
    let _ <- FdStream.set_timeout sock cfg.idle_timeout_ms cfg.write_timeout_ms;
    let mt <- mk_transport sock;
    match mt {
        Result.err _ => Server.accept_factory_failed cfg listener stop live mk_transport handler sock,
        Result.ok t => Server.accept_fork cfg listener stop live mk_transport handler t
    }
}

def Server.accept_accept_failed (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response)
    (still : List (Fiber Unit)) : IO Unit := do {
    Server.cancel_fibers still;
    Stream.close listener
}

/// Accept continuously. Finished fibers are reaped each pass; while the live
/// count is at the cap the loop sleeps briefly instead of accepting. A slow
/// or SSE connection therefore never blocks acceptance until the cap itself
/// is reached.
#[terminating]
def Server.accept_loop_with (cfg : ServerConfig) (listener : FdStream)
    (stop : Ref Bool) (live : Ref (List (Fiber Unit)))
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) : IO Unit := do {
    let stopping <- Ref.get stop;
    if stopping
    then Server.accept_stop listener live
    else do {
        let current <- Ref.get live;
        let still <- Server.reap_fibers current List.empty;
        Ref.set live still;
        let count := List.length still;
        if I64.gt count cfg.max_in_flight
        then Server.accept_continue cfg listener stop live mk_transport handler
        else do {
            let accept <- IO.tcp_accept listener;
            match accept {
                Result.err _ => Server.accept_accept_failed cfg listener stop live mk_transport handler still,
                Result.ok sock => Server.accept_one cfg listener stop live mk_transport handler sock
            }
        }
    }
}

pub def Server.plain_transport (sock : FdStream) : IO (Result String Transport) :=
    IO.pure (Result.ok (Transport.plain sock))

def Server.start_on (cfg : ServerConfig) (handler : HandlerT IO Response)
    (listener : FdStream) : IO (Result String ServerHandleT) := do {
    let stop : Ref Bool <- Ref.new false;
    let live : Ref (List (Fiber Unit)) <- Ref.new List.empty;
    let fiber <- forkIO (fn (_ : Unit) =>
        Server.accept_loop_with cfg listener stop live Server.plain_transport handler);
    let h : ServerHandleT :=
        { listener := listener, fiber := fiber, stop := stop, live := live };
    IO.pure (Result.ok h)
}

/// Start on a fiber and return a handle whose listener can be closed.
pub def Server.start_t (cfg : ServerConfig) (handler : HandlerT IO Response) :
    IO (Result String ServerHandleT) := do {
    let listen <- IO.tcp_listen_on cfg.host cfg.port;
    match listen {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok listener => Server.start_on cfg handler listener
    }
}

pub def Server.wait_t (h : ServerHandleT) : IO (Result FiberError Unit) :=
    await_fiber h.fiber

pub def Server.shutdown_t (h : ServerHandleT) : IO Unit := do {
    Ref.set h.stop true;
    Stream.close h.listener
}

def Server.run_on (cfg : ServerConfig)
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) (listener : FdStream) :
    IO (Result String Unit) := do {
    let stop : Ref Bool <- Ref.new false;
    let live : Ref (List (Fiber Unit)) <- Ref.new List.empty;
    Server.accept_loop_with cfg listener stop live mk_transport handler;
    IO.pure (Result.ok unit)
}

/// Run with a per-connection transport factory. TLS is a factory
/// (`motes/tls` currently has only a client handshake); moon never depends
/// on it.
pub def Server.run_with (cfg : ServerConfig)
    (mk_transport : FdStream -> IO (Result String Transport))
    (handler : HandlerT IO Response) : IO (Result String Unit) := do {
    let listen <- IO.tcp_listen_on cfg.host cfg.port;
    match listen {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok listener => Server.run_on cfg mk_transport handler listener
    }
}

pub def Server.run_t (cfg : ServerConfig) (handler : HandlerT IO Response) :
    IO (Result String Unit) :=
    Server.run_with cfg Server.plain_transport handler
