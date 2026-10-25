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

use std::concurrent::fiber {Fiber, FiberError, FiberError.message, await_fiber, forkIO}
use std::list {List.length}
use std::stream {Stream, FdStream}
use http::types {
  Transport, Transport.read_bytes, Transport.write_bytes,
  Body, Body.is_stream, Headers, Headers.get_all, Method, Request, Response,
  Status.bad_request, Status.internal_server_error, Status.not_found, http1_0,
  http1_1,
}
use http::strings {Strings.drop_bytes, Strings.parse_i64}
use http::wire {
  Wire.find_body_start, Wire.format_response, Wire.format_response_head,
  Wire.frame_request, Wire.head_headers, Wire.parse_request,
  Wire.response_has_body, Wire.response_head_chunked, Wire.take_bytes,
}
use lib::handler {Handler.try}
use http::body_io {Body.write_chunked}
use lib::static_files {Static.handler, StaticConfig.default}

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

def Server.list_has_token (values : List String) (token : String) : Bool :=
  match values {
    List.empty => false,
    List.cons v rest =>
      if String.beq (String.to_lowercase (String.trim v)) token
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
def Server.keep_alive (req : Request) (served : I64) : Bool :=
  if Bool.not (I64.gt Server.max_keep_alive_requests served)
  then false
  else if Server.header_has_token "connection" "close" req.headers
  then false
  else
    match req.version {
      HttpVersion.http1_1 => true,
      HttpVersion.http1_0 => Server.header_has_token "connection" "keep-alive" req.headers
    }

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
  max_keep_alive : I64
}

pub def ServerConfig.default : ServerConfig :=
  let cfg : ServerConfig :=
    { host := "0.0.0.0", port := 8080u16, max_in_flight := 1, max_keep_alive := 100 } in
  cfg

pub def ServerConfig.on (port : U16) : ServerConfig :=
  let base := ServerConfig.default in
  let cfg : ServerConfig := { base with port := port } in
  cfg

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
