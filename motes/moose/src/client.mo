/// HTTP/1.1 client — `moose` mote, Layer 1.
///
/// Connects to a server over TCP, sends an HTTP/1.1 request, reads the
/// response. Two API styles:
///
///   One-shot:  `Client.get url`, `Client.post url body`, `Client.request req`
///              — opens a fresh connection per call, closes after.
///
///   Keep-alive: `Client.connect url` → `Client.send conn req` → `Client.close conn`
///              — reuses one TCP connection across multiple `send` calls.
///              Requires `Content-Length` in responses to delimit bodies.
///
/// Redirect following is opt-in via `Client.request_with max_redirects req`,
/// where the argument is the hop cap (0 = do not follow). The policy is
/// `Client.redirect_request`: 307/308 and HEAD keep the method and body,
/// 301/302 keep them except for a POST, 303 asks with GET; headers travel with
/// the request except the ones describing a dropped body, and credentials are
/// dropped when the redirect leaves the origin.
///
/// HTTPS goes through `motes/tls`: the connection's transport is
/// `Transport.secure` carrying `Tls.read`/`write`/`close` over a
/// verified handshake (certificate chain AND hostname), and everything
/// below `Client.connect` speaks `Transport`, not `Socket`, so the two
/// schemes share one request/response path.

use http::types {
  Body, Headers, Method, Request, Response, Status.found,
  Status.moved_permanently, Status.permanent_redirect, Status.see_other,
  Status.temporary_redirect, Transport, Uri, http1_1,
}
use tls::stream {Tls.Stream, Tls.close, Tls.connect, Tls.read, Tls.write}
use http::wire {
  Wire.format_request, Wire.frame_response, Wire.parse_response_with_method,
  Wire.take_bytes,
}
use http::body {}
use http::uri {Uri.format, Uri.parse, Uri.resolve, Uri.same_origin}

// ── Connection handle ───────────────────────────────────────────────────

struct Connection {
  socket : Transport,
  host : String,
  port : U16
}

// ── small helpers ───────────────────────────────────────────────────────

// ── URI → host/port ─────────────────────────────────────────────────────

/// The port a scheme connects on when the URI names none: 443 for
/// `https`, 80 for everything else.
def Client.default_port (scheme : String) : U16 :=
  if String.beq scheme "https"
  then 443u16
  else 80u16

/// Extract host and port from a URI. Defaults to the scheme's port
/// (443 for `https`, 80 otherwise) when absent.
def Client.host_port (u : Uri) : Pair String U16 :=
  match u.port {
    Option.some p => Pair.pair u.host p,
    Option.none => Pair.pair u.host (Client.default_port u.scheme)
  }

/// Build the `Host` header value: `host:port` when the port is non-default
/// for the scheme, just `host` otherwise (an explicit `:443` on an
/// `https` URL is as default as `:80` on `http`).
def Client.host_header_value (u : Uri) : String :=
  match u.port {
    Option.none => u.host,
    Option.some p =>
      if U16.beq p (Client.default_port u.scheme)
      then u.host
      else String.concat u.host (String.concat ":" (U16.to_string p))
  }

/// Ensure the `Host` header is set on the request before sending.
def Client.prepare_request (req : Request) : Request :=
  let host := Client.host_header_value req.uri in
  { req with headers := Headers.set "Host" host req.headers }

// ── reading a response ──────────────────────────────────────────────────
//
// Frame-first, like the server's request reader: buffer until
// `Wire.frame_response` can see where the message ends, then parse. The method
// is part of the frame rather than a detail of the parse -- a `HEAD` response
// carries the `Content-Length` of the body it is *not* sending, so framing it
// by that length is how a client comes to wait for bytes that never arrive.
//
// A response with no `Content-Length` has no frame until the connection ends
// (RFC 9110 §6.3, read-to-close), so `ok none` at EOF means the buffer is the
// whole message. Parsing is what decides: the call that rejects a truncated
// `Content-Length` body accepts an EOF-delimited one, so EOF needs no special
// case here beyond "stop reading and parse".

/// Read one whole response to `method`, buffering until it frames.
#[terminating]
def Client.read_message (method : Method) (t : Transport) (carry : List U8) : IO (Result String Response) := do {
  let frame : Result String (Option I64) := Wire.frame_response carry method;
  match frame {
    Result.err e => return (Result.err e),
    Result.ok opt =>
      match opt {
        Option.some n => return (Client.parse_framed method (Wire.take_bytes n carry)),
        Option.none => do {
          let read_res <- Transport.read t 4096u64;
          Client.read_message_step method t carry read_res
        }
      }
  }
}

/// One `Transport.read` result, while the response is still incomplete.
#[terminating]
def Client.read_message_step (method : Method) (t : Transport) (carry : List U8) (read_res : Result String (List U8)) : IO (Result String Response) :=
  match read_res {
    Result.err e => return (Result.err e),
    Result.ok chunk =>
      if List.is_empty chunk
      then return (Client.parse_framed method carry)
      else Client.read_message method t (List.append carry chunk)
  }

/// Parse a buffered response. A frame that completed and a buffer that ended
/// at EOF both arrive here, and `Wire.parse_response_with_method` is what tells
/// them apart: a `Content-Length` message that stops short is a truncation and
/// the parse reports it, while a read-to-close message is everything buffered.
def Client.parse_framed (method : Method) (bytes : List U8) : Result String Response :=
  Wire.parse_response_with_method bytes method

/// Read a full response to `method` from a socket. Exposed so callers (and
/// tests) can read a pre-written response without writing a request first.
///
/// The remainder after the frame is dropped rather than carried, unlike the
/// server's reader: a client that asks for one response at a time is not sent
/// a second one ahead of its request.
def Client.read_response (t : Transport) (method : Method) : IO (Result String Response) :=
  Client.read_message method t List.empty

// ── connection-handle API (keep-alive) ───────────────────────────────────

/// Open a connection to the host:port in `url` — TLS for `https`, TCP for
/// everything else.
def Client.connect (url : String) : IO (Result String Connection) :=
  match Uri.parse url {
    Result.err e => return (Result.err e),
    Result.ok u =>
      if String.beq u.scheme "https"
      then Client.connect_tls u
      else Client.connect_tcp u
  }

/// Connect to the host:port extracted from `u` and wrap in `Connection`.
def Client.connect_tcp (u : Uri) : IO (Result String Connection) :=
  let hp := Client.host_port u in
  Monad.bind (IO.tcp_connect hp.first hp.second) (fn connect_res =>
    Client.connect_done hp connect_res)

/// Wrap a successful `tcp_connect` result in a `Connection`.
def Client.connect_done (hp : Pair String U16) (connect_res : Result String Socket) : IO (Result String Connection) :=
  match connect_res {
    Result.err e => return (Result.err e),
    Result.ok sock =>
      // Bare bindings, not `hp.first`/`hp.second` inline: the self-hosted
      // checker types a `Pair` read with the inductive's parameter left
      // unsubstituted, which a literal's field position cannot absorb.
      let host := hp.first in
      let port := hp.second in
      return (Result.ok ({ socket := Transport.plain sock, host := host, port := port } : Connection))
  }

/// Hand `host:port` to `Tls.connect`, whose handshake verifies the
/// certificate chain AND the hostname before it returns.
def Client.connect_tls (u : Uri) : IO (Result String Connection) :=
  let hp := Client.host_port u in
  Monad.bind (Tls.connect hp.first hp.second) (fn tls_res =>
    Client.connect_tls_done hp tls_res)

/// Wrap a verified `Tls.Stream` in a `Connection` carrying `Transport.secure`
/// — the one place http's transport closures and the tls mote are joined.
def Client.connect_tls_done (hp : Pair String U16) (tls_res : Result String Tls.Stream) : IO (Result String Connection) :=
  match tls_res {
    Result.err e => return (Result.err e),
    Result.ok s =>
      let host := hp.first in
      let port := hp.second in
      return (Result.ok ({ socket := Transport.secure (Tls.read s) (Tls.write s) (Tls.close s), host := host, port := port } : Connection))
  }

/// Write a request to the connection's socket (no read). Exposed so callers
/// (and tests) can interleave writes with server-side reads/writes.
///
/// Serialising reports failure for a `Body.stream`, which has no pure byte
/// form, and the failure is returned rather than written: sending the peer a
/// `Content-Length: 0` message instead would claim a body that was never sent.
def Client.write_request (conn : Connection) (req : Request) : IO (Result String U64) :=
  match Wire.format_request (Client.prepare_request req) {
    Result.err e => return (Result.err e),
    Result.ok bytes => Transport.write conn.socket bytes
  }

/// Send a request on an existing connection and read the response.
/// The socket stays open — call `Client.send` again or `Client.close`.
///
/// The request's method is carried into the read: it is what tells the frame
/// whether the response has a body at all, so a `HEAD` cannot be answered with
/// a hang on a `Content-Length` it will not be sent.
def Client.send (conn : Connection) (req : Request) : IO (Result String Response) :=
  match Wire.format_request (Client.prepare_request req) {
    Result.err e => return (Result.err e),
    Result.ok bytes =>
      Monad.bind (Transport.write conn.socket bytes) (fn write_res =>
        Client.send_after_write conn.socket req.method write_res)
  }

/// After writing the request, read the response and parse it.
def Client.send_after_write (t : Transport) (method : Method) (write_res : Result String U64) : IO (Result String Response) :=
  match write_res {
    Result.err e => return (Result.err e),
    Result.ok _ => Client.read_response t method
  }

/// Close a connection (and, under `Transport.secure`, everything the TLS
/// session held: ssl, ctx, socket — `Tls.close` frees in reverse
/// construction order).
def Client.close (conn : Connection) : IO Unit :=
  Transport.close conn.socket

// ── one-shot API ────────────────────────────────────────────────────────

/// Send one request, read the response, close the connection.
/// Follows up to `max_redirects` redirects (0 = no redirect following).
#[terminating]
def Client.request_with (max_redirects : I64) (req : Request) : IO (Result String Response) :=
  Monad.bind (Client.connect (Uri.format req.uri)) (fn conn_res =>
    Client.request_with_conn max_redirects req conn_res)

/// After connecting: send, close, then optionally follow redirects.
def Client.request_with_conn (max_redirects : I64) (req : Request) (conn_res : Result String Connection) : IO (Result String Response) :=
  match conn_res {
    Result.err e => return (Result.err e),
    Result.ok conn =>
      Monad.bind (Client.send conn req) (fn send_res =>
        Client.request_after_send max_redirects req conn send_res)
  }

/// After send: close the connection, then check for redirects.
#[terminating]
def Client.request_after_send (max_redirects : I64) (req : Request) (conn : Connection) (send_res : Result String Response) : IO (Result String Response) :=
  Monad.bind (Client.close conn) (fn _ =>
    Client.request_check_redirect max_redirects req send_res)

/// If the response is a redirect and we have redirects left, follow it.
/// Otherwise return the response as-is.
def Client.request_check_redirect (max_redirects : I64) (req : Request) (send_res : Result String Response) : IO (Result String Response) :=
  match send_res {
    Result.err e => return (Result.err e),
    Result.ok res =>
      if Bool.not (Client.is_redirect res.status)
      then return (Result.ok res)
      else Client.request_follow max_redirects req res
  }

/// Follow a redirect response.
#[terminating]
def Client.request_follow (max_redirects : I64) (req : Request) (res : Response) : IO (Result String Response) :=
  if Bool.not (I64.gt max_redirects 0i64)
  then return (Result.ok res)
  else
    match Headers.get "Location" res.headers {
      Option.none => return (Result.ok res),
      Option.some loc => Client.request_follow_location max_redirects req res loc
    }

/// Parse the Location header, resolve it against the original URI, build the
/// redirect request the status asks for, and recurse via `request_with`.
#[terminating]
def Client.request_follow_location (max_redirects : I64) (req : Request) (res : Response) (loc : String) : IO (Result String Response) :=
  match Uri.parse loc {
    Result.err e => return (Result.err (String.concat "invalid redirect Location: " e)),
    Result.ok redirect_uri =>
      let resolved := Uri.resolve req.uri redirect_uri in
      let new_req := Client.redirect_request req res.status resolved in
      Client.request_with (I64.sub max_redirects 1i64) new_req
  }

// ── redirect policy ─────────────────────────────────────────────────────

/// Is this status code a redirect (301-303, 307-308)?
///
/// 300 and 305 are deliberately absent: 300 carries no `Location` a client has
/// to act on, and 305 names a proxy that may not be reachable at all. The
/// statuses that are here all promise a `Location`.
def Client.is_redirect (status : U16) : Bool :=
  if U16.beq status Status.moved_permanently then true
  else if U16.beq status Status.found then true
  else if U16.beq status Status.see_other then true
  else if U16.beq status Status.temporary_redirect then true
  else if U16.beq status Status.permanent_redirect then true
  else false

/// Whether a redirect is followed with the original method and body.
///
/// 307 and 308 exist to promise exactly that (RFC 9110 §15.4.8, §15.4.9), so
/// they always preserve. 301 and 302 predate the distinction and say nothing,
/// and what clients converged on is "preserve, except turn a POST into a GET"
/// (§15.4.2, §15.4.3) -- a POST is the one method where repeating the request
/// risks doing the work twice. 303 means "ask for it with GET" (§15.4.4).
///
/// A HEAD keeps its method under every status: it is a request for the head of
/// a representation, and answering a redirected HEAD with a GET would deliver
/// a body that was never asked for.
def Client.redirect_preserves (status : U16) (orig : Method) : Bool :=
  if orig == Method.HEAD
  then true
  else if U16.beq status Status.temporary_redirect
  then true
  else if U16.beq status Status.permanent_redirect
  then true
  else if U16.beq status Status.moved_permanently
  then Bool.not (orig == Method.POST)
  else if U16.beq status Status.found
  then Bool.not (orig == Method.POST)
  else false

/// The method a redirect is followed with.
def Client.redirect_method (status : U16) (orig : Method) : Method :=
  if Client.redirect_preserves status orig
  then orig
  else Method.GET

/// Build the request a redirect is followed with.
///
/// The redirect is the same request aimed elsewhere, so its headers come along
/// -- minus the ones describing a body it is no longer sending, and minus the
/// credentials when "elsewhere" is a different origin. A `Location` is chosen
/// by the server being talked to, so following one must not hand a host that
/// server named the credentials this client held for the first one
/// (RFC 9110 §15.4).
def Client.redirect_request (orig : Request) (status : U16) (resolved : Uri) : Request :=
  let preserve : Bool := Client.redirect_preserves status orig.method in
  let headers : Headers := Client.redirect_headers orig.headers orig.uri resolved preserve in
  let body : Body := if preserve then orig.body else Body.empty in
  { method := Client.redirect_method status orig.method, uri := resolved, headers := headers, version := HttpVersion.http1_1, body := body }

/// The headers a redirect request carries.
def Client.redirect_headers (headers : Headers) (from : Uri) (to : Uri) (preserve : Bool) : Headers :=
  let kept : Headers := if preserve then headers else Client.drop_body_headers headers in
  if Uri.same_origin from to
  then kept
  else Client.drop_credentials kept

/// Drop the headers that describe a body.
def Client.drop_body_headers (h : Headers) : Headers :=
  Client.drop_headers (List.cons "Content-Length" (List.singleton "Content-Type")) h

/// Drop the headers that are credentials.
def Client.drop_credentials (h : Headers) : Headers :=
  Client.drop_headers (List.cons "Authorization" (List.cons "Proxy-Authorization" (List.singleton "Cookie"))) h

#[terminating]
def Client.drop_headers (names : List String) (h : Headers) : Headers :=
  match names {
    List.empty => h,
    List.cons n rest => Client.drop_headers rest (Headers.remove n h)
  }

/// One-shot request without redirect following.
def Client.request (req : Request) : IO (Result String Response) :=
  Client.request_with 0i64 req

/// Convenience: GET a URL, follow up to 10 redirects.
def Client.get (url : String) : IO (Result String Response) :=
  match Uri.parse url {
    Result.err e => return (Result.err e),
    Result.ok u =>
      let req := Request.get u in
      Client.request_with 10i64 req
  }

/// Convenience: POST a body to a URL, follow up to 10 redirects.
def Client.post (url : String) (body : Body) : IO (Result String Response) :=
  match Uri.parse url {
    Result.err e => return (Result.err e),
    Result.ok u =>
      let req : Request :=
        { method := Method.POST, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := body }
      in
      Client.request_with 10i64 req
  }
