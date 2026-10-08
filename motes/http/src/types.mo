/// HTTP core types — Layer 0, pure Monad.
///
/// Shared by the `moose` client and `moon` server motes. Depends only on the
/// auto-loaded stdlib (`String`, `List`, `Option`, `Pair`, `U16`, `U8`, `IO`)
/// plus `std.show` for the `Show` class.

use std::show {Show}

// ── Method ──────────────────────────────────────────────────────────────
// Variants mirror RFC 9110 §9.

type Method {
  GET,
  HEAD,
  POST,
  PUT,
  DELETE,
  CONNECT,
  OPTIONS,
  TRACE,
  PATCH
}
open Method { GET, HEAD, POST, PUT, DELETE, CONNECT, OPTIONS, TRACE, PATCH }

// ── HttpVersion ─────────────────────────────────────────────────────────

type HttpVersion {
  http1_0,
  http1_1
}
open HttpVersion { http1_0, http1_1 }

// ── Status ──────────────────────────────────────────────────────────────
// Status codes as U16 with named constants. An enum of 60+ variants is
// avoided; users write `Status.ok`, `Status.not_found`, etc. `Response.status`
// holds a raw `U16`, so these are plain `U16` values, not a distinct type.

def Status.ok : U16 := 200u16
def Status.created : U16 := 201u16
def Status.accepted : U16 := 202u16
def Status.no_content : U16 := 204u16
def Status.moved_permanently : U16 := 301u16
def Status.found : U16 := 302u16
def Status.see_other : U16 := 303u16
def Status.not_modified : U16 := 304u16
def Status.temporary_redirect : U16 := 307u16
def Status.permanent_redirect : U16 := 308u16
def Status.bad_request : U16 := 400u16
def Status.unauthorized : U16 := 401u16
def Status.forbidden : U16 := 403u16
def Status.not_found : U16 := 404u16
def Status.method_not_allowed : U16 := 405u16
def Status.conflict : U16 := 409u16
def Status.internal_server_error : U16 := 500u16
def Status.bad_gateway : U16 := 502u16
def Status.service_unavailable : U16 := 503u16

// ── Headers ─────────────────────────────────────────────────────────────
// A list of key/value pairs with case-insensitive key lookup. Keys are
// lowercased on insert (`Headers.set`/`Headers.add`), so lookups are a plain
// `List` scan against an already-lowercased stored key.

type Headers {
  headers (pairs : List (Pair String String))
}
open Headers { headers }

def Headers.empty : Headers :=
  Headers.headers List.empty

def Headers.get (key : String) (h : Headers) : Option String :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => headers_lookup lk pairs
  }

def headers_lookup (lk : String) (pairs : List (Pair String String)) : Option String :=
  match pairs {
    List.empty => Option.none,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq lk k
          then Option.some v
          else headers_lookup lk rest
      }
  }

def Headers.set (key : String) (val : String) (h : Headers) : Headers :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs =>
      Headers.headers (List.cons (Pair.pair lk val) (headers_remove lk pairs))
  }

def headers_remove (lk : String) (pairs : List (Pair String String)) : List (Pair String String) :=
  match pairs {
    List.empty => List.empty,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq lk k
          then headers_remove lk rest
          else List.cons (Pair.pair k v) (headers_remove lk rest)
      }
  }

def Headers.add (key : String) (val : String) (h : Headers) : Headers :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => Headers.headers (List.cons (Pair.pair lk val) pairs)
  }

/// Drop every value stored under `key`. Absent is not an error.
def Headers.remove (key : String) (h : Headers) : Headers :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => Headers.headers (headers_remove lk pairs)
  }

def Headers.is_empty (h : Headers) : Bool :=
  match h {
    Headers.headers pairs => List.is_empty pairs
  }

/// Every value stored under `key`, in stored (front-of-list) order.
///
/// `Headers.get` answers with the first match, which is the right shape for a
/// header that may appear at most once and hides a duplicate. `Content-Length`
/// is the header where a duplicate matters -- two disagreeing values are a
/// request-smuggling shape, not a precedence question -- so framing needs to
/// see all of them.
def Headers.get_all (key : String) (h : Headers) : List String :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => headers_lookup_all lk pairs
  }

def headers_lookup_all (lk : String) (pairs : List (Pair String String)) : List String :=
  match pairs {
    List.empty => List.empty,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq lk (String.to_lowercase k)
          then List.cons v (headers_lookup_all lk rest)
          else headers_lookup_all lk rest
      }
  }

// ── Uri ─────────────────────────────────────────────────────────────────
// Structured URI. Built by the parser (uri.mo), never hand-constructed.

type Uri {
  uri (scheme : String) (userinfo : Option String) (host : String) (port : Option U16) (path : String) (query : Option String) (fragment : Option String)
}
open Uri { uri }

def Uri.host (u : Uri) : String :=
  match u {
    Uri.uri _ _ h _ _ _ _ => h
  }

// ── Body ────────────────────────────────────────────────────────────────
// A tagged union of transport representations, not content types. No `Json`
// variant: JSON encoding is the caller's responsibility (keeps the motes free
// of a serialization dependency). Callers pass `Body.bytes` with already-
// encoded JSON and set `Content-Type` themselves.

type Body {
  empty,
  bytes (data : List U8),
  text (data : String),
  stream (read : IO (Option (List U8))),
  form (fields : List (Pair String String))
}
open Body { empty, bytes, text, stream, form }

def Body.is_empty (b : Body) : Bool :=
  match b {
    Body.empty => true,
    Body.bytes _ => false,
    Body.text _ => false,
    Body.stream _ => false,
    Body.form _ => false
  }

def Body.is_text (b : Body) (s : String) : Bool :=
  match b {
    Body.text data => String.beq data s,
    Body.empty => false,
    Body.bytes _ => false,
    Body.stream _ => false,
    Body.form _ => false
  }

// ── Transport ───────────────────────────────────────────────────────────
// A tagged union of byte-level transports, so `moose` (and later `moon`)
// can speak either scheme without this mote learning what TLS is: the
// `secure` arm carries read/write/close CLOSURES rather than a
// `Tls.Stream`, which keeps the dependency (and the `-lssl` link flag)
// opt-in at the mote level -- `http` depends on neither, and `moose` is
// where the two are joined, at connect time. `Body.stream` above is the
// precedent for a closure-carrying constructor field.

type Transport {
  plain (sock : Socket),
  secure (read : U64 -> IO (Result String (List U8)))
         (write : List U8 -> IO (Result String U64))
         (close : Unit -> IO Unit)
}
open Transport { plain, secure }

def Transport.read (t : Transport) (max : U64) : IO (Result String (List U8)) :=
  match t {
    Transport.plain sock => IO.tcp_read sock max,
    Transport.secure read _ _ => read max
  }

def Transport.write (t : Transport) (data : List U8) : IO (Result String U64) :=
  match t {
    Transport.plain sock => IO.tcp_write sock data,
    Transport.secure _ write _ => write data
  }

// `close` takes a `Unit` where the two payload fields are called with the
// values they act on: in the compiled backend an action stored in a ctor
// field executes at CONSTRUCTION, and a closure stored in an action-typed
// field crashes when the arm returns it for execution — the call is the one
// shape that survives (probed 2026-10-08; `Body.stream`'s action field is
// the same trap, never constructed anywhere).
def Transport.close (t : Transport) : IO Unit :=
  match t {
    Transport.plain sock => IO.tcp_close sock,
    Transport.secure _ _ close => close unit
  }

// ── Framing ─────────────────────────────────────────────────────────────
// How a message's body is delimited (RFC 9110 §6.3). `no_body` is not the
// same as a length of zero: a HEAD response and a 204 both carry a
// `Content-Length` describing the representation the request *would* have
// returned, and treating that number as a frame is how a client ends up
// waiting for a body the server is never going to send. `until_eof` is the
// HTTP/1.0 read-to-close case, where the end of the body is the end of the
// connection and is only known once the peer closes it.

type Framing {
  content_length (len : I64),
  until_eof,
  no_body
}
open Framing { content_length, until_eof, no_body }

// ── Request / Response ──────────────────────────────────────────────────

struct Request {
  method : Method,
  uri : Uri,
  headers : Headers,
  version : HttpVersion,
  body : Body,
  params : List (Pair String String) := List.empty
}

struct Response {
  status : U16,
  headers : Headers,
  version : HttpVersion,
  body : Body
}

/// Convenience constructor: a GET request with empty headers, HTTP/1.1, no body.
def Request.get (uri : Uri) : Request :=
  { method := Method.GET, uri := uri, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// Convenience constructor: a 200 response with a text body and empty headers.
def Response.ok_text (s : String) : Response :=
  { status := Status.ok, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text s }

// ── Instances ───────────────────────────────────────────────────────────

def Method.to_i64 (m : Method) : I64 :=
  match m {
    Method.GET => 0,
    Method.HEAD => 1,
    Method.POST => 2,
    Method.PUT => 3,
    Method.DELETE => 4,
    Method.CONNECT => 5,
    Method.OPTIONS => 6,
    Method.TRACE => 7,
    Method.PATCH => 8
  }

instance BEq Method {
  def beq (a b : Method) : Bool := I64.beq (Method.to_i64 a) (Method.to_i64 b)
}

instance Show Method {
  def show (m : Method) : String :=
    match m {
      Method.GET => "GET",
      Method.HEAD => "HEAD",
      Method.POST => "POST",
      Method.PUT => "PUT",
      Method.DELETE => "DELETE",
      Method.CONNECT => "CONNECT",
      Method.OPTIONS => "OPTIONS",
      Method.TRACE => "TRACE",
      Method.PATCH => "PATCH"
    }
}

def HttpVersion.to_i64 (v : HttpVersion) : I64 :=
  match v {
    HttpVersion.http1_0 => 0,
    HttpVersion.http1_1 => 1
  }

instance BEq HttpVersion {
  def beq (a b : HttpVersion) : Bool := I64.beq (HttpVersion.to_i64 a) (HttpVersion.to_i64 b)
}

instance Show HttpVersion {
  def show (v : HttpVersion) : String :=
    match v {
      HttpVersion.http1_0 => "HTTP/1.0",
      HttpVersion.http1_1 => "HTTP/1.1"
    }
}
