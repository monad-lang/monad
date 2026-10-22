/// HTTP core types — Layer 0, pure Monad.
///
/// Shared by the `moose` client and `moon` server motes. Depends only on the
/// auto-loaded stdlib (`String`, `List`, `Option`, `Pair`, `U16`, `U8`, `IO`)
/// plus `std.show` for the `Show` class and, for `Transport`, `std.stream`'s
/// byte streams over `std.bytebuf`'s buffers.

use std::show {Show}
use std::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.length, ByteBuf.of_list, ByteBuf.to_list}
use std::stream {Stream, StreamError, FdStream}

// ── Method ──────────────────────────────────────────────────────────────
// Variants mirror RFC 9110 §9.

pub type Method {
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

pub type HttpVersion {
  http1_0,
  http1_1
}
open HttpVersion { http1_0, http1_1 }

// ── Status ──────────────────────────────────────────────────────────────
// Status codes as U16 with named constants. An enum of 60+ variants is
// avoided; users write `Status.ok`, `Status.not_found`, etc. `Response.status`
// holds a raw `U16`, so these are plain `U16` values, not a distinct type.

pub def Status.ok : U16 := 200u16
pub def Status.created : U16 := 201u16
pub def Status.accepted : U16 := 202u16
pub def Status.no_content : U16 := 204u16
pub def Status.moved_permanently : U16 := 301u16
pub def Status.found : U16 := 302u16
pub def Status.see_other : U16 := 303u16
pub def Status.not_modified : U16 := 304u16
pub def Status.temporary_redirect : U16 := 307u16
pub def Status.permanent_redirect : U16 := 308u16
pub def Status.bad_request : U16 := 400u16
pub def Status.unauthorized : U16 := 401u16
pub def Status.forbidden : U16 := 403u16
pub def Status.not_found : U16 := 404u16
pub def Status.method_not_allowed : U16 := 405u16
pub def Status.conflict : U16 := 409u16
pub def Status.internal_server_error : U16 := 500u16
pub def Status.bad_gateway : U16 := 502u16
pub def Status.service_unavailable : U16 := 503u16

// ── Headers ─────────────────────────────────────────────────────────────
// A list of key/value pairs with case-insensitive key lookup. Keys are
// lowercased on insert (`Headers.set`/`Headers.add`), so lookups are a plain
// `List` scan against an already-lowercased stored key.

pub type Headers {
  headers (pairs : List (Pair String String))
}
open Headers { headers }

pub def Headers.empty : Headers :=
  Headers.headers List.empty

pub def Headers.get (key : String) (h : Headers) : Option String :=
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

pub def Headers.set (key : String) (val : String) (h : Headers) : Headers :=
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

pub def Headers.add (key : String) (val : String) (h : Headers) : Headers :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => Headers.headers (List.cons (Pair.pair lk val) pairs)
  }

/// Drop every value stored under `key`. Absent is not an error.
pub def Headers.remove (key : String) (h : Headers) : Headers :=
  let lk : String := String.to_lowercase key in
  match h {
    Headers.headers pairs => Headers.headers (headers_remove lk pairs)
  }

pub def Headers.is_empty (h : Headers) : Bool :=
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
pub def Headers.get_all (key : String) (h : Headers) : List String :=
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

pub type Uri {
  uri (scheme : String) (userinfo : Option String) (host : String) (port : Option U16) (path : String) (query : Option String) (fragment : Option String)
}
open Uri { uri }

pub def Uri.host (u : Uri) : String :=
  match u {
    Uri.uri _ _ h _ _ _ _ => h
  }

// ── Body ────────────────────────────────────────────────────────────────
// A tagged union of transport representations, not content types. No `Json`
// variant: JSON encoding is the caller's responsibility (keeps the motes free
// of a serialization dependency). Callers pass `Body.bytes` with already-
// encoded JSON and set `Content-Type` themselves.

pub type Body {
  empty,
  bytes (data : List U8),
  text (data : String),
  stream (read : IO (Option (List U8))),
  form (fields : List (Pair String String))
}
open Body { empty, bytes, text, stream, form }

pub def Body.is_empty (b : Body) : Bool :=
  match b {
    Body.empty => true,
    Body.bytes _ => false,
    Body.text _ => false,
    Body.stream _ => false,
    Body.form _ => false
  }

pub def Body.is_text (b : Body) (s : String) : Bool :=
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
//
// Both arms speak `Stream`'s contract (std/stream.mo): a read hands back
// a `ByteBuf` the caller frees, a zero-length one at end of stream; a
// write writes the whole buffer, which stays the caller's to free.

pub type Transport {
  plain (s : FdStream),
  secure (read : I64 -> IO (Result StreamError ByteBuf))
         (write : ByteBuf -> IO (Result StreamError I64))
         (close : Unit -> IO Unit)
}
open Transport { plain, secure }

pub def Transport.read (t : Transport) (max : I64) : IO (Result StreamError ByteBuf) :=
  match t {
    Transport.plain s => Stream.read s max,
    Transport.secure read _ _ => read max
  }

pub def Transport.write (t : Transport) (buf : ByteBuf) : IO (Result StreamError I64) :=
  match t {
    Transport.plain s => Stream.write s buf,
    Transport.secure _ write _ => write buf
  }

// `close` takes a `Unit` where the two payload fields are called with the
// values they act on: in the compiled backend an action stored in a ctor
// field executes at CONSTRUCTION, and a closure stored in an action-typed
// field crashes when the arm returns it for execution — the call is the one
// shape that survives (probed 2026-10-08; `Body.stream`'s action field is
// the same trap, never constructed anywhere).
pub def Transport.close (t : Transport) : IO Unit :=
  match t {
    Transport.plain s => Stream.close s,
    Transport.secure _ _ close => close unit
  }

// The wire parsers work on `List U8`, so the clients and servers above the
// transport convert at this boundary, once per read and once per write.
// Errors become their `message`: callers report failures as text.

/// One read of at most `max` bytes as a list; `Result.ok List.empty` at
/// end of stream.
pub def Transport.read_bytes (t : Transport) (max : I64) : IO (Result String (List U8)) := do {
  let r <- Transport.read t max;
  Transport.read_bytes_got r
}

def Transport.read_bytes_got (r : Result StreamError ByteBuf) : IO (Result String (List U8)) :=
  match r {
    Result.err e => IO.pure (Result.err e.message),
    Result.ok buf => Transport.buf_bytes buf
  }

def Transport.buf_bytes (buf : ByteBuf) : IO (Result String (List U8)) := do {
  let bytes <- ByteBuf.to_list buf (ByteBuf.length buf);
  let _ <- ByteBuf.free buf;
  return (Result.ok bytes)
}

/// Write all of `bytes`; the ok payload is the full length.
pub def Transport.write_bytes (t : Transport) (bytes : List U8) : IO (Result String U64) := do {
  let buf <- ByteBuf.of_list bytes;
  let r <- Transport.write t buf;
  let _ <- ByteBuf.free buf;
  return (Transport.wrote r)
}

def Transport.wrote (r : Result StreamError I64) : Result String U64 :=
  match r {
    Result.err e => Result.err e.message,
    Result.ok n => Result.ok (I64.to_u64 n)
  }

// ── Framing ─────────────────────────────────────────────────────────────
// How a message's body is delimited (RFC 9110 §6.3). `no_body` is not the
// same as a length of zero: a HEAD response and a 204 both carry a
// `Content-Length` describing the representation the request *would* have
// returned, and treating that number as a frame is how a client ends up
// waiting for a body the server is never going to send. `until_eof` is the
// HTTP/1.0 read-to-close case, where the end of the body is the end of the
// connection and is only known once the peer closes it. `chunked` is
// `Transfer-Encoding: chunked`: the body is a sequence of hex-sized chunks
// terminated by a zero chunk, so the end is knowable in-stream without
// either a length or a close.

pub type Framing {
  content_length (len : I64),
  chunked,
  until_eof,
  no_body
}
open Framing { content_length, chunked, until_eof, no_body }

// ── Request / Response ──────────────────────────────────────────────────

pub struct Request {
  method : Method,
  uri : Uri,
  headers : Headers,
  version : HttpVersion,
  body : Body,
  params : List (Pair String String) := List.empty
}

pub struct Response {
  status : U16,
  headers : Headers,
  version : HttpVersion,
  body : Body
}

/// Convenience constructor: a GET request with empty headers, HTTP/1.1, no body.
pub def Request.get (uri : Uri) : Request :=
  { method := Method.GET, uri := uri, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// Convenience constructor: a 200 response with a text body and empty headers.
pub def Response.ok_text (s : String) : Response :=
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
