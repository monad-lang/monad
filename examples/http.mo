// Exercise the pure part of the `http` mote: URI parsing, formatting and
// percent-encoding; the wire format and its framing rules; body handling
// including multipart.
//
// Deliberately socket-free. The `moon` (server) and `moose` (client) motes are
// where TCP lives, and TCP is self-hosted only -- the Rust host has no `tcp_*`
// natives -- so a server or client example would fail this file's own gate
// (`cargo run -- test examples/`). Everything below is pure, and runs under
// both compilers.
#![mote { name := "http_example", deps := [http] }]

use http::types {
  Body, HEAD, Headers.empty, Headers.set, POST, Request, Response, Status.ok, Uri,
  http1_1,
}
use http::body {Body.content_type, Body.parse_multipart, Body.to_bytes_pure}
use http::strings {Strings.drop_bytes}
use http::uri {
  Uri.format, Uri.parse, Uri.percent_decode, Uri.percent_encode, Uri.resolve,
  Uri.same_origin,
}
use http::wire {
  Wire.format_request, Wire.format_response, Wire.frame_request,
  Wire.frame_response, Wire.parse_request, Wire.parse_response,
  Wire.request_target,
}

// ── helpers ─────────────────────────────────────────────────────────────

/// Parse a URI, or an empty one when the text is malformed. Every input below
/// is well-formed, so an error here would be a bug in the example.
def uri (s : String) : Uri :=
  match Uri.parse s {
    Result.err _ => Uri.uri "" Option.none "" Option.none "" Option.none Option.none,
    Result.ok u => u
  }

/// A bodyless GET aimed at `path`, on the origin server the connection
/// already points at -- so the request target is the origin-form path, which
/// is what goes on the wire.
def get_req (path : String) : Request :=
  Request.get (uri path)

/// The wire bytes of a request, as text.
def req_text (req : Request) : String :=
  match Wire.format_request req {
    Result.ok bytes => String.from_list bytes,
    Result.err _ => "SERIALIZE-FAILED"
  }

/// The wire bytes of a response, as text.
def res_text (res : Response) : String :=
  match Wire.format_response res {
    Result.ok bytes => String.from_list bytes,
    Result.err _ => "SERIALIZE-FAILED"
  }

// ── URI ─────────────────────────────────────────────────────────────────

#[test]
def test_percent_roundtrip : Bool :=
  match Uri.percent_decode (Uri.percent_encode "a b&c") {
    Result.err _ => false,
    Result.ok s => String.beq s "a b&c"
  }

/// A URI survives a parse/format round trip, authority, port, query and
/// fragment included.
#[test]
def test_uri_roundtrip : Bool :=
  String.beq (Uri.format (uri "http://user@example.com:8443/a/b?q=1#frag")) "http://user@example.com:8443/a/b?q=1#frag"

/// A non-empty path with no leading `/` still gets one when formatted, so the
/// authority and the path do not run together into `example.comfoo`.
#[test]
def test_uri_format_separates_path : Bool :=
  let no_path : Uri := Uri.uri "http" Option.none "example.com" Option.none "foo" Option.none Option.none in
  String.beq (Uri.format no_path) "http://example.com/foo"

/// A relative `Location` resolves against the response's own URL, replacing
/// only its last path segment.
#[test]
def test_uri_resolve_relative : Bool :=
  let base : Uri := uri "http://example.com/a/b" in
  let ref : Uri := uri "c" in
  String.beq (Uri.format (Uri.resolve base ref)) "http://example.com/a/c"

/// A rooted `Location` replaces the whole path, not just its tail.
#[test]
def test_uri_resolve_absolute : Bool :=
  let base : Uri := uri "http://example.com/a/b" in
  let ref : Uri := uri "/x/y" in
  String.beq (Uri.format (Uri.resolve base ref)) "http://example.com/x/y"

/// A port past `65535` is rejected. It used to accumulate into a `U16` and
/// come out as `4464`: a wrong port on a URI that parsed "successfully".
#[test]
def test_uri_port_out_of_range_fails : Bool :=
  match Uri.parse "http://example.com:70000/" {
    Result.err _ => true,
    Result.ok _ => false
  }

/// `http://example.com` and `http://example.com:80` are one origin.
#[test]
def test_same_origin_effective_port : Bool :=
  Uri.same_origin (uri "http://example.com/") (uri "http://example.com:80/")

// ── wire format ─────────────────────────────────────────────────────────

/// A request serialises to bytes that parse back to the same request. The
/// parser hands back a `Body.bytes`, not the `Body.text` that went in: the
/// wire carries octets, and only the content type says they were text.
#[test]
def test_request_roundtrip : Bool :=
  let req : Request :=
    { method := Method.POST, uri := uri "/api", headers := Headers.set "X-Test" "yes" Headers.empty, version := HttpVersion.http1_1, body := Body.text "data" } in
  match Wire.parse_request (String.to_list (req_text req)) {
    Result.err _ => false,
    Result.ok parsed =>
      Bool.and (parsed.method == Method.POST)
        (Bool.and (String.beq (Wire.request_target parsed.uri) "/api")
          (match parsed.body {
            Body.bytes bs => String.beq (String.from_list bs) "data",
            Body.text s => String.beq s "data",
            Body.empty => false,
            Body.stream _ => false,
            Body.form _ => false
          }))
  }

/// The request line, the headers and the body are separated the way the wire
/// format says: CRLF after the request line, CRLF CRLF before the body. The
/// header names come out lowercased, since that is how they are stored.
#[test]
def test_request_wire_shape : Bool :=
  String.beq (req_text (get_req "/")) "GET / HTTP/1.1\r\ncontent-length: 0\r\n\r\n"

#[test]
def test_response_roundtrip : Bool :=
  match Wire.parse_response (String.to_list (res_text (Response.ok_text "hi"))) {
    Result.err _ => false,
    Result.ok parsed =>
      Bool.and (U16.beq parsed.status Status.ok)
        (match parsed.body {
          Body.bytes bs => String.beq (String.from_list bs) "hi",
          Body.text s => String.beq s "hi",
          Body.empty => false,
          Body.stream _ => false,
          Body.form _ => false
        })
  }

// ── framing ─────────────────────────────────────────────────────────────

/// Framing honours `Content-Length`, so bytes after it belong to the next
/// message rather than to this one's body. A reader that took everything
/// buffered would swallow the pipelined request behind it.
#[test]
def test_frame_keeps_pipelined_request : Bool :=
  let two : List U8 := String.to_list "POST /a HTTP/1.1\r\nContent-Length: 3\r\n\r\nhelGET /b HTTP/1.1\r\n\r\n" in
  match Wire.frame_request two {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n => String.beq (String.from_list (Strings.drop_bytes n two)) "GET /b HTTP/1.1\r\n\r\n"
      }
  }

/// A body that has not fully arrived is "not yet", not an error: a single
/// socket read lands here routinely.
#[test]
def test_frame_incomplete_is_not_an_error : Bool :=
  match Wire.frame_request (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nab") {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => true,
        Option.some _ => false
      }
  }

/// Two `Content-Length` headers that disagree are a request-smuggling shape --
/// one hop honours the first and the next honours the second -- so the message
/// cannot be framed at all.
#[test]
def test_frame_conflicting_length_fails : Bool :=
  match Wire.frame_request (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello") {
    Result.err _ => true,
    Result.ok _ => false
  }

/// Chunked framing is not implemented, so a message that declares it is
/// rejected rather than mis-framed.
#[test]
def test_frame_transfer_encoding_fails : Bool :=
  match Wire.frame_request (String.to_list "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n") {
    Result.err _ => true,
    Result.ok _ => false
  }

/// A response to a `HEAD` carries the `Content-Length` of the body it is not
/// sending, so the method has to reach the frame: honouring that number leaves
/// a client waiting for bytes that never come.
#[test]
def test_frame_head_response_has_no_body : Bool :=
  match Wire.frame_response (String.to_list head_res_text) Method.HEAD {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n => I64.beq n head_res_bytes
      }
  }

/// The message above with no body attached: `HTTP/1.1 200 OK` (15) + CRLF (2) +
/// `Content-Length: 5` (17) + CRLF (2) + CRLF (2) = 38 bytes.
def head_res_text : String := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n"
def head_res_bytes : I64 := 38

/// A body shorter than its `Content-Length` is a truncation, not a short body.
#[test]
def test_parse_short_body_fails : Bool :=
  match Wire.parse_request (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nab") {
    Result.err _ => true,
    Result.ok _ => false
  }

// ── body ────────────────────────────────────────────────────────────────

/// A form body encodes as `application/x-www-form-urlencoded` and declares
/// that content type itself.
#[test]
def test_body_form : Bool :=
  let fields : List (Pair String String) := List.cons (Pair.pair "a" "1") (List.cons (Pair.pair "b" "2") List.empty) in
  let b : Body := Body.form fields in
  let bytes : List U8 := Body.to_bytes_pure b in
  Bool.and (String.beq (String.from_list bytes) "a=1&b=2") (String.beq (Body.content_type b) "application/x-www-form-urlencoded")

/// A `multipart/form-data` body parses into its parts, with the name and
/// filename from each part's `Content-Disposition`.
#[test]
def test_body_multipart : Bool :=
  let body_str := "--B\r\nContent-Disposition: form-data; name=\"file\"; filename=\"a.txt\"\r\nContent-Type: text/plain\r\n\r\nhello\r\n--B--\r\n" in
  match Body.parse_multipart "B" (String.to_list body_str) {
    Result.err _ => false,
    Result.ok parts =>
      match parts {
        List.empty => false,
        List.cons p1 rest =>
          match rest {
            List.empty =>
              Bool.and (String.beq p1.name "file") (String.beq (String.from_list p1.data) "hello"),
            List.cons _ _ => false
          }
      }
  }

/// A body that stops at a boundary token with no closing `--` is truncated,
/// not a body with zero parts.
#[test]
def test_body_multipart_truncated_fails : Bool :=
  match Body.parse_multipart "B" (String.to_list "--B") {
    Result.err _ => true,
    Result.ok _ => false
  }

/// The read function of a streaming body. The serialiser refuses a stream
/// before reading it, so this is never called.
def no_chunk : IO (Option (List U8)) := do {
  return Option.none
}

/// A `Body.stream` has no pure byte form, and serialising one is an error --
/// rendering it as `Content-Length: 0` would be byte-for-byte what an empty
/// body produces, so the peer could not tell that a body it was promised never
/// arrived.
#[test]
def test_stream_body_fails_to_serialise : Bool :=
  let req : Request :=
    { method := Method.POST, uri := uri "http://example.com/upload", headers := Headers.empty, version := HttpVersion.http1_1, body := Body.stream no_chunk } in
  match Wire.format_request req {
    Result.err _ => true,
    Result.ok _ => false
  }
