/// Phase 3 tests — HTTP/1.1 wire format parse/serialize roundtrips.

use http::types {
  Body, Framing, Headers, HttpVersion, Method, Request, Response, Response.no_content,
  Response.text, Response.with_header, Response.with_status, Status.created, Status.no_content,
  Status.not_found, Status.not_modified, Status.ok, Uri,
}
use http::body {Body.length, Body.to_bytes_pure}
use http::strings {Strings.drop_bytes}
use http::wire {
  Wire.chunk_step, Wire.body_bytes, Wire.content_length_of,
  Wire.format_request, Wire.format_response, Wire.format_response_head,
  Wire.frame_request,
  Wire.frame_response, Wire.parse_chunk_size, Wire.parse_content_length,
  Wire.parse_method, Wire.parse_request, Wire.parse_response,
  Wire.parse_response_with_method, Wire.parse_u16, Wire.parse_version,
  Wire.request_target, Wire.request_framing, Wire.response_has_body,
  Wire.split_lines, Wire.take_bytes,
}

def expect_ok_req (got : Result String Request) (want_method : Method) (want_path : String) : Bool :=
  match got {
    Result.err _ => false,
    Result.ok req =>
      req.method == want_method
        && Wire.request_target req.uri == want_path
        && Body.is_empty req.body
  }

def expect_ok_res (got : Result String Response) (want_status : U16) : Bool :=
  match got {
    Result.err _ => false,
    Result.ok res => res.status == want_status
  }

// ── serialisation helpers ──────────────────────────────────────────────
//
// Formatting a message reports failure now that a `Body.stream` has no pure
// byte form (see the streaming section below), so a test that expects success
// unwraps, and the ones that expect the failure say so.

/// The wire bytes of a request, as text.
def w_req_text (req : Request) : String :=
  match Wire.format_request req {
    Result.ok bytes => String.from_list bytes,
    Result.err _ => "SERIALIZE-FAILED"
  }

def w_res_text (res : Response) : String :=
  match Wire.format_response res {
    Result.ok bytes => String.from_list bytes,
    Result.err _ => "SERIALIZE-FAILED"
  }

def w_req_fails (req : Request) : Bool :=
  match Wire.format_request req {
    Result.err _ => true,
    Result.ok _ => false
  }

def w_res_fails (res : Response) : Bool :=
  match Wire.format_response res {
    Result.err _ => true,
    Result.ok _ => false
  }

/// Serialise a request, then parse the bytes back.
def w_reparse_request (req : Request) : Result String Request :=
  match Wire.format_request req {
    Result.err e => Result.err e,
    Result.ok bytes => Wire.parse_request bytes
  }

def w_reparse_response (res : Response) : Result String Response :=
  match Wire.format_response res {
    Result.err e => Result.err e,
    Result.ok bytes => Wire.parse_response bytes
  }

#[test]
def test_format_simple_get : Bool :=
  let u : Uri := Uri.uri "" Option.none "" Option.none "/" Option.none Option.none in
  let req : Request := { method := Method.GET, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty } in
  String.beq (w_req_text req) "GET / HTTP/1.1\r\ncontent-length: 0\r\n\r\n"

#[test]
def test_format_response_ok_text : Bool :=
  let res : Response := Response.ok_text "hello" in
  String.beq (w_res_text res) "HTTP/1.1 200 \r\ncontent-length: 5\r\n\r\nhello"

#[test]
def test_parse_simple_get : Bool :=
  let bytes := String.to_list "GET /path HTTP/1.1\r\nHost: example.com\r\n\r\n" in
  expect_ok_req (Wire.parse_request bytes) Method.GET "/path"

#[test]
def test_parse_response : Bool :=
  let bytes := String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" in
  expect_ok_res (Wire.parse_response bytes) 200u16

#[test]
def test_parse_response_with_body : Bool :=
  let bytes := String.to_list "HTTP/1.1 404 Not Found\r\nContent-Length: 4\r\n\r\nbody" in
  match Wire.parse_response bytes {
    Result.err _ => false,
    Result.ok res =>
      res.status == 404u16
        && match res.body {
          Body.bytes bs => String.beq (String.from_list bs) "body",
          Body.empty => false,
          Body.text _ => false,
          Body.stream _ => false,
          Body.form _ => false
        }
  }

#[test]
def test_wire_request_roundtrip : Bool :=
  let u : Uri := Uri.uri "" Option.none "" Option.none "/api/v1/users" Option.none Option.none in
  let req : Request := { method := Method.POST, uri := u, headers := Headers.set "X-Test" "yes" Headers.empty, version := HttpVersion.http1_1, body := Body.text "data" } in
  match w_reparse_request req {
    Result.err _ => false,
    Result.ok parsed =>
      parsed.method == Method.POST
        && Wire.request_target parsed.uri == "/api/v1/users"
        && parsed.version == HttpVersion.http1_1
        && match parsed.body {
          Body.bytes bs => String.beq (String.from_list bs) "data",
          Body.text s => s == "data",
          Body.empty => false,
          Body.stream _ => false,
          Body.form _ => false
        }
  }

#[test]
def test_wire_response_roundtrip : Bool :=
  let res : Response := { status := Status.created, headers := Headers.set "X-Custom" "val" Headers.empty, version := HttpVersion.http1_1, body := Body.text "created" } in
  match w_reparse_response res {
    Result.err _ => false,
    Result.ok parsed =>
      parsed.status == Status.created
        && parsed.version == HttpVersion.http1_1
        && match parsed.body {
          Body.bytes bs => String.beq (String.from_list bs) "created",
          Body.text s => s == "created",
          Body.empty => false,
          Body.stream _ => false,
          Body.form _ => false
        }
  }

#[test]
def test_parse_request_with_headers : Bool :=
  let bytes := String.to_list "GET / HTTP/1.1\r\nHost: a.com\r\nAccept: text/html\r\n\r\n" in
  match Wire.parse_request bytes {
    Result.err _ => false,
    Result.ok req =>
      req.method == Method.GET
        && match Headers.get "host" req.headers {
          Option.some v => v == "a.com",
          Option.none => false
        }
        && match Headers.get "accept" req.headers {
          Option.some v => v == "text/html",
          Option.none => false
        }
  }

#[test]
def test_split_lines_basic : Bool :=
  match Wire.split_lines (String.to_list "a\r\nb\r\nc") {
    List.empty => false,
    List.cons l1 r1 =>
      match r1 {
        List.empty => false,
        List.cons l2 r2 =>
          match r2 {
            List.empty => false,
            List.cons l3 r3 =>
              match r3 {
                List.empty => String.beq (String.from_list l1) "a" && String.beq (String.from_list l2) "b" && String.beq (String.from_list l3) "c",
                List.cons _ _ => false
              }
          }
      }
  }

#[test]
def test_format_request_absolute_uri : Bool :=
  let u : Uri := Uri.uri "http" Option.none "example.com" Option.none "/path" Option.none Option.none in
  let req : Request := { method := Method.GET, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty } in
  String.beq (w_req_text req) "GET http://example.com/path HTTP/1.1\r\ncontent-length: 0\r\n\r\n"

/// A PUT request carries its body like a POST; the method is the only
/// difference in the request line.
#[test]
def test_format_put_with_body : Bool :=
  let u : Uri := Uri.uri "" Option.none "" Option.none "/item" Option.none Option.none in
  let req : Request := { method := Method.PUT, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "abc" } in
  String.beq (w_req_text req) "PUT /item HTTP/1.1\r\ncontent-length: 3\r\n\r\nabc"

#[test]
def test_parse_method_all : Bool :=
  match Wire.parse_method "GET" {
    Result.ok m1 => m1 == Method.GET
      && match Wire.parse_method "POST" {
        Result.ok m2 => m2 == Method.POST
          && match Wire.parse_method "DELETE" {
            Result.ok m3 => m3 == Method.DELETE
              && match Wire.parse_method "PATCH" {
                Result.ok m4 => m4 == Method.PATCH
                  && match Wire.parse_method "PUT" {
                    Result.ok m5 => m5 == Method.PUT,
                    Result.err _ => false
                  },
                Result.err _ => false
              },
            Result.err _ => false
          },
        Result.err _ => false
      },
    Result.err _ => false
  }

#[test]
def test_parse_method_unknown : Bool :=
  match Wire.parse_method "BOGUS" {
    Result.ok _ => false,
    Result.err _ => true
  }

#[test]
def test_parse_version : Bool :=
  match Wire.parse_version "HTTP/1.0" {
    Result.ok v1 => v1 == HttpVersion.http1_0
      && match Wire.parse_version "HTTP/1.1" {
        Result.ok v2 => v2 == HttpVersion.http1_1,
        Result.err _ => false
      },
    Result.err _ => false
  }

// ── status range ───────────────────────────────────────────────────────

/// True when a status parse failed.
def w_u16_fails (got : Result String U16) : Bool :=
  match got {
    Result.err _ => true,
    Result.ok _ => false
  }

/// True when a status parse succeeded with exactly `want`.
def w_u16_is (got : Result String U16) (want : U16) : Bool :=
  match got {
    Result.err _ => false,
    Result.ok v => U16.beq v want
  }

#[test]
def test_parse_status_ok : Bool :=
  w_u16_is (Wire.parse_u16 "200") 200u16

#[test]
def test_parse_status_boundary_ok : Bool :=
  w_u16_is (Wire.parse_u16 "65535") 65535u16

/// `70000` truncated to `4464` before the bound was added, so a malformed
/// status line parsed as a real status.
#[test]
def test_parse_status_out_of_range_fails : Bool :=
  w_u16_fails (Wire.parse_u16 "70000")

#[test]
def test_parse_status_empty_fails : Bool :=
  w_u16_fails (Wire.parse_u16 "")

#[test]
def test_parse_status_non_digit_fails : Bool :=
  w_u16_fails (Wire.parse_u16 "20x")

// ── framing ────────────────────────────────────────────────────────────
//
// Framing decides how many bytes of a buffer belong to the first message. The
// parser used to call everything after the header block a body, which swallowed
// the next pipelined request; these tests pin the boundary and the leftover.

/// True when the parsed body's bytes are exactly `want`.
def w_body_is (b : Body) (want : String) : Bool :=
  match b {
    Body.bytes bs => String.beq (String.from_list bs) want,
    Body.empty => String.beq want "",
    Body.text s => String.beq s want,
    Body.stream _ => false,
    Body.form _ => false
  }

/// True when `n` bytes of `bytes` parse as a message whose body is
/// `want_body`, leaving exactly `want_rest` behind.
def w_framed_ok (n : I64) (bytes : List U8) (want_body : String) (want_rest : String) : Bool :=
  if Bool.not (String.from_list (Strings.drop_bytes n bytes) == want_rest)
  then false
  else
    match Wire.parse_request (Wire.take_bytes n bytes) {
      Result.err _ => false,
      Result.ok req => w_body_is req.body want_body
    }

/// Frame the first request in `bytes` and check its body and its leftover.
def w_frames_to (bytes : List U8) (want_body : String) (want_rest : String) : Bool :=
  match Wire.frame_request bytes {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n => w_framed_ok n bytes want_body want_rest
      }
  }

/// True when the buffer does not hold a whole request yet.
def w_frame_incomplete (bytes : List U8) : Bool :=
  match Wire.frame_request bytes {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => true,
        Option.some _ => false
      }
  }

/// True when the request head cannot be trusted to frame at all.
def w_frame_bad (bytes : List U8) : Bool :=
  match Wire.frame_request bytes {
    Result.err _ => true,
    Result.ok _ => false
  }

/// True when the parsed request's body is exactly `want`.
def w_parsed_body_is (bytes : List U8) (want : String) : Bool :=
  match Wire.parse_request bytes {
    Result.err _ => false,
    Result.ok req => w_body_is req.body want
  }

def w_parse_fails (bytes : List U8) : Bool :=
  match Wire.parse_request bytes {
    Result.err _ => true,
    Result.ok _ => false
  }

/// True when `n` bytes of `bytes` parse as a response to `method` whose body is
/// `want_body`, leaving exactly `want_rest` behind.
def w_res_framed_ok (n : I64) (bytes : List U8) (method : Method) (want_body : String) (want_rest : String) : Bool :=
  if Bool.not (String.from_list (Strings.drop_bytes n bytes) == want_rest)
  then false
  else
    match Wire.parse_response_with_method (Wire.take_bytes n bytes) method {
      Result.err _ => false,
      Result.ok res => w_body_is res.body want_body
    }

/// Frame the first response in `bytes` and check its body and its leftover.
def w_res_frames_to (bytes : List U8) (method : Method) (want_body : String) (want_rest : String) : Bool :=
  match Wire.frame_response bytes method {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n => w_res_framed_ok n bytes method want_body want_rest
      }
  }

def w_res_frame_incomplete (bytes : List U8) (method : Method) : Bool :=
  match Wire.frame_response bytes method {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => true,
        Option.some _ => false
      }
  }

def w_res_frame_bad (bytes : List U8) (method : Method) : Bool :=
  match Wire.frame_response bytes method {
    Result.err _ => true,
    Result.ok _ => false
  }

def w_res_body_is (bytes : List U8) (method : Method) (want : String) : Bool :=
  match Wire.parse_response_with_method bytes method {
    Result.err _ => false,
    Result.ok res => w_body_is res.body want
  }

def w_res_parse_fails (bytes : List U8) : Bool :=
  match Wire.parse_response bytes {
    Result.err _ => true,
    Result.ok _ => false
  }

// ── Content-Length ─────────────────────────────────────────────────────

def w_cl (v : String) : Headers :=
  Headers.set "Content-Length" v Headers.empty

/// Two `Content-Length` headers, the second added after the first.
def w_cl_two (a : String) (b : String) : Headers :=
  Headers.add "Content-Length" b (w_cl a)

def w_cl_is (h : Headers) (want : I64) : Bool :=
  match Wire.parse_content_length h {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n => I64.beq n want
      }
  }

def w_cl_absent (h : Headers) : Bool :=
  match Wire.parse_content_length h {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => true,
        Option.some _ => false
      }
  }

def w_cl_fails (h : Headers) : Bool :=
  match Wire.parse_content_length h {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_content_length_absent : Bool :=
  Bool.and (w_cl_absent Headers.empty) (w_cl_absent (Headers.set "Host" "a.com" Headers.empty))

#[test]
def test_content_length_present : Bool :=
  w_cl_is (w_cl "5") 5

#[test]
def test_content_length_zero : Bool :=
  w_cl_is (w_cl "0") 0

/// Header values arrive with surrounding whitespace.
#[test]
def test_content_length_trims : Bool :=
  w_cl_is (w_cl " 5 ") 5

/// The same declaration twice is one declaration.
#[test]
def test_content_length_duplicate_agreeing : Bool :=
  w_cl_is (w_cl_two "5" "5") 5

/// Two different numbers are a request-smuggling shape: one hop honours the
/// first and the next honours the second, so this must not resolve to either.
#[test]
def test_content_length_duplicate_conflicting : Bool :=
  w_cl_fails (w_cl_two "5" "6")

#[test]
def test_content_length_non_numeric : Bool :=
  w_cl_fails (w_cl "5a")

#[test]
def test_content_length_negative : Bool :=
  w_cl_fails (w_cl "-5")

/// A value past `I64.max` must not wrap to a small length.
#[test]
def test_content_length_overflow : Bool :=
  w_cl_fails (w_cl "99999999999999999999999999")

/// `parse_content_length` is the length question alone: any
/// `Transfer-Encoding` is a rejection there even now that the response
/// path decodes chunked, and a request declaring one is still refused.
#[test]
def test_content_length_with_transfer_encoding : Bool :=
  Bool.and
    (w_cl_fails (Headers.set "Transfer-Encoding" "chunked" (w_cl "5")))
    (w_cl_fails (Headers.set "Transfer-Encoding" "chunked" Headers.empty))

// ── chunked ─────────────────────────────────────────────────────────────
//
// `Transfer-Encoding: chunked` on a RESPONSE is decoded (RFC 9110 §7.1) --
// the shape Ollama and friends switch to once an answer outgrows a buffer.
// On a request it stays the rejection it always was.

/// True when the size line parses to `want`.
def w_size_is (line : String) (want : I64) : Bool :=
  match Wire.parse_chunk_size (String.to_list line) {
    Result.err _ => false,
    Result.ok n => n == want
  }

/// True when the size line is rejected.
def w_size_bad (line : String) : Bool :=
  match Wire.parse_chunk_size (String.to_list line) {
    Result.err _ => true,
    Result.ok _ => false
  }

/// A chunked response head with the body bytes appended raw.
def w_chunked_res (body : String) : List U8 :=
  String.to_list (String.concat "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n" body)

#[test]
def test_chunk_size_decimal_digits : Bool :=
  w_size_is "5" 5

/// Hex, not decimal -- `10` is sixteen bytes, not ten.
#[test]
def test_chunk_size_is_hex : Bool :=
  Bool.and (w_size_is "a" 10) (w_size_is "A" 10)

/// Chunk extensions follow a `;` and are tolerated, not parsed.
#[test]
def test_chunk_size_stops_at_extension : Bool :=
  w_size_is "5;name=value" 5

/// A size is what the whole frame hangs off: no hex digits is an error,
/// not a zero-size chunk.
#[test]
def test_chunk_size_empty_is_error : Bool :=
  Bool.and (w_size_bad "") (w_size_bad ";ext=1")

#[test]
def test_chunk_size_non_hex_is_error : Bool :=
  w_size_bad "zz"

/// A size past `I64.max` must not wrap to a small one.
#[test]
def test_chunk_size_overflow_is_error : Bool :=
  w_size_bad "FFFFFFFFFFFFFFFFF"

/// One chunk, terminal chunk, done: the frame ends where the terminal
/// chunk's CRLF does, and the body is the decoded data.
#[test]
def test_frame_response_chunked_single : Bool :=
  w_res_frames_to (w_chunked_res "5\r\nhello\r\n0\r\n\r\n") Method.GET "hello" ""

/// Several chunks concatenate in order.
#[test]
def test_frame_response_chunked_multi : Bool :=
  w_res_frames_to (w_chunked_res "3\r\nabc\r\n2\r\nde\r\n0\r\n\r\n") Method.GET "abcde" ""

/// Uppercase hex sizes are legal on the wire.
#[test]
def test_frame_response_chunked_uppercase : Bool :=
  w_res_frames_to (w_chunked_res "A\r\n0123456789\r\n0\r\n\r\n") Method.GET "0123456789" ""

/// Trailer lines after the terminal chunk are consumed, not parsed, and
/// cost the frame nothing.
#[test]
def test_frame_response_chunked_trailers : Bool :=
  w_res_frames_to (w_chunked_res "3\r\nabc\r\n0\r\nX-Checksum: 1\r\n\r\n") Method.GET "abc" ""

/// The body is still arriving: a size line without its CRLF yet.
#[test]
def test_frame_response_chunked_size_line_split : Bool :=
  w_res_frame_incomplete (w_chunked_res "2") Method.GET

/// The size line is complete but the data is not all here.
#[test]
def test_frame_response_chunked_data_pending : Bool :=
  w_res_frame_incomplete (w_chunked_res "5\r\nhel") Method.GET

/// The terminal chunk arrived but the trailer section has not.
#[test]
def test_frame_response_chunked_terminal_pending : Bool :=
  w_res_frame_incomplete (w_chunked_res "5\r\nhello\r\n0\r\n") Method.GET

/// EOF before the terminal chunk is a truncation, not a short body.
#[test]
def test_parse_chunked_short_body_fails : Bool :=
  w_res_parse_fails (w_chunked_res "5\r\nhel")

/// A size line that is not hex is reported, not guessed around.
#[test]
def test_parse_chunked_bad_size_fails : Bool :=
  w_res_parse_fails (w_chunked_res "zz\r\nhello\r\n0\r\n\r\n")

/// A transfer coding other than chunked is still refused: the chunks
/// would decode to bytes still encoded.
#[test]
def test_frame_response_te_other_is_error : Bool :=
  w_res_frame_bad (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\nx") Method.GET

/// Stacked codings are refused for the same reason -- `chunked` must be
/// the only one for the decoded bytes to be the body.
#[test]
def test_frame_response_te_stacked_is_error : Bool :=
  w_res_frame_bad (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\nx") Method.GET

/// Transfer coding names are case-insensitive (RFC 9112 §7): a server
/// that spells it `Chunked` is declaring the one coding this library
/// decodes, not an unsupported one.
#[test]
def test_frame_response_te_case_insensitive : Bool :=
  w_res_frames_to
    (String.to_list (String.concat "HTTP/1.1 200 OK\r\nTransfer-Encoding: Chunked\r\n\r\n" "5\r\nhello\r\n0\r\n\r\n"))
    Method.GET "hello" ""

// ── request framing ────────────────────────────────────────────────────

#[test]
def test_frame_request_no_body : Bool :=
  w_frames_to (String.to_list "GET / HTTP/1.1\r\n\r\n") "" ""

/// A request header block that has not finished arriving yet.
#[test]
def test_frame_request_incomplete_headers : Bool :=
  w_frame_incomplete (String.to_list "GET / HTTP/1.1\r\nHost: a")

/// The headers are complete but the body is not all here. A single socket read
/// hits this routinely, so it is "not yet", not an error.
#[test]
def test_frame_request_incomplete_body : Bool :=
  w_frame_incomplete (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nab")

#[test]
def test_frame_request_complete_body : Bool :=
  w_frames_to (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello") "hello" ""

/// The body is exactly `Content-Length` bytes: the request after it is left
/// over whole rather than being swallowed as body.
#[test]
def test_frame_request_keeps_pipelined_remainder : Bool :=
  w_frames_to
    (String.to_list "POST /a HTTP/1.1\r\nContent-Length: 5\r\n\r\nhelloGET /b HTTP/1.1\r\n\r\n")
    "hello" "GET /b HTTP/1.1\r\n\r\n"

/// The read that delivered the body also delivered the start of the next
/// request -- and the body is still only `Content-Length` bytes. Before the
/// boundary existed the whole chunk was appended to the body, so the second
/// request was lost.
#[test]
def test_frame_request_body_overrun_keeps_remainder : Bool :=
  w_frames_to
    (String.to_list "POST /a HTTP/1.1\r\nContent-Length: 3\r\n\r\nhelloGET /b HTTP/1.1\r\n\r\n")
    "hel" "loGET /b HTTP/1.1\r\n\r\n"

/// A request with no `Content-Length` has no body (RFC 9110 §8.6), so trailing
/// bytes are the next message rather than a body nobody declared.
#[test]
def test_frame_request_absent_length_is_no_body : Bool :=
  w_frames_to (String.to_list "POST / HTTP/1.1\r\n\r\nEXTRA") "" "EXTRA"

#[test]
def test_frame_request_conflicting_length_is_error : Bool :=
  w_frame_bad (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello")

#[test]
def test_frame_request_unsupported_transfer_encoding_is_error : Bool :=
  w_frame_bad (String.to_list "POST / HTTP/1.1\r\nTransfer-Encoding: gzip\r\n\r\n")

// ── parse strictness ───────────────────────────────────────────────────

/// A body shorter than its `Content-Length` is a truncation, not a short body.
#[test]
def test_parse_request_short_body_fails : Bool :=
  w_parse_fails (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nab")

#[test]
def test_parse_response_short_body_fails : Bool :=
  w_res_parse_fails (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nab")

/// Parsing a request out of a buffer that holds two gives the first one's body,
/// not everything that followed.
#[test]
def test_parse_request_body_is_content_length : Bool :=
  w_parsed_body_is
    (String.to_list "POST /a HTTP/1.1\r\nContent-Length: 5\r\n\r\nhelloGET /b HTTP/1.1\r\n\r\n")
    "hello"

#[test]
def test_parse_request_zero_length_body : Bool :=
  w_parsed_body_is (String.to_list "POST / HTTP/1.1\r\nContent-Length: 0\r\n\r\n") ""

// ── response framing ───────────────────────────────────────────────────

/// Which responses may carry a body at all, and which carry a
/// `Content-Length` that describes a body they are not sending.
#[test]
def test_response_has_body_matrix : Bool :=
  Bool.and (Bool.not (Wire.response_has_body Method.HEAD Status.ok))
    (Bool.and (Bool.not (Wire.response_has_body Method.GET 100u16))
      (Bool.and (Bool.not (Wire.response_has_body Method.GET Status.no_content))
        (Bool.and (Bool.not (Wire.response_has_body Method.GET Status.not_modified))
          (Bool.and (Wire.response_has_body Method.GET Status.ok)
            (Wire.response_has_body Method.GET Status.not_found)))))

#[test]
def test_frame_response_content_length : Bool :=
  w_res_frames_to
    (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello") Method.GET "hello" ""

#[test]
def test_frame_response_keeps_remainder : Bool :=
  w_res_frames_to
    (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhelloHTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n")
    Method.GET "hello" "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"

/// The review's hang: a HEAD response declares the `Content-Length` of the
/// body it is not sending, so honouring that length leaves a client waiting for
/// five bytes that never arrive. No body, and the message ends at the head.
#[test]
def test_frame_response_head_has_no_body : Bool :=
  w_res_frames_to (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n") Method.HEAD "" ""

#[test]
def test_frame_response_204_has_no_body : Bool :=
  w_res_frames_to (String.to_list "HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n") Method.GET "" ""

#[test]
def test_frame_response_304_has_no_body : Bool :=
  w_res_frames_to (String.to_list "HTTP/1.1 304 Not Modified\r\nContent-Length: 5\r\n\r\n") Method.GET "" ""

#[test]
def test_frame_response_1xx_has_no_body : Bool :=
  w_res_frames_to (String.to_list "HTTP/1.1 100 Continue\r\n\r\n") Method.GET "" ""

/// No `Content-Length` on a response means read-to-close, so the body is
/// everything buffered and the message ends where the buffer does.
#[test]
def test_frame_response_until_eof : Bool :=
  w_res_frames_to (String.to_list "HTTP/1.1 200 OK\r\n\r\nhello") Method.GET "hello" ""

#[test]
def test_frame_response_incomplete_body : Bool :=
  w_res_frame_incomplete (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nab") Method.GET

#[test]
def test_frame_response_conflicting_length_is_error : Bool :=
  w_res_frame_bad (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello") Method.GET

/// The method reaches the body decision: the same bytes are a body for a `GET`
/// and no body at all for a `HEAD`.
#[test]
def test_parse_response_method_decides_body : Bool :=
  Bool.and
    (w_res_body_is (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello") Method.GET "hello")
    (w_res_body_is (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n") Method.HEAD "")

// ── streaming bodies ───────────────────────────────────────────────────
//
// A `Body.stream` has no pure byte form, and treating it as one produced
// `Content-Length: 0` with an empty body -- byte-for-byte what an empty body
// serialises to, so the peer read a complete response that had dropped
// everything it was promised. It is an error instead, at the length and at the
// bytes, and the parser never builds one.

/// The read function of a test stream. The serialiser refuses a stream before
/// reading it, so this is never called.
def w_no_chunk : Unit -> IO (Option (List U8)) :=
  fn (_ : Unit) => do { return Option.none }

def w_stream_body : Body :=
  Body.stream w_no_chunk

def w_res_of_body (b : Body) : Response :=
  { status := Status.ok, headers := Headers.empty, version := HttpVersion.http1_1, body := b }

def w_is_stream (b : Body) : Bool :=
  match b {
    Body.stream _ => true,
    Body.empty => false,
    Body.bytes _ => false,
    Body.text _ => false,
    Body.form _ => false
  }

#[test]
def test_content_length_of_stream_fails : Bool :=
  match Wire.content_length_of w_stream_body {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_body_bytes_of_stream_fails : Bool :=
  match Wire.body_bytes w_stream_body {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_format_stream_body_request_fails : Bool :=
  let u : Uri := Uri.uri "" Option.none "" Option.none "/upload" Option.none Option.none in
  let req : Request := { method := Method.POST, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := w_stream_body } in
  w_req_fails req

#[test]
def test_format_stream_body_response_fails : Bool :=
  w_res_fails (w_res_of_body w_stream_body)

/// The pure projections answer with no bytes and length zero rather than
/// failing: they are for callers looking at a body they know is not a stream.
#[test]
def test_stream_body_pure_projections_are_empty : Bool :=
  Bool.and
    (List.is_empty (Body.to_bytes_pure w_stream_body))
    (I64.beq (Body.length w_stream_body) 0)

/// Nothing the parser builds is a stream -- a parsed message is always
/// something its holder can serialise straight back out.
#[test]
def test_parse_never_produces_stream : Bool :=
  match Wire.parse_request (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello") {
    Result.err _ => false,
    Result.ok req => Bool.not (w_is_stream req.body)
  }

#[test]
def test_parse_response_never_produces_stream : Bool :=
  match Wire.parse_response (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello") {
    Result.err _ => false,
    Result.ok res => Bool.not (w_is_stream res.body)
  }

// ── incremental chunked decoding ─────────────────────────────────────────
//
// `chunk_step` is the streaming half of the chunked decoder: pending +
// incoming in, done/decoded/pending' out. The pinned triple is the whole
// contract -- a streaming client reassembles exactly these answers.

/// One `chunk_step` call, pinned: the done flag, the decoded bytes, and the
/// leftover pending.
def cs_ok (pending : String) (incoming : String) (want_done : Bool) (want_decoded : String) (want_pending : String) : Bool :=
  match Wire.chunk_step (String.to_list pending) (String.to_list incoming) {
    Result.err _ => false,
    Result.ok pr =>
      match pr {
        Pair.pair step pending2 =>
          match step {
            Pair.pair done decoded =>
              Bool.and (if want_done then done else Bool.not done)
                (Bool.and (String.from_list decoded == want_decoded)
                  (String.from_list pending2 == want_pending))
          }
      }
  }

/// A fully-buffered chunk decodes, and the walk keeps waiting (not done).
#[test]
def test_chunk_step_decodes_complete_chunk : Bool :=
  cs_ok "" "5\r\nhello\r\n" false "hello" ""

/// A chunk split across steps: the first half stays pending, the second
/// completes it -- the size line is never re-read from a lost buffer.
#[test]
def test_chunk_step_split_across_steps : Bool :=
  Bool.and
    (cs_ok "" "5\r\nhel" false "" "5\r\nhel")
    (cs_ok "5\r\nhel" "lo\r\n" false "hello" "")

/// The terminal chunk sets done, and its trailer section is neither waited
/// for nor carried.
#[test]
def test_chunk_step_terminal_chunk : Bool :=
  cs_ok "" "0\r\n\r\n" true "" ""

/// Data and the terminal chunk in one step: the decoded bytes ride along
/// with done rather than being lost behind it.
#[test]
def test_chunk_step_data_then_terminal : Bool :=
  cs_ok "" "5\r\nhello\r\n0\r\n\r\n" true "hello" ""

/// Two chunks in one step, decoded in order.
#[test]
def test_chunk_step_two_chunks : Bool :=
  cs_ok "" "3\r\nabc\r\n3\r\ndef\r\n" false "abcdef" ""

/// Nothing in, nothing out: not done, nothing decoded, nothing pending.
#[test]
def test_chunk_step_empty : Bool :=
  cs_ok "" "" false "" ""

/// A size line that is not hex is reported, not guessed around.
#[test]
def test_chunk_step_bad_size_is_error : Bool :=
  match Wire.chunk_step List.empty (String.to_list "zz\r\nhello") {
    Result.err _ => true,
    Result.ok _ => false
  }

// ── chunked requests ──

#[test]
def test_request_framing_chunked : Bool :=
  let hs := Headers.set "Transfer-Encoding" "chunked" Headers.empty in
  match Wire.request_framing hs {
    Result.err _ => false,
    Result.ok framing =>
      match framing {
        Framing.chunked => true,
        _ => false
      }
  }

#[test]
def test_request_framing_chunked_with_length_rejected : Bool :=
  let hs := Headers.set "Content-Length" "4"
    (Headers.set "Transfer-Encoding" "chunked" Headers.empty) in
  match Wire.request_framing hs {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_frame_and_parse_chunked_request : Bool :=
  let bytes := String.to_list
    "POST /x HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nabcd\r\n0\r\n\r\n" in
  match Wire.frame_request bytes {
    Result.err _ => false,
    Result.ok opt =>
      match opt {
        Option.none => false,
        Option.some n =>
          match Wire.parse_request (Wire.take_bytes n bytes) {
            Result.err _ => false,
            Result.ok req =>
              match req.body {
                Body.bytes data => String.beq (String.from_list data) "abcd",
                Body.empty => false,
                Body.text _ => false,
                Body.stream _ => false,
                Body.form _ => false
              }
          }
      }
  }

// ── header validation and bodyless head framing ────────────────────────

#[test]
def test_format_response_rejects_header_injection : Bool :=
  let res := Response.with_header "X-Test" "ok\r\nSet-Cookie: a=b" (Response.text 200u16 "hi") in
  match Wire.format_response res {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_format_response_accepts_normal_header : Bool :=
  let res := Response.with_header "X-Test" "ok" (Response.text 200u16 "hi") in
  match Wire.format_response res {
    Result.ok _ => true,
    Result.err _ => false
  }

#[test]
def test_head_204_has_no_content_length : Bool :=
  match Wire.format_response_head Response.no_content {
    Result.err _ => false,
    Result.ok bytes => String.beq (String.from_list bytes) "HTTP/1.1 204 \r\n\r\n"
  }

#[test]
def test_head_304_omits_computed_length : Bool :=
  let res := Response.with_status 304u16 (Response.text 200u16 "") in
  match Wire.format_response_head res {
    Result.err _ => false,
    Result.ok bytes => String.beq (String.from_list bytes) "HTTP/1.1 304 \r\n\r\n"
  }

#[test]
def test_head_200_keeps_representation_length : Bool :=
  match Wire.format_response_head (Response.text 200u16 "hello") {
    Result.err _ => false,
    Result.ok bytes =>
      String.beq (String.from_list bytes)
        "HTTP/1.1 200 \r\ncontent-length: 5\r\n\r\n"
  }
