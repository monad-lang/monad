/// HTTP/1.1 wire format — Layer 0, pure Monad.
///
/// Pure parse/serialize of the on-the-wire HTTP/1.1 format, operating on
/// `List U8` and `Request`/`Response` from `types.mo`. No IO. Shared by
/// `moose` (format request / parse response) and `moon` (parse request /
/// format response).
///
/// Also owns framing (`Wire.frame_request` / `Wire.frame_response`): how many
/// bytes of a buffer belong to the first message. Parsing a message and
/// framing one are separate questions -- a buffer may hold a message and a
/// half, or two -- and only the caller knows which it is asking.

use http::strings {
  Strings.drop_bytes, Strings.hex_value, Strings.i64_of_nibble, Strings.parse_i64,
  Strings.parse_u16_bounded, Strings.split_at_byte,
  Strings.split_at_byte_opt,
}
use lib::types {Body, Framing, Headers, HttpVersion, Method, Request, Response, Uri}
use http::uri {Uri.format, Uri.format_query, Uri.parse}
use std::list {List.length}

// ── byte list builders ──────────────────────────────────────────────────

def Wire.crlf : List U8 :=
  String.to_list "\r\n"

def Wire.byte (b : U8) : List U8 :=
  List.singleton b

def Wire.str_bytes (s : String) : List U8 :=
  String.to_list s

def Wire.append_all (xs : List (List U8)) : List U8 :=
  match xs {
    List.empty => List.empty,
    List.cons h t => List.append h (Wire.append_all t)
  }

// ── helpers for method / status / version strings ───────────────────────

pub def Wire.method_str (m : Method) : String :=
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

def Wire.version_str (v : HttpVersion) : String :=
  match v {
    HttpVersion.http1_0 => "HTTP/1.0",
    HttpVersion.http1_1 => "HTTP/1.1"
  }

def Wire.parse_version (s : String) : Result String HttpVersion :=
  if String.beq s "HTTP/1.0"
  then Result.ok HttpVersion.http1_0
  else if String.beq s "HTTP/1.1"
  then Result.ok HttpVersion.http1_1
  else Result.err "unsupported HTTP version"

def Wire.parse_method (s : String) : Result String Method :=
  if String.beq s "GET" then Result.ok Method.GET
  else if String.beq s "HEAD" then Result.ok Method.HEAD
  else if String.beq s "POST" then Result.ok Method.POST
  else if String.beq s "PUT" then Result.ok Method.PUT
  else if String.beq s "DELETE" then Result.ok Method.DELETE
  else if String.beq s "CONNECT" then Result.ok Method.CONNECT
  else if String.beq s "OPTIONS" then Result.ok Method.OPTIONS
  else if String.beq s "TRACE" then Result.ok Method.TRACE
  else if String.beq s "PATCH" then Result.ok Method.PATCH
  else Result.err "unknown method"

// ── header line building ───────────────────────────────────────────────

def Wire.header_lines (h : Headers) : List U8 :=
  match h {
    Headers.headers pairs => Wire.header_lines_go pairs
  }

def Wire.header_lines_go (pairs : List (Pair String String)) : List U8 :=
  match pairs {
    List.empty => List.empty,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          let line := Wire.append_all (List.cons (Wire.str_bytes k) (List.cons (Wire.byte 58u8) (List.cons (Wire.byte 32u8) (List.singleton (Wire.str_bytes v))))) in
          List.append line (List.append Wire.crlf (Wire.header_lines_go rest))
      }
  }

// ── chunked response framing ────────────────────────────────────────────
//
// A stream has no length, so a response that carries one is framed with
// `Transfer-Encoding: chunked`: `<hex size> CRLF <bytes> CRLF` per chunk,
// then a zero-size terminal chunk. These helpers are pure; `Body.write_chunked`
// drives a body through them.

def Wire.hex_chars : List String :=
  ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"]

#[terminating]
def Wire.nth_string (n : I64) (xs : List String) : String :=
  match xs {
    List.empty => "0",
    List.cons x rest => if I64.lt n 1 then x else Wire.nth_string (I64.sub n 1) rest
  }

#[terminating]
def Wire.hex_digits (n : I64) : List String :=
  if I64.lt n 1
  then List.empty
  else
    let q := I64.div n 16i64 in
    let r := I64.sub n (I64.mul q 16i64) in
    List.append (Wire.hex_digits q)
      (List.cons (Wire.nth_string r Wire.hex_chars) List.empty)

pub def Wire.hex_i64 (n : I64) : String :=
  if I64.lt n 1 then "0" else String.concat_list (Wire.hex_digits n)

/// One chunk: `<hex length> CRLF <bytes> CRLF`.
pub def Wire.chunk_frame (bytes : List U8) : List U8 :=
  let size := String.to_list (Wire.hex_i64 (List.length bytes)) in
  List.append (List.append (List.append size Wire.crlf) bytes) Wire.crlf

pub def Wire.terminal_chunk : List U8 :=
  String.to_list "0\r\n\r\n"

/// A response head for a chunked body: status line + headers with
/// `Transfer-Encoding: chunked` and no `Content-Length`.
pub def Wire.response_head_chunked (res : Response) : List U8 :=
  let status_line := Wire.status_line res.status res.version in
  let hs := Headers.remove "Content-Length"
    (Headers.set "Transfer-Encoding" "chunked" res.headers) in
  let hdrs := Wire.header_lines hs in
  List.append (List.append status_line hdrs) Wire.crlf

// ── body to bytes ──────────────────────────────────────────────────────
//
// Serialising a `Body.stream` fails rather than rendering as zero bytes. There
// is no pure byte form of a stream, and producing an empty one would be
// indistinguishable from a real empty body: the peer would get a
// `Content-Length: 0` message and no way to tell that bytes it was promised
// were never sent. The type stays constructible -- a caller may build one and
// hand it to an IO-aware path -- but every pure serialiser says so.

/// The error a body that cannot be serialised produces.
def Wire.stream_unsupported : String :=
  "streaming bodies are not supported"

def Wire.body_bytes (b : Body) : Result String (List U8) :=
  match b {
    Body.empty => Result.ok List.empty,
    Body.bytes data => Result.ok data,
    Body.text s => Result.ok (String.to_list s),
    Body.stream _ => Result.err Wire.stream_unsupported,
    Body.form fields => Result.ok (String.to_list (Uri.format_query fields))
  }

def Wire.content_length_of (b : Body) : Result String I64 :=
  match b {
    Body.empty => Result.ok 0,
    Body.bytes data => Result.ok (List.length data),
    Body.text s => Result.ok (String.length s),
    Body.stream _ => Result.err Wire.stream_unsupported,
    Body.form fields => Result.ok (String.length (Uri.format_query fields))
  }

// ── format request ─────────────────────────────────────────────────────
//
// Both formatters answer `Result`: the length and the bytes of a body are
// computed separately, so a body that cannot be serialised has to be caught at
// both -- and it is the caller that decides what to do about it (the server
// answers 500, the client returns the error).

pub def Wire.format_request (req : Request) : Result String (List U8) :=
  match Wire.content_length_of req.body {
    Result.err e => Result.err e,
    Result.ok len => Wire.format_request_at req len
  }

/// Format a request whose body length is already known.
def Wire.format_request_at (req : Request) (len : I64) : Result String (List U8) :=
  match Wire.body_bytes req.body {
    Result.err e => Result.err e,
    Result.ok body => Result.ok (Wire.render_request req len body)
  }

/// The request head followed by an already-serialised body.
def Wire.render_request (req : Request) (len : I64) (body : List U8) : List U8 :=
  let req_line := Wire.request_line req.method req.uri req.version in
  let hs := Wire.add_content_length req.headers len in
  let hdrs := Wire.header_lines hs in
  List.append (List.append req_line hdrs) (List.append Wire.crlf body)

def Wire.request_line (m : Method) (u : Uri) (v : HttpVersion) : List U8 :=
  let path := Wire.request_target u in
  let line := Wire.append_all (List.cons (Wire.str_bytes (Wire.method_str m)) (List.cons (Wire.byte 32u8) (List.cons (Wire.str_bytes path) (List.cons (Wire.byte 32u8) (List.singleton (Wire.str_bytes (Wire.version_str v))))))) in
  List.append line Wire.crlf

def Wire.request_target (u : Uri) : String :=
  if String.is_empty u.scheme
  then
    let q := match u.query {
      Option.none => "",
      Option.some qstr => String.concat "?" qstr
    } in
    String.concat u.path q
  else Uri.format u

def Wire.add_content_length (h : Headers) (len : I64) : Headers :=
  Headers.set "Content-Length" (I64.to_string len) h

// ── format response ─────────────────────────────────────────────────────

pub def Wire.format_response (res : Response) : Result String (List U8) :=
  match Wire.content_length_of res.body {
    Result.err e => Result.err e,
    Result.ok len => Wire.format_response_at res len
  }

/// Serialise only the response head, keeping the representation's
/// `Content-Length` but writing no body. This is what a `HEAD`, 204 or 304
/// answer needs: the peer is told how large the body would be, and the
/// connection stays framed.
pub def Wire.format_response_head (res : Response) : Result String (List U8) :=
  match Wire.content_length_of res.body {
    Result.err e => Result.err e,
    Result.ok len =>
      let status_line := Wire.status_line res.status res.version in
      let hs := Wire.add_content_length res.headers len in
      let hdrs := Wire.header_lines hs in
      Result.ok (List.append (List.append status_line hdrs) Wire.crlf)
  }

/// Format a response whose body length is already known.
def Wire.format_response_at (res : Response) (len : I64) : Result String (List U8) :=
  match Wire.body_bytes res.body {
    Result.err e => Result.err e,
    Result.ok body => Result.ok (Wire.render_response res len body)
  }

/// The response head followed by an already-serialised body.
def Wire.render_response (res : Response) (len : I64) (body : List U8) : List U8 :=
  let status_line := Wire.status_line res.status res.version in
  let hs := Wire.add_content_length res.headers len in
  let hdrs := Wire.header_lines hs in
  List.append (List.append status_line hdrs) (List.append Wire.crlf body)

def Wire.status_line (status : U16) (v : HttpVersion) : List U8 :=
  let line := Wire.append_all (List.cons (Wire.str_bytes (Wire.version_str v)) (List.cons (Wire.byte 32u8) (List.cons (Wire.str_bytes (U16.to_string status)) (List.singleton (Wire.byte 32u8))))) in
  List.append line Wire.crlf

// ── parsing: line splitting on CRLF ────────────────────────────────────

def Wire.split_lines (bytes : List U8) : List (List U8) :=
  Wire.split_lines_go bytes List.empty

#[terminating]
def Wire.split_lines_go (bytes : List U8) (acc : List U8) : List (List U8) :=
  match bytes {
    List.empty => List.singleton (List.reverse acc),
    List.cons x rest =>
      if U8.beq x 13u8
      then
        match rest {
          List.empty => List.singleton (List.reverse acc),
          List.cons y rest2 =>
            if U8.beq y 10u8
            then List.cons (List.reverse acc) (Wire.split_lines_go rest2 List.empty)
            else Wire.split_lines_go rest (List.cons x acc)
        }
      else Wire.split_lines_go rest (List.cons x acc)
  }

/// Find the blank line (CRLFCRLF) that separates headers from body. Returns
/// the byte offset of the body start, or none if not found.
pub def Wire.find_body_start (bytes : List U8) : Option I64 :=
  Wire.find_body_start_go bytes 0i64

#[terminating]
def Wire.find_body_start_go (bytes : List U8) (idx : I64) : Option I64 :=
  match bytes {
    List.empty => Option.none,
    List.cons x rest =>
      if U8.beq x 13u8
      then
        match rest {
          List.empty => Option.none,
          List.cons y rest2 =>
            if U8.beq y 10u8
            then
              match rest2 {
                List.empty => Option.none,
                List.cons z rest3 =>
                  if U8.beq z 13u8
                  then
                    match rest3 {
                      List.empty => Option.none,
                      List.cons w rest4 =>
                        if U8.beq w 10u8
                        then Option.some (I64.add idx 4i64)
                        else Wire.find_body_start_go rest3 (I64.add idx 3i64)
                    }
                  else Wire.find_body_start_go rest2 (I64.add idx 2i64)
              }
            else Wire.find_body_start_go rest (I64.add idx 1i64)
        }
      else Wire.find_body_start_go rest (I64.add idx 1i64)
  }

pub def Wire.take_bytes (n : I64) (bytes : List U8) : List U8 :=
  if I64.beq n 0
  then List.empty
  else
    match bytes {
      List.empty => List.empty,
      List.cons x rest => List.cons x (Wire.take_bytes (I64.sub n 1i64) rest)
    }

// ── parse header lines into Headers ───────────────────────────────────

def Wire.parse_header_lines (lines : List (List U8)) : Result String Headers :=
  Wire.parse_header_lines_go lines Headers.empty

def Wire.parse_header_lines_go (lines : List (List U8)) (acc : Headers) : Result String Headers :=
  match lines {
    List.empty => Result.ok acc,
    List.cons line rest =>
      if List.is_empty line
      then Result.ok acc
      else
        match Wire.parse_one_header line {
          Result.err e => Result.err e,
          Result.ok kv => Wire.parse_header_lines_go rest (Headers.add kv.first kv.second acc)
        }
  }

/// Split one header line at its colon. A line with no colon is an error.
///
/// `Body.parse_part_header_lines_go` also calls this, and *skips* the error
/// rather than propagating it: one malformed line inside a multipart section
/// should not cost the caller the whole body. The difference is deliberate and
/// lives at that call site; this function only reports what it saw.
def Wire.parse_one_header (line : List U8) : Result String (Pair String String) :=
  match Strings.split_at_byte_opt 58u8 line {
    Option.none => Result.err "header line without colon",
    Option.some sp =>
      let k := String.from_list sp.first in
      let v := String.trim (String.from_list (Wire.drop_leading_space sp.second)) in
      Result.ok (Pair.pair k v)
  }

def Wire.drop_leading_space (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons x rest =>
      if U8.beq x 32u8
      then Wire.drop_leading_space rest
      else bytes
  }

// ── message framing ────────────────────────────────────────────────────
//
// Framing is what makes the end of a body predictable. The parser used to
// define a body as "every byte after the header block", which is right for a
// single message on a fresh connection and wrong the moment two messages
// share one read: the first request's body swallowed the second's request
// line. The boundary is now `Content-Length`, and the bytes it does not cover
// are reported so a pipelined request can be served out of them.

/// The body length a `Content-Length` declares, or `Option.none` when the head
/// declares none.
///
/// Errors rather than guesses when the head is ambiguous. This is the
/// LENGTH question alone, so any `Transfer-Encoding` is still a rejection
/// here -- the response path decodes chunked itself (`Wire.response_framing`),
/// and a request declaring one is a request this library will not frame.
/// Two `Content-Length` values that disagree are the classic
/// request-smuggling shape, where one hop honours the first value and the next
/// honours the second. A value that is not a plain non-negative number is an
/// error too, including one that overflows, so an absurd length cannot arrive
/// as a small positive one.
def Wire.parse_content_length (headers : Headers) : Result String (Option I64) :=
  if Bool.not (List.is_empty (Headers.get_all "transfer-encoding" headers))
  then Result.err "Transfer-Encoding is not supported"
  else
    match Headers.get_all "content-length" headers {
      List.empty => Result.ok Option.none,
      List.cons first rest =>
        if Wire.content_lengths_agree first rest
        then
          match Strings.parse_i64 first {
            Option.none => Result.err "invalid Content-Length",
            Option.some n => Result.ok (Option.some n)
          }
        else Result.err "conflicting Content-Length values"
    }

/// True when every later value repeats the first. The same declaration written
/// twice is legal; two different numbers are not.
def Wire.content_lengths_agree (first : String) (rest : List String) : Bool :=
  match rest {
    List.empty => true,
    List.cons v vs =>
      Bool.and (String.beq (String.trim v) (String.trim first)) (Wire.content_lengths_agree first vs)
  }

/// The framing a request's head declares. A request with no `Content-Length`
/// has no body (RFC 9110 §8.6), which is not the response rule: there an
/// absent length means read-to-close.
def Wire.request_framing (headers : Headers) : Result String Framing :=
  match Headers.get_all "transfer-encoding" headers {
    List.empty =>
      match Wire.parse_content_length headers {
        Result.err e => Result.err e,
        Result.ok opt =>
          match opt {
            Option.none => Result.ok Framing.no_body,
            Option.some n => Result.ok (Framing.content_length n)
          }
      },
    List.cons _ _ => Wire.chunked_request_framing headers
  }

/// A request declaring exactly `Transfer-Encoding: chunked`. A request that
/// also carries `Content-Length` is rejected: that is the request-smuggling
/// shape, where two hops disagree about where the body ends.
pub def Wire.chunked_request_framing (headers : Headers) : Result String Framing :=
  match Wire.chunked_declared headers {
    Option.none => Result.err "no chunked transfer coding",
    Option.some declared =>
      if declared
      then
        if List.is_empty (Headers.get_all "content-length" headers)
        then Result.ok Framing.chunked
        else Result.err "both Content-Length and Transfer-Encoding"
      else Result.err "unsupported transfer coding"
  }

// ── chunked decoding ───────────────────────────────────────────────────
//
// A `Transfer-Encoding: chunked` body is a sequence of `size CRLF data
// CRLF` chunks closed by a `0`-size chunk and a trailer section (RFC 9110
// §7.1). One walk serves both questions the framing section asks of it:
// how many bytes the body spans (`message_total`) and what the decoded
// bytes are (`body_at`) -- two answers from one parser is the whole point
// of sharing `decode_chunked`, since a frame and a body that disagree is
// a client handing its caller body bytes a length did not vouch for.

/// The offset of the first CRLF in `bytes`, or none when there is none.
#[terminating]
def Wire.find_crlf (bytes : List U8) (idx : I64) : Option I64 :=
  match bytes {
    List.empty => Option.none,
    List.cons x rest =>
      if x == 13u8
      then
        match rest {
          List.empty => Option.none,
          List.cons y _ =>
            if y == 10u8
            then Option.some idx
            else Wire.find_crlf rest (I64.add idx 1i64)
        }
      else Wire.find_crlf rest (I64.add idx 1i64)
  }

/// The chunk size in a size line: hex digits, stopping at `;` -- chunk
/// extensions are tolerated, not parsed. A size is what the whole frame
/// hangs off, so an empty size line and one that overflows `I64` are
/// errors rather than guesses (an absurd size wrapped to a small one is a
/// body boundary the server never sent).
def Wire.parse_chunk_size (line : List U8) : Result String I64 :=
  Wire.parse_chunk_size_go line 0i64 false

/// `seen` tells the empty case from a leading `;`: an extension with no
/// size in front of it is a malformed line, not a zero-size chunk.
#[terminating]
def Wire.parse_chunk_size_go (line : List U8) (acc : I64) (seen : Bool) : Result String I64 :=
  match line {
    List.empty =>
      if seen then Result.ok acc else Result.err "empty chunk size",
    List.cons b rest =>
      if b == 59u8
      then
        if seen then Result.ok acc else Result.err "empty chunk size"
      else
        match Strings.hex_value b {
          Option.none => Result.err "invalid chunk size",
          Option.some nib =>
            let d : I64 := Strings.i64_of_nibble nib in
            if Wire.chunk_size_overflows acc d
            then Result.err "chunk size overflows"
            else Wire.parse_chunk_size_go rest (I64.add (I64.mul acc 16i64) d) true
        }
  }

/// Would `acc * 16 + digit` exceed `I64.max`? The same pre-multiply
/// discipline as `Strings.i64_overflows`, base 16.
def Wire.chunk_size_overflows (acc : I64) (digit : I64) : Bool :=
  if I64.gt acc 576460752303423487i64
  then true
  else if acc == 576460752303423487i64
  then I64.gt digit 7i64
  else false

/// Walk a whole chunked body. `ok none` is "not all here yet", which a
/// single socket read hits routinely; `err` is a body that cannot be
/// decoded (a size line that is not hex, a data chunk not CRLF-terminated);
/// `ok some` carries the number of bytes the body spans and the decoded
/// data, trailers excluded.
pub def Wire.decode_chunked (bytes : List U8) : Result String (Option (Pair I64 (List U8))) :=
  Wire.decode_chunk_size_line bytes 0i64 List.empty

/// Read the next chunk's size line (up to its CRLF) and dispatch on the
/// size. `offset` counts bytes consumed so far; `acc` holds decoded data.
#[terminating]
def Wire.decode_chunk_size_line (bytes : List U8) (offset : I64) (acc : List U8) : Result String (Option (Pair I64 (List U8))) :=
  match Wire.find_crlf bytes 0i64 {
    Option.none => Result.ok Option.none,
    Option.some idx =>
      match Wire.parse_chunk_size (Wire.take_bytes idx bytes) {
        Result.err e => Result.err e,
        Result.ok size =>
          let consumed := I64.add offset (I64.add idx 2i64) in
          Wire.decode_chunk_dispatch size (Strings.drop_bytes (I64.add idx 2i64) bytes) consumed acc
      }
  }

/// A zero-size chunk is the terminator: what follows is a trailer section.
/// Anything else has `size` bytes of data waiting behind it.
#[terminating]
def Wire.decode_chunk_dispatch (size : I64) (rest : List U8) (offset : I64) (acc : List U8) : Result String (Option (Pair I64 (List U8))) :=
  if size == 0i64
  then Wire.decode_chunk_trailers rest offset acc
  else Wire.decode_chunk_data size rest offset acc

/// Consume `size` bytes of data plus the CRLF behind them, then continue
/// with the next chunk. Less than `size + 2` bytes buffered is "not here
/// yet", not an error -- the CRLF may still be in flight.
#[terminating]
def Wire.decode_chunk_data (size : I64) (rest : List U8) (offset : I64) (acc : List U8) : Result String (Option (Pair I64 (List U8))) :=
  if I64.gt size (I64.sub (List.length rest) 2i64)
  then Result.ok Option.none
  else
    let data := Wire.take_bytes size rest in
    let after := Strings.drop_bytes size rest in
    Wire.decode_chunk_data_crlf data after (I64.add offset size) acc

/// Check the CRLF that closes a chunk's data, then recurse into the next
/// size line.
#[terminating]
def Wire.decode_chunk_data_crlf (data : List U8) (after : List U8) (offset : I64) (acc : List U8) : Result String (Option (Pair I64 (List U8))) :=
  match after {
    List.empty => Result.ok Option.none,
    List.cons cr lf_rest =>
      if cr == 13u8
      then
        match lf_rest {
          List.empty => Result.ok Option.none,
          List.cons lf more =>
            if lf == 10u8
            then Wire.decode_chunk_size_line more (I64.add offset 2i64) (List.append acc data)
            else Result.err "chunk data not CRLF-terminated"
        }
      else Result.err "chunk data not CRLF-terminated"
  }

/// The trailer section after the terminal chunk: zero or more `field:
/// value CRLF` lines, closed by a bare CRLF. The trailer lines themselves
/// are consumed, not parsed -- this library keeps no fields a trailer
/// would carry.
#[terminating]
def Wire.decode_chunk_trailers (rest : List U8) (offset : I64) (acc : List U8) : Result String (Option (Pair I64 (List U8))) :=
  match Wire.find_crlf rest 0i64 {
    Option.none => Result.ok Option.none,
    Option.some idx =>
      if idx == 0i64
      then Result.ok (Option.some (Pair.pair (I64.add offset 2i64) acc))
      else Wire.decode_chunk_trailers (Strings.drop_bytes (I64.add idx 2i64) rest) (I64.add offset (I64.add idx 2i64)) acc
  }

// ── incremental chunked decoding ───────────────────────────────────────
//
// `decode_chunked` answers the buffered question ("is the whole body here
// yet?"); a streaming client needs the other one: given what arrived since
// last time, which body bytes are newly decoded? `chunk_step` folds
// `incoming` into `pending` (the undecoded remainder the previous step left)
// and walks every chunk that is fully buffered, answering the done flag, the
// bytes this step decoded, and the remainder to carry into the next step.
// The terminal chunk sets done without waiting for the trailer section:
// trailers carry no field this library keeps (see `decode_chunk_trailers`)
// and no body byte exists behind them, so waiting would only delay the
// caller's completion for bytes it will drop.

/// One incremental chunked decode. `ok ((done, decoded), pending')`:
/// `done` at the terminal chunk, `decoded` the body bytes this step produced
/// (possibly empty, also on the done path -- a step can decode data and then
/// meet the terminal chunk), `pending'` the bytes the next step starts from.
/// `err` for a body that cannot be decoded at all.
pub def Wire.chunk_step (pending : List U8) (incoming : List U8) : Result String (Pair (Pair Bool (List U8)) (List U8)) :=
  Wire.chunk_step_go (List.append pending incoming) List.empty

#[terminating]
def Wire.chunk_step_go (buf : List U8) (out : List U8) : Result String (Pair (Pair Bool (List U8)) (List U8)) :=
  match Wire.find_crlf buf 0i64 {
    Option.none => Result.ok (Pair.pair (Pair.pair false out) buf),
    Option.some idx =>
      match Wire.parse_chunk_size (Wire.take_bytes idx buf) {
        Result.err e => Result.err e,
        Result.ok size => Wire.chunk_step_size size buf (Strings.drop_bytes (I64.add idx 2i64) buf) out
      }
  }

/// Dispatch on a chunk size: zero is the terminator, anything else needs
/// `size` data bytes plus their CRLF before it can contribute. `buf` (the
/// walk's unconsumed bytes, size line included) is passed along so an
/// incomplete chunk returns it as the pending remainder instead of losing the
/// size line it had already read.
#[terminating]
def Wire.chunk_step_size (size : I64) (buf : List U8) (rest : List U8) (out : List U8) : Result String (Pair (Pair Bool (List U8)) (List U8)) :=
  if size == 0i64
  then Result.ok (Pair.pair (Pair.pair true out) List.empty)
  else
    if I64.gt size (I64.sub (List.length rest) 2i64)
    then Result.ok (Pair.pair (Pair.pair false out) buf)
    else Wire.chunk_step_data size rest out

/// Consume one data chunk's bytes plus the CRLF behind them, then continue
/// with the next size line. The length test in `chunk_step_size` guarantees
/// the CRLF is buffered, so it is checked rather than waited for.
#[terminating]
def Wire.chunk_step_data (size : I64) (rest : List U8) (out : List U8) : Result String (Pair (Pair Bool (List U8)) (List U8)) :=
  let data : List U8 := Wire.take_bytes size rest in
  let after : List U8 := Strings.drop_bytes size rest in
  match after {
    List.cons cr more1 =>
      match more1 {
        List.cons lf more2 =>
          if cr == 13u8
          then
            if lf == 10u8
            then Wire.chunk_step_go more2 (List.append out data)
            else Result.err "chunk data not CRLF-terminated"
          else Result.err "chunk data not CRLF-terminated",
        List.empty => Result.err "chunk data not CRLF-terminated"
      },
    List.empty => Result.err "chunk data not CRLF-terminated"
  }

/// Whether a response to `method` with `status` may carry a body at all.
/// `HEAD` answers the request with the headers the `GET` would have produced,
/// `Content-Length` included and no body behind it; 1xx, 204 and 304 are the
/// same shape for their own reasons.
pub def Wire.response_has_body (method : Method) (status : U16) : Bool :=
  if method == Method.HEAD
  then false
  else if U16.gt 200u16 status
  then false
  else if U16.beq status 204u16
  then false
  else Bool.not (U16.beq status 304u16)

/// Whether the head declares exactly `Transfer-Encoding: chunked` -- the
/// one transfer coding this library decodes. The coding name is compared
/// case-insensitively: transfer coding names are case-insensitive (RFC
/// 9112 §7), so a sloppy server's `Chunked` is the same coding.
/// `Option.none` when no `Transfer-Encoding` is present at all;
/// `Option.some false` when it names anything else, or stacks codings
/// (`gzip, chunked`), which stays the error it has always been: the chunks
/// would decode to bytes still encoded, and handing those to the caller
/// as a body is a lie with a `Content-Length`'s confidence.
def Wire.chunked_declared (headers : Headers) : Option Bool :=
  match Headers.get_all "transfer-encoding" headers {
    List.empty => Option.none,
    List.cons first rest =>
      // Bound step by step rather than nested: `(String.trim x) == "chunked"
      // "chunked"` -- a call inside a call's argument -- miscompiles in the
      // compiled backend, and this answer decides whether a body is decoded
      // at all.
      let trimmed : String := String.trim first in
      let lowered : String := String.to_lowercase trimmed in
      let is_chunked : Bool := lowered == "chunked" in
      let only : Bool := List.is_empty rest in
      Option.some (Bool.and only is_chunked)
  }

/// The framing a response's head declares, given the method it answers.
/// A chunked response is framed by its terminal chunk; a length, when both
/// are absent, means read-to-close.
///
/// The `chunked_declared` result matches a VARIABLE pattern and the Bool
/// is dispatched with an `if` below: constructor-with-literal patterns
/// (`Option.some true => ...`) on a cross-module call result misdispatch
/// in the compiled backend, and this is the decision that picks whether a
/// body is decoded at all.
pub def Wire.response_framing (method : Method) (status : U16) (headers : Headers) : Result String Framing :=
  if Bool.not (Wire.response_has_body method status)
  then Result.ok Framing.no_body
  else
    match Wire.chunked_declared headers {
      Option.some chunked =>
        if chunked
        then Result.ok Framing.chunked
        else Result.err "Transfer-Encoding is not supported",
      Option.none =>
        match Wire.parse_content_length headers {
          Result.err e => Result.err e,
          Result.ok opt =>
            match opt {
              Option.none => Result.ok Framing.until_eof,
              Option.some n => Result.ok (Framing.content_length n)
            }
        }
    }

/// The total byte length of the first message in `bytes`, given where its body
/// starts and how that body is framed.
///
/// `Option.none` means the message is not all here yet, which a single `read`
/// on a socket hits routinely; the caller reads more and asks again.
/// Read-to-close messages span everything buffered, because it is the close
/// and not a number that will end them. A chunked body that cannot be
/// decoded also answers `none` here -- the frame has no error channel, and
/// the EOF parse (`body_at`) is where the malformed size line is reported
/// rather than guessed around.
def Wire.message_total (body_start : I64) (framing : Framing) (bytes : List U8) : Option I64 :=
  match framing {
    Framing.no_body => Option.some body_start,
    Framing.until_eof => Option.some (List.length bytes),
    Framing.chunked =>
      match Wire.decode_chunked (Strings.drop_bytes body_start bytes) {
        Result.err _ => Option.none,
        Result.ok opt =>
          match opt {
            Option.none => Option.none,
            Option.some pr => Option.some (I64.add body_start pr.first)
          }
      },
    Framing.content_length n =>
      let total := I64.add body_start n in
      if I64.gt total (List.length bytes) then Option.none else Option.some total
  }

/// The body bytes at `body_start`, sliced by framing. An error when they are
/// not all present: this is handed one message, so asking for more than was
/// supplied means the caller framed it wrong -- and reporting the short body as
/// success is the silent truncation this section exists to remove.
def Wire.body_at (body_start : I64) (framing : Framing) (bytes : List U8) : Result String Body :=
  match framing {
    Framing.no_body => Result.ok Body.empty,
    Framing.until_eof => Result.ok (Wire.body_of (Strings.drop_bytes body_start bytes)),
    Framing.chunked =>
      match Wire.decode_chunked (Strings.drop_bytes body_start bytes) {
        Result.err e => Result.err e,
        Result.ok opt =>
          match opt {
            Option.none => Result.err "chunked body ended before the terminal chunk",
            Option.some pr => Result.ok (Wire.body_of pr.second)
          }
      },
    Framing.content_length n =>
      if I64.gt (I64.add body_start n) (List.length bytes)
      then Result.err "body shorter than Content-Length"
      else Result.ok (Wire.body_of (Wire.take_bytes n (Strings.drop_bytes body_start bytes)))
  }

pub def Wire.body_of (data : List U8) : Body :=
  if List.is_empty data then Body.empty else Body.bytes data

/// The headers of a message whose body starts at `body_start`.
pub def Wire.head_headers (body_start : I64) (bytes : List U8) : Result String Headers :=
  let head := Wire.take_bytes body_start bytes in
  match Wire.split_lines head {
    List.empty => Result.err "empty message",
    List.cons _ rest => Wire.parse_header_lines rest
  }

/// The status code of the response whose body starts at `body_start`.
pub def Wire.head_status (body_start : I64) (bytes : List U8) : Result String U16 :=
  let head := Wire.take_bytes body_start bytes in
  match Wire.split_lines head {
    List.empty => Result.err "empty response",
    List.cons first _ =>
      match Wire.parse_status_line first {
        Result.err e => Result.err e,
        Result.ok pr =>
          match pr {
            Pair.pair v _ =>
              match v {
                Pair.pair _ status => Result.ok status
              }
          }
      }
  }

/// Frame the first request in `bytes`: exactly one message, or `ok none` when
/// it is not all here yet. `err` means the head cannot be trusted, so the
/// caller must not guess a length from it.
pub def Wire.frame_request (bytes : List U8) : Result String (Option I64) :=
  match Wire.find_body_start bytes {
    Option.none => Result.ok Option.none,
    Option.some body_start =>
      match Wire.head_headers body_start bytes {
        Result.err e => Result.err e,
        Result.ok headers =>
          match Wire.request_framing headers {
            Result.err e => Result.err e,
            Result.ok framing => Result.ok (Wire.message_total body_start framing bytes)
          }
      }
  }

/// Frame the first response in `bytes`, for a request made with `method`.
pub def Wire.frame_response (bytes : List U8) (method : Method) : Result String (Option I64) :=
  match Wire.find_body_start bytes {
    Option.none => Result.ok Option.none,
    Option.some body_start =>
      match Wire.head_status body_start bytes {
        Result.err e => Result.err e,
        Result.ok status =>
          match Wire.head_headers body_start bytes {
            Result.err e => Result.err e,
            Result.ok headers =>
              match Wire.response_framing method status headers {
                Result.err e => Result.err e,
                Result.ok framing => Result.ok (Wire.message_total body_start framing bytes)
              }
          }
      }
  }

// ── parse request ──────────────────────────────────────────────────────

pub def Wire.parse_request (bytes : List U8) : Result String Request :=
  match Wire.find_body_start bytes {
    Option.none => Result.err "no header/body separator found",
    Option.some body_start => Wire.parse_request_after_headers body_start bytes
  }

def Wire.parse_request_after_headers (body_start : I64) (bytes : List U8) : Result String Request :=
  let head := Wire.take_bytes body_start bytes in
  match Wire.split_lines head {
    List.empty => Result.err "empty request",
    List.cons first rest =>
      match Wire.parse_request_line first {
        Result.err e => Result.err e,
        Result.ok pr =>
          match pr {
            Pair.pair m t =>
              match m {
                Pair.pair method target =>
                  match Wire.parse_header_lines rest {
                    Result.err e => Result.err e,
                    Result.ok headers =>
                      match Wire.request_framing headers {
                        Result.err e => Result.err e,
                        Result.ok framing =>
                          match Wire.body_at body_start framing bytes {
                            Result.err e => Result.err e,
                            Result.ok req_body =>
                              Result.ok ({ method := method, uri := Wire.target_to_uri target, headers := headers, version := t, body := req_body } : Request)
                          }
                      }
                  }
              }
          }
      }
  }

def Wire.parse_request_line (line : List U8) : Result String (Pair (Pair Method String) HttpVersion) :=
  match Strings.split_at_byte 32u8 line {
    Pair.pair method_bytes rest1 =>
      match Strings.split_at_byte 32u8 rest1 {
        Pair.pair target_bytes rest2 =>
          let ver_bytes := Wire.trim_trailing_crlf rest2 in
          match Wire.parse_method (String.trim (String.from_list method_bytes)) {
            Result.err e => Result.err e,
            Result.ok method =>
              match Wire.parse_version (String.trim (String.from_list ver_bytes)) {
                Result.err e => Result.err e,
                Result.ok version => Result.ok (Pair.pair (Pair.pair method (String.from_list target_bytes)) version)
              }
          }
      }
  }

def Wire.trim_trailing_crlf (bytes : List U8) : List U8 :=
  match List.reverse bytes {
    List.empty => List.empty,
    List.cons x rest =>
      if U8.beq x 10u8
      then
        match rest {
          List.empty => List.empty,
          List.cons y rest2 =>
            if U8.beq y 13u8
            then List.reverse rest2
            else bytes
        }
      else bytes
  }

def Wire.target_to_uri (target : String) : Uri :=
  match Uri.parse target {
    Result.err _ => Uri.uri "" Option.none "" Option.none target Option.none Option.none,
    Result.ok u => u
  }

// ── parse response ─────────────────────────────────────────────────────

/// Parse a response as the answer to a `GET`, which is what its framing
/// assumes. A caller that asked with `HEAD` -- whose response carries the
/// `Content-Length` of the body it is *not* sending -- must use
/// `Wire.parse_response_with_method`, or the body slice will not be there.
pub def Wire.parse_response (bytes : List U8) : Result String Response :=
  Wire.parse_response_with_method bytes Method.GET

pub def Wire.parse_response_with_method (bytes : List U8) (method : Method) : Result String Response :=
  match Wire.find_body_start bytes {
    Option.none => Result.err "no header/body separator found",
    Option.some body_start => Wire.parse_response_after_headers method body_start bytes
  }

def Wire.parse_response_after_headers (method : Method) (body_start : I64) (bytes : List U8) : Result String Response :=
  let head := Wire.take_bytes body_start bytes in
  match Wire.split_lines head {
    List.empty => Result.err "empty response",
    List.cons first rest =>
      match Wire.parse_status_line first {
        Result.err e => Result.err e,
        Result.ok pr =>
          match pr {
            Pair.pair v t =>
              match v {
                Pair.pair version status =>
                  match Wire.parse_header_lines rest {
                    Result.err e => Result.err e,
                    Result.ok headers =>
                      match Wire.response_framing method status headers {
                        Result.err e => Result.err e,
                        Result.ok framing =>
                          match Wire.body_at body_start framing bytes {
                            Result.err e => Result.err e,
                            Result.ok res_body =>
                              Result.ok ({ status := status, headers := headers, version := version, body := res_body } : Response)
                          }
                      }
                  }
              }
          }
      }
  }

def Wire.parse_status_line (line : List U8) : Result String (Pair (Pair HttpVersion U16) String) :=
  match Strings.split_at_byte 32u8 line {
    Pair.pair ver_bytes rest1 =>
      match Strings.split_at_byte 32u8 rest1 {
        Pair.pair status_bytes rest2 =>
          let reason := Wire.trim_trailing_crlf rest2 in
          match Wire.parse_version (String.trim (String.from_list ver_bytes)) {
            Result.err e => Result.err e,
            Result.ok version =>
              match Wire.parse_u16 (String.trim (String.from_list status_bytes)) {
                Result.err e => Result.err e,
                Result.ok status => Result.ok (Pair.pair (Pair.pair version status) (String.from_list reason))
              }
          }
      }
  }

/// Parse a three-digit status code. Delegates to the shared bounded parser so
/// an out-of-range status is rejected rather than truncated.
def Wire.parse_u16 (s : String) : Result String U16 :=
  Strings.parse_u16_bounded "status" (String.to_list s)
