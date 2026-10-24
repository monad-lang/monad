/// Body handling — Layer 0, pure Monad.
///
/// Default Content-Type inference per `Body` variant, plus multipart
/// `form-data` parsing (RFC 7578). The `Body.to_bytes_pure` and
/// `Body.content_type` helpers are used by both `moose` (client) and
/// `moon` (server).
///
/// A `Body.stream` cannot be drained — there is no `IO`-context counterpart
/// that binds it — so writing one out is an error rather than zero bytes:
/// `Wire.body_bytes` and `Wire.content_length_of` are what serialisation goes
/// through, and both refuse. `Body.to_bytes_pure` and `Body.length` are pure
/// projections of those, for callers looking at a body they know is not a
/// stream. The parser never produces a stream.
///
/// Byte-level work — splitting lines, trimming a CRLF, splitting a header —
/// lives in `Wire`, which this module depends on rather than duplicating. What
/// is here is what a *body* means: its content type, its form encoding, and the
/// multipart grammar.

use http::strings {
  Strings.list_drop_prefix, Strings.list_starts_with, Strings.split_at_byte,
  Strings.split_on,
}
use lib::types {Body, Headers}
use lib::uri {Uri.format_query, Uri.percent_decode}
use http::wire {
  Wire.body_bytes, Wire.content_length_of, Wire.drop_leading_space,
  Wire.parse_one_header, Wire.split_lines, Wire.trim_trailing_crlf,
}

// ── content type ─────────────────────────────────────────────────────────

/// Default Content-Type per `Body` variant.
/// `stream` has no default — the caller must set `Content-Type` explicitly.
pub def Body.content_type (b : Body) : String :=
  match b {
    Body.empty => "",
    Body.text _ => "text/plain; charset=utf-8",
    Body.bytes _ => "application/octet-stream",
    Body.form _ => "application/x-www-form-urlencoded",
    Body.stream _ => ""
  }

// ── body construction helpers ───────────────────────────────────────────

pub def Body.from_bytes (data : List U8) : Body :=
  if List.is_empty data
  then Body.empty
  else Body.bytes data

pub def Body.from_text (s : String) : Body :=
  if String.is_empty s
  then Body.empty
  else Body.text s

pub def Body.from_form (fields : List (Pair String String)) : Body :=
  if List.is_empty fields
  then Body.empty
  else Body.form fields

// ── form data ───────────────────────────────────────────────────────────
//
// A submitted form is a transport-level concern: the caller has a
// `Request`, and wants fields or parts without re-implementing content-type
// parsing. `parse_form` dispatches on the media type; `parse_urlencoded`
// and `parse_multipart_of` do the two encodings. Duplicate field names are
// preserved in order (a browser may submit the same name twice), and a
// malformed escape is an error rather than a silently garbled value.

/// The media type of the request's `Content-Type`, lowercased and with its
/// parameters removed. `""` when the header is absent.
pub def Body.media_type (headers : Headers) : String :=
  match Headers.get "content-type" headers {
    Option.none => "",
    Option.some ct => String.to_lowercase (String.trim (String.from_list (Body.take_until_semi (String.to_list ct))))
  }

/// The `boundary=` parameter of a multipart `Content-Type`. Quoted and bare
/// forms are both accepted; an absent or empty boundary is an error.
pub def Body.boundary_of (headers : Headers) : Result String String :=
  match Headers.get "content-type" headers {
    Option.none => Result.err "missing Content-Type",
    Option.some ct =>
      let b := Body.extract_param "boundary" ct in
      if String.is_empty b
      then Result.err "multipart boundary missing"
      else Result.ok b
  }

/// Decode an `application/x-www-form-urlencoded` body. `+` means space and
/// each key/value is percent-decoded. Duplicate keys are kept, in order.
pub def Body.parse_urlencoded (s : String) : Result String (List (Pair String String)) :=
  if String.is_empty s
  then Result.ok List.empty
  else Body.parse_urlencoded_entries (Strings.split_on "&" s)

#[terminating]
def Body.parse_urlencoded_entries (entries : List String) : Result String (List (Pair String String)) :=
  match entries {
    List.empty => Result.ok List.empty,
    List.cons e rest =>
      if String.is_empty e
      then Body.parse_urlencoded_entries rest
      else
        match Body.parse_urlencoded_pair e {
          Result.err err => Result.err err,
          Result.ok pair =>
            match Body.parse_urlencoded_entries rest {
              Result.err err => Result.err err,
              Result.ok pairs => Result.ok (List.cons pair pairs)
            }
        }
  }

def Body.parse_urlencoded_pair (e : String) : Result String (Pair String String) :=
  match Strings.split_at_byte 61u8 (String.to_list e) {
    Pair.pair k_bytes v_bytes =>
      match Body.form_decode (String.from_list k_bytes) {
        Result.err err => Result.err err,
        Result.ok k =>
          match Body.form_decode (String.from_list v_bytes) {
            Result.err err => Result.err err,
            Result.ok v => Result.ok (Pair.pair k v)
          }
      }
  }

/// `+` -> space, then percent-decode. An invalid escape is an error.
def Body.form_decode (s : String) : Result String String :=
  Uri.percent_decode (Body.plus_to_space s)

def Body.plus_to_space (s : String) : String :=
  String.from_list (Body.plus_to_space_go (String.to_list s))

#[terminating]
def Body.plus_to_space_go (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons b rest =>
      if U8.beq b 43u8
      then List.cons 32u8 (Body.plus_to_space_go rest)
      else List.cons b (Body.plus_to_space_go rest)
  }

/// The raw bytes of a body, for the form parsers. A stream cannot be
/// decoded here; the caller must drain it first (the IO counterpart).
def Body.bytes_content (b : Body) : Result String (List U8) :=
  match b {
    Body.empty => Result.ok List.empty,
    Body.bytes data => Result.ok data,
    Body.text s => Result.ok (String.to_list s),
    Body.form fields => Result.ok (String.to_list (Uri.format_query fields)),
    Body.stream _ => Result.err "form body is a stream"
  }

/// Dispatch on the request's media type and decode the body. Wrong media
/// types are errors; an empty body is an empty field list.
pub def Body.parse_form (headers : Headers) (body : Body) : Result String (List (Pair String String)) :=
  let mt := Body.media_type headers in
  if String.is_empty mt
  then Result.err "missing Content-Type"
  else if String.beq mt "application/x-www-form-urlencoded"
  then
    match Body.bytes_content body {
      Result.err e => Result.err e,
      Result.ok bytes => Body.parse_urlencoded (String.from_list bytes)
    }
  else Result.err (String.concat "not a form body: " mt)

/// Dispatch on the request's media type and decode a multipart body.
pub def Body.parse_multipart_of (headers : Headers) (body : Body) : Result String (List MultipartPart) :=
  let mt := Body.media_type headers in
  if String.is_empty mt
  then Result.err "missing Content-Type"
  else if String.beq mt "multipart/form-data"
  then
    match Body.boundary_of headers {
      Result.err e => Result.err e,
      Result.ok boundary =>
        match Body.bytes_content body {
          Result.err e => Result.err e,
          Result.ok bytes => Body.parse_multipart boundary bytes
        }
    }
  else Result.err (String.concat "not a multipart body: " mt)

// ── body to bytes (pure projection) ─────────────────────────────────────

/// Convert a `Body` to `List U8`, projecting the failure away.
///
/// This is a *reader*, not the serialiser. `Wire.body_bytes` is what writing
/// goes through and it refuses a `Body.stream`; the projection renders one as
/// zero bytes for callers that only want to look at a body they know is not a
/// stream (`Body.length` below, and the tests).
pub def Body.to_bytes_pure (b : Body) : List U8 :=
  match Wire.body_bytes b {
    Result.ok bytes => bytes,
    Result.err _ => List.empty
  }

// ── body length ─────────────────────────────────────────────────────────

/// The byte length of a `Body`, projected the same way as `Body.to_bytes_pure`.
/// `Wire.content_length_of` is the version framing uses, and it refuses a
/// stream rather than declaring it zero bytes long.
pub def Body.length (b : Body) : I64 :=
  match Wire.content_length_of b {
    Result.ok len => len,
    Result.err _ => 0
  }

// ── multipart/form-data parsing (RFC 7578) ──────────────────────────────
//
// Multipart bodies look like:
//
//   --BOUNDARY\r\n
//   Content-Disposition: form-data; name="field1"\r\n
//   \r\n
//   value1\r\n
//   --BOUNDARY\r\n
//   Content-Disposition: form-data; name="file"; filename="test.txt"\r\n
//   Content-Type: text/plain\r\n
//   \r\n
//   file contents\r\n
//   --BOUNDARY--\r\n
//
// The parser splits on `--BOUNDARY`, extracts headers per part, and
// returns a list of `MultipartPart` records. The final `--BOUNDARY--`
// delimiter terminates the body; trailing data after it is ignored.

pub type MultipartPart {
  part (name : String) (filename : Option String) (headers : Headers) (data : List U8)
}
open MultipartPart { part }

pub def MultipartPart.field_name (p : MultipartPart) : String :=
  match p {
    MultipartPart.part name _ _ _ => name
  }

pub def MultipartPart.file_name (p : MultipartPart) : Option String :=
  match p {
    MultipartPart.part _ filename _ _ => filename
  }

pub def MultipartPart.content_type (p : MultipartPart) : Option String :=
  match p {
    MultipartPart.part _ _ hs _ => Headers.get "content-type" hs
  }

pub def MultipartPart.bytes (p : MultipartPart) : List U8 :=
  match p {
    MultipartPart.part _ _ _ data => data
  }

/// Parse a `multipart/form-data` body. `boundary` is the boundary string
/// (without the leading `--`). Returns the parts or an error message.
pub def Body.parse_multipart (boundary : String) (body : List U8) : Result String (List MultipartPart) :=
  let delim := String.to_list (String.concat "--" boundary) in
  match Body.find_delim delim body {
    Option.none => Result.err "multipart boundary not found",
    Option.some after_delim =>
      if Body.is_close_delim after_delim
      then Result.ok List.empty
      else Body.parse_parts delim after_delim List.empty
  }

/// Parse parts recursively: each call parses one part, then checks whether
/// the remaining input (after the part's terminating boundary) is the close
/// delimiter (`--\r\n`). If so, all parts have been found; otherwise the
/// remaining input is `\r\n` + the next part's content, so recurse.
#[terminating]
def Body.parse_parts (delim : List U8) (input : List U8) (acc : List MultipartPart) : Result String (List MultipartPart) :=
  match Body.parse_one_part delim input {
    Result.err e => Result.err e,
    Result.ok part_rest =>
      let part := part_rest.first in
      let next := part_rest.second in
      if Body.is_close_delim next
      then Result.ok (List.reverse (List.cons part acc))
      else Body.parse_parts delim next (List.cons part acc)
  }

/// Check whether the bytes following a boundary token are the closing `--`
/// of `--BOUNDARY--`, i.e. that this delimiter ends the multipart body.
///
/// Both short inputs are `false`, not `true`: a body that stops right after
/// the token (`--BOUNDARY`) or after a single dash (`--BOUNDARY-`) has no
/// terminator at all, and reporting either as a close delimiter turns a
/// truncated body into a successful parse with zero parts -- the same
/// silent-truncation shape as an EOF read reported as success.
def Body.is_close_delim (input : List U8) : Bool :=
  match input {
    List.empty => false,
    List.cons x rest =>
      if U8.beq x 45u8
      then
        match rest {
          List.empty => false,
          List.cons y _ => U8.beq y 45u8
        }
      else false
  }

/// Parse one multipart part: headers, blank line, body (up to next boundary).
/// Returns the parsed part and the remaining input after the boundary line.
def Body.parse_one_part (delim : List U8) (input : List U8) : Result String (Pair MultipartPart (List U8)) :=
  match Body.split_headers_body input {
    Pair.pair header_bytes data_bytes =>
      match Body.parse_part_headers header_bytes {
        Result.err e => Result.err e,
        Result.ok ph => Body.parse_one_part_body delim ph data_bytes
      }
  }

def Body.parse_one_part_body (delim : List U8) (ph : PartHeaders) (data_bytes : List U8) : Result String (Pair MultipartPart (List U8)) :=
  match Body.find_delim delim data_bytes {
    Option.none => Result.err "part body without closing boundary",
    Option.some after =>
      let part_data := Wire.trim_trailing_crlf (Body.take_until_delim delim data_bytes) in
      Result.ok (Pair.pair (MultipartPart.part ph.name ph.filename ph.headers part_data) after)
  }

/// Split the part at the first blank line (CRLFCRLF), separating headers
/// from body data.
def Body.split_headers_body (input : List U8) : Pair (List U8) (List U8) :=
  Body.split_headers_body_go input List.empty

#[terminating]
def Body.split_headers_body_go (input : List U8) (acc : List U8) : Pair (List U8) (List U8) :=
  match input {
    List.empty => Pair.pair (List.reverse acc) List.empty,
    List.cons x rest =>
      if U8.beq x 13u8
      then
        match rest {
          List.empty => Pair.pair (List.reverse acc) List.empty,
          List.cons y rest2 =>
            if U8.beq y 10u8
            then
              match rest2 {
                List.empty => Pair.pair (List.reverse acc) List.empty,
                List.cons z rest3 =>
                  if U8.beq z 13u8
                  then
                    match rest3 {
                      List.empty => Pair.pair (List.reverse acc) List.empty,
                      List.cons w rest4 =>
                        if U8.beq w 10u8
                        then Pair.pair (List.reverse acc) rest4
                        else Body.split_headers_body_go rest2 (List.cons y (List.cons x acc))
                    }
                  else Body.split_headers_body_go rest2 (List.cons y (List.cons x acc))
              }
            else Body.split_headers_body_go rest (List.cons x acc)
        }
      else Body.split_headers_body_go rest (List.cons x acc)
  }

/// Parsed part headers — the name and filename from Content-Disposition,
/// plus all headers for the part.
struct PartHeaders {
  name : String,
  filename : Option String,
  headers : Headers
}

def Body.parse_part_headers (bytes : List U8) : Result String PartHeaders :=
  let lines := Wire.split_lines bytes in
  match Body.extract_disposition lines {
    Result.err e => Result.err e,
    Result.ok disp =>
      let headers := Body.parse_part_header_lines lines in
      // Read the pair's fields into their own bindings rather than inlining
      // `disp.first`/`disp.second` into the literal: the self-hosted checker
      // types a read from a parameterized `Pair` with the inductive's own
      // parameter left unsubstituted, which only survives where no expected
      // type is in play. A bare binding introduces no expectation; a
      // literal's field does.
      let name := disp.first in
      let filename := disp.second in
      Result.ok ({ name := name, filename := filename, headers := headers } : PartHeaders)
  }

/// Extract `name` and `filename` from the Content-Disposition header line.
/// Returns `Pair name filename` (filename may be `Option.none`).
def Body.extract_disposition (lines : List (List U8)) : Result String (Pair String (Option String)) :=
  match Body.find_disposition_line lines {
    Option.none => Result.err "Content-Disposition header not found in multipart part",
    Option.some line =>
      let name := Body.extract_param value_name (String.from_list line) in
      let filename := Body.extract_param value_filename (String.from_list line) in
      let filename_opt := if String.is_empty filename then Option.none else Option.some filename in
      Result.ok (Pair.pair name filename_opt)
  }

def Body.find_disposition_line (lines : List (List U8)) : Option (List U8) :=
  match lines {
    List.empty => Option.none,
    List.cons line rest =>
      if Body.starts_with_ci (String.to_list "content-disposition:") line
      then Option.some line
      else Body.find_disposition_line rest
  }

/// Check if `prefix` is a case-insensitive prefix of `bytes`.
def Body.starts_with_ci (prefix : List U8) (bytes : List U8) : Bool :=
  match prefix {
    List.empty => true,
    List.cons p ps =>
      match bytes {
        List.empty => false,
        List.cons x xs =>
          if Body.eq_ci p x
          then Body.starts_with_ci ps xs
          else false
      }
  }

/// Case-insensitive byte equality for ASCII letters.
def Body.eq_ci (a : U8) (b : U8) : Bool :=
  if U8.beq a b
  then true
  else if U8.lt a 65u8
  then false
  else if U8.lt a 91u8
  then U8.beq (U8.add a 32u8) b
  else if U8.lt b 65u8
  then false
  else if U8.lt b 91u8
  then U8.beq a (U8.add b 32u8)
  else false

/// Extract a `name="value"` or `name=value` parameter from a header line.
/// `param_name` is the parameter to find (e.g. `name`, `filename`).
def Body.extract_param (param_name : String) (line : String) : String :=
  Body.extract_param_go (String.to_list param_name) (String.to_list line)

#[terminating]
def Body.extract_param_go (param : List U8) (input : List U8) : String :=
  match input {
    List.empty => "",
    List.cons _ rest =>
      if Body.starts_with_ci param input
      then Body.extract_param_value (Body.drop_param param input)
      else Body.extract_param_go param rest
  }

/// Drop the param name and optional `=` from the input, returning what's
/// after.
def Body.drop_param (param : List U8) (input : List U8) : List U8 :=
  match param {
    List.empty => Body.drop_eq input,
    List.cons _ ps =>
      match input {
        List.empty => List.empty,
        List.cons _ xs => Body.drop_param ps xs
      }
  }

def Body.drop_eq (input : List U8) : List U8 :=
  match input {
    List.empty => List.empty,
    List.cons x rest =>
      if U8.beq x 61u8
      then rest
      else if U8.beq x 32u8
      then Body.drop_eq rest
      else input
  }

/// Extract the value after `=`: strip optional quotes, read until `;` or
/// end.
def Body.extract_param_value (input : List U8) : String :=
  let stripped := Wire.drop_leading_space input in
  match stripped {
    List.empty => "",
    List.cons x rest =>
      if U8.beq x 34u8
      then String.from_list (Body.take_until_quote rest)
      else String.from_list (Body.take_until_semi stripped)
  }

def Body.take_until_quote (input : List U8) : List U8 :=
  Body.take_until_quote_go input List.empty

#[terminating]
def Body.take_until_quote_go (input : List U8) (acc : List U8) : List U8 :=
  match input {
    List.empty => List.reverse acc,
    List.cons x rest =>
      if U8.beq x 34u8
      then List.reverse acc
      else Body.take_until_quote_go rest (List.cons x acc)
  }

def Body.take_until_semi (input : List U8) : List U8 :=
  Body.take_until_semi_go input List.empty

#[terminating]
def Body.take_until_semi_go (input : List U8) (acc : List U8) : List U8 :=
  match input {
    List.empty => List.reverse acc,
    List.cons x rest =>
      if U8.beq x 59u8
      then List.reverse acc
      else Body.take_until_semi_go rest (List.cons x acc)
  }

/// Parse header lines (List of byte lists) into a Headers value.
def Body.parse_part_header_lines (lines : List (List U8)) : Headers :=
  Body.parse_part_header_lines_go lines Headers.empty

def Body.parse_part_header_lines_go (lines : List (List U8)) (acc : Headers) : Headers :=
  match lines {
    List.empty => acc,
    List.cons line rest =>
      if List.is_empty line
      then acc
      else
        // A part header that does not parse is skipped rather than failing the
        // part: one malformed line in a multipart section should not cost the
        // caller the whole body. `Wire.parse_one_header` is the same split,
        // and reports the malformed case instead of hiding it.
        match Wire.parse_one_header line {
          Result.err _ => Body.parse_part_header_lines_go rest acc,
          Result.ok kv =>
            let k := kv.first in
            let v := kv.second in
            Body.parse_part_header_lines_go rest (Headers.add k v acc)
        }
  }

/// Find the delimiter in the input, return what's after it, or none.
def Body.find_delim (delim : List U8) (input : List U8) : Option (List U8) :=
  Body.find_delim_go delim input

#[terminating]
def Body.find_delim_go (delim : List U8) (input : List U8) : Option (List U8) :=
  match input {
    List.empty => Option.none,
    List.cons _ rest =>
      if Strings.list_starts_with delim input
      then Option.some (Strings.list_drop_prefix delim input)
      else Body.find_delim_go delim rest
  }

/// Take bytes until the delimiter is found (exclusive).
def Body.take_until_delim (delim : List U8) (input : List U8) : List U8 :=
  Body.take_until_delim_go delim input List.empty

#[terminating]
def Body.take_until_delim_go (delim : List U8) (input : List U8) (acc : List U8) : List U8 :=
  match input {
    List.empty => List.reverse acc,
    List.cons x rest =>
      if Strings.list_starts_with delim input
      then List.reverse acc
      else Body.take_until_delim_go delim rest (List.cons x acc)
  }

// ── param name constants (avoid reserved keyword conflicts) ────────────

def value_name : String := "name"
def value_filename : String := "filename"
