/// Phase 9 tests — body handling, content-type, multipart parsing.

use http::types {Body.is_empty, bytes, empty, form, stream, text}
use http::body {
  Body.content_type, Body.from_bytes, Body.from_form, Body.from_text,
  Body.is_close_delim, Body.length, Body.parse_multipart, Body.to_bytes_pure,
}

#[test]
def test_content_type_text : Bool :=
  Body.content_type (Body.text "hello") == "text/plain; charset=utf-8"

#[test]
def test_content_type_bytes : Bool :=
  Body.content_type (Body.bytes (List.cons 0u8 List.empty)) == "application/octet-stream"

#[test]
def test_content_type_form : Bool :=
  Body.content_type (Body.form (List.cons (Pair.pair "k" "v") List.empty)) == "application/x-www-form-urlencoded"

#[test]
def test_content_type_empty : Bool :=
  Body.content_type Body.empty == ""

#[test]
def test_from_bytes_empty : Bool :=
  Body.is_empty (Body.from_bytes List.empty)

#[test]
def test_from_bytes_nonempty : Bool :=
  match Body.from_bytes (List.cons 1u8 List.empty) {
    Body.bytes _ => true,
    Body.empty => false,
    Body.text _ => false,
    Body.stream _ => false,
    Body.form _ => false
  }

#[test]
def test_from_text_empty : Bool :=
  Body.is_empty (Body.from_text "")

#[test]
def test_from_text_nonempty : Bool :=
  match Body.from_text "hi" {
    Body.text s => s == "hi",
    Body.empty => false,
    Body.bytes _ => false,
    Body.stream _ => false,
    Body.form _ => false
  }

#[test]
def test_from_form_empty : Bool :=
  Body.is_empty (Body.from_form List.empty)

#[test]
def test_from_form_nonempty : Bool :=
  match Body.from_form (List.cons (Pair.pair "k" "v") List.empty) {
    Body.form _ => true,
    Body.empty => false,
    Body.bytes _ => false,
    Body.text _ => false,
    Body.stream _ => false
  }

#[test]
def test_to_bytes_pure_text : Bool :=
  String.beq (String.from_list (Body.to_bytes_pure (Body.text "hello"))) "hello"

#[test]
def test_to_bytes_pure_bytes : Bool :=
  match Body.to_bytes_pure (Body.bytes (String.to_list "AB")) {
    List.cons a rest1 =>
      match rest1 {
        List.cons b rest2 =>
          U8.beq a 65u8 && U8.beq b 66u8 && List.is_empty rest2,
        List.empty => false
      },
    List.empty => false
  }

#[test]
def test_to_bytes_pure_form : Bool :=
  String.beq (String.from_list (Body.to_bytes_pure (Body.form (List.cons (Pair.pair "a" "b") List.empty)))) "a=b"

#[test]
def test_to_bytes_pure_empty : Bool :=
  List.is_empty (Body.to_bytes_pure Body.empty)

#[test]
def test_to_bytes_pure_stream : Bool :=
  match Body.to_bytes_pure (Body.stream (fn (_ : Unit) => IO.pure Option.none)) {
    List.empty => true,
    List.cons _ _ => false
  }

#[test]
def test_body_length_text : Bool :=
  Body.length (Body.text "hello") == 5

#[test]
def test_body_length_empty : Bool :=
  Body.length Body.empty == 0

#[test]
def test_body_length_bytes : Bool :=
  Body.length (Body.bytes (List.cons 1u8 (List.cons 2u8 (List.cons 3u8 List.empty)))) == 3

#[test]
def test_body_length_form : Bool :=
  Body.length (Body.form (List.cons (Pair.pair "a" "b") List.empty)) == 3

#[test]
def test_multipart_simple : Bool :=
  let body_str := "--BOUNDARY\r\nContent-Disposition: form-data; name=\"field1\"\r\n\r\nvalue1\r\n--BOUNDARY--\r\n" in
  let body := String.to_list body_str in
  match Body.parse_multipart "BOUNDARY" body {
    Result.err _ => false,
    Result.ok parts =>
      match parts {
        List.empty => false,
        List.cons p1 rest =>
          match rest {
            List.empty =>
              p1.name == "field1"
                && p1.filename == Option.none
                && String.beq (String.from_list p1.data) "value1",
            List.cons _ _ => false
          }
      }
  }

#[test]
def test_multipart_with_filename : Bool :=
  let body_str := "--BOUNDARY\r\nContent-Disposition: form-data; name=\"file\"; filename=\"test.txt\"\r\nContent-Type: text/plain\r\n\r\ncontents\r\n--BOUNDARY--\r\n" in
  let body := String.to_list body_str in
  match Body.parse_multipart "BOUNDARY" body {
    Result.err _ => false,
    Result.ok parts =>
      match parts {
        List.empty => false,
        List.cons p1 rest =>
          match rest {
            List.empty =>
              p1.name == "file"
                && match p1.filename {
                  Option.some f => f == "test.txt",
                  Option.none => false
                }
                && String.beq (String.from_list p1.data) "contents",
            List.cons _ _ => false
          }
      }
  }

#[test]
def test_multipart_multiple_parts : Bool :=
  let body_str := "--BOUNDARY\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\nval1\r\n--BOUNDARY\r\nContent-Disposition: form-data; name=\"b\"\r\n\r\nval2\r\n--BOUNDARY--\r\n" in
  let body := String.to_list body_str in
  match Body.parse_multipart "BOUNDARY" body {
    Result.err _ => false,
    Result.ok parts =>
      match parts {
        List.empty => false,
        List.cons p1 r1 =>
          match r1 {
            List.empty => false,
            List.cons p2 r2 =>
              match r2 {
                List.empty =>
                  p1.name == "a" && String.beq (String.from_list p1.data) "val1"
                    && p2.name == "b" && String.beq (String.from_list p2.data) "val2",
                List.cons _ _ => false
              }
          }
      }
  }

#[test]
def test_multipart_bad_boundary : Bool :=
  match Body.parse_multipart "WRONG" (String.to_list "--BOUNDARY--\r\n") {
    Result.ok _ => false,
    Result.err _ => true
  }

// ── closing-delimiter recognition ──────────────────────────────────────
//
// The close form is exactly `--` after the boundary token. The two short
// inputs used to report `true`, which made a truncated body indistinguishable
// from a complete one: `--BOUNDARY` parsed as a successful zero-part body.

/// A body that stops right after the token has no terminator at all.
#[test]
def test_multipart_truncated_after_boundary_fails : Bool :=
  match Body.parse_multipart "BOUNDARY" (String.to_list "--BOUNDARY") {
    Result.ok _ => false,
    Result.err _ => true
  }

/// A single dash is not the closing form either.
#[test]
def test_multipart_lone_dash_fails : Bool :=
  match Body.parse_multipart "BOUNDARY" (String.to_list "--BOUNDARY-") {
    Result.ok _ => false,
    Result.err _ => true
  }

/// The close form on its own is legitimate, and means zero parts.
#[test]
def test_multipart_close_only_ok : Bool :=
  match Body.parse_multipart "BOUNDARY" (String.to_list "--BOUNDARY--\r\n") {
    Result.err _ => false,
    Result.ok parts => List.is_empty parts
  }

// ── close delimiter ─────────────────────────────────────────────────────
//
// `Body.is_close_delim` answers whether the bytes after a boundary token are
// the closing `--`. Reading a truncated body as terminated is the failure mode
// these pin: an empty remainder, or one dash, is a body that stopped, not a
// body that ended.

#[test]
def test_close_delim_both_dashes : Bool :=
  Body.is_close_delim (String.to_list "--")

/// The empty input used to answer `true`, which turned a body ending exactly
/// at a boundary token into a successful parse with zero parts.
#[test]
def test_close_delim_empty_is_false : Bool :=
  Bool.not (Body.is_close_delim List.empty)

#[test]
def test_close_delim_lone_dash_is_false : Bool :=
  Bool.not (Body.is_close_delim (String.to_list "-"))

#[test]
def test_close_delim_one_dash_then_other_is_false : Bool :=
  Bool.not (Body.is_close_delim (String.to_list "-x"))

/// Trailing CRLF after the closing dashes does not change the answer.
#[test]
def test_close_delim_with_crlf : Bool :=
  Body.is_close_delim (String.to_list "--\r\n")
