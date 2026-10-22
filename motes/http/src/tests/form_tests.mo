/// Form-data tests: urlencoded decoding, media-type/boundary dispatch,
/// multipart-from-headers, part accessors, and the Request helpers.

use std::list {List.length}
use http::types {
  Headers, Headers.empty, Headers.set, Method, Request, Uri, bytes, text,
}
use http::body {
  Body.boundary_of, Body.media_type, Body.parse_form, Body.parse_multipart_of,
  Body.parse_urlencoded, MultipartPart.bytes, MultipartPart.field_name,
  MultipartPart.file_name,
}
use http::request {Request.form_fields, Request.param}

#[test]
def test_urlencoded_basic : Bool :=
  match Body.parse_urlencoded "a=1&b=2" {
    Result.err _ => false,
    Result.ok fields =>
      List.length fields == 2
        && match Request.param "a" fields {
          Option.some v => String.beq v "1",
          Option.none => false
        }
        && match Request.param "b" fields {
          Option.some v => String.beq v "2",
          Option.none => false
        }
  }

#[test]
def test_urlencoded_plus_is_space : Bool :=
  match Body.parse_urlencoded "q=hello+world" {
    Result.err _ => false,
    Result.ok fields =>
      match Request.param "q" fields {
        Option.some v => String.beq v "hello world",
        Option.none => false
      }
  }

#[test]
def test_urlencoded_percent_decoded : Bool :=
  match Body.parse_urlencoded "a=%41%42" {
    Result.err _ => false,
    Result.ok fields =>
      match Request.param "a" fields {
        Option.some v => String.beq v "AB",
        Option.none => false
      }
  }

#[test]
def test_urlencoded_duplicates_preserved : Bool :=
  match Body.parse_urlencoded "a=1&a=2" {
    Result.err _ => false,
    Result.ok fields => List.length fields == 2
  }

#[test]
def test_urlencoded_empty_is_empty_list : Bool :=
  match Body.parse_urlencoded "" {
    Result.err _ => false,
    Result.ok fields => List.is_empty fields
  }

#[test]
def test_urlencoded_malformed_escape_is_error : Bool :=
  match Body.parse_urlencoded "a=%G1" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_media_type_strips_params_and_lowercases : Bool :=
  let hs := Headers.set "Content-Type" "Multipart/Form-Data; boundary=BOUND" Headers.empty in
  String.beq (Body.media_type hs) "multipart/form-data"

#[test]
def test_boundary_bare : Bool :=
  let hs := Headers.set "Content-Type" "multipart/form-data; boundary=BOUND" Headers.empty in
  match Body.boundary_of hs {
    Result.err _ => false,
    Result.ok b => String.beq b "BOUND"
  }

#[test]
def test_boundary_quoted : Bool :=
  let hs := Headers.set "Content-Type" "multipart/form-data; boundary=\"BOUND\"" Headers.empty in
  match Body.boundary_of hs {
    Result.err _ => false,
    Result.ok b => String.beq b "BOUND"
  }

#[test]
def test_boundary_missing_is_error : Bool :=
  let hs := Headers.set "Content-Type" "multipart/form-data" Headers.empty in
  match Body.boundary_of hs {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_parse_form_urlencoded : Bool :=
  let hs := Headers.set "Content-Type" "application/x-www-form-urlencoded" Headers.empty in
  match Body.parse_form hs (Body.text "a=1&b=2") {
    Result.err _ => false,
    Result.ok fields => List.length fields == 2
  }

#[test]
def test_parse_form_wrong_media_type_is_error : Bool :=
  let hs := Headers.set "Content-Type" "text/plain" Headers.empty in
  match Body.parse_form hs (Body.text "a=1") {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_parse_multipart_from_headers : Bool :=
  let raw := "--BOUND\r\nContent-Disposition: form-data; name=\"a\"\r\n\r\n1\r\n--BOUND--\r\n" in
  let hs := Headers.set "Content-Type" "multipart/form-data; boundary=BOUND" Headers.empty in
  match Body.parse_multipart_of hs (Body.bytes (String.to_list raw)) {
    Result.err _ => false,
    Result.ok parts =>
      match parts {
        List.empty => false,
        List.cons p rest =>
          List.is_empty rest
            && String.beq (MultipartPart.field_name p) "a"
            && String.beq (String.from_list (MultipartPart.bytes p)) "1"
            && match MultipartPart.file_name p {
              Option.none => true,
              Option.some _ => false
            }
      }
  }

#[test]
def test_request_form_fields : Bool :=
  let hs := Headers.set "Content-Type" "application/x-www-form-urlencoded" Headers.empty in
  let base : Request := Request.get (Uri.uri "" Option.none "" Option.none "/" Option.none Option.none) in
  let req : Request := { base with method := Method.POST, headers := hs, body := Body.text "a=1" } in
  match Request.form_fields req {
    Result.err _ => false,
    Result.ok fields =>
      match Request.param "a" fields {
        Option.some v => String.beq v "1",
        Option.none => false
      }
  }
