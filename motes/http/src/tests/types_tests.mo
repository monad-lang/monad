/// Phase 1 tests for the `http` mote core types.

use http::types {
  Body.is_empty, Body.is_text, DELETE, GET, Headers, Headers.set_checked,
  PATCH, POST, Request, Response, Response.bytes, Response.json,
  Response.json_bytes, Response.no_content, Response.redirect, Response.text,
  Response.with_header, Status.internal_server_error, Status.not_found,
  Status.ok, Uri, http1_0, http1_1,
}
use std::show {Show}

#[test]
def test_request_get_fields : Bool :=
  let u : Uri := Uri.uri "https" Option.none "example.com" Option.none "/" Option.none Option.none in
  let r : Request := Request.get u in
  match r {
    { method, uri, headers, version, body, .. } =>
      method == Method.GET
        && Uri.host uri == "example.com"
        && Headers.is_empty headers
        && version == HttpVersion.http1_1
        && Body.is_empty body
  }

#[test]
def test_response_ok_text : Bool :=
  let r : Response := Response.ok_text "hi" in
  match r {
    { status, headers, version, body } =>
      status == Status.ok
        && Headers.is_empty headers
        && version == HttpVersion.http1_1
        && Body.is_text body "hi"
  }

#[test]
def test_method_eq : Bool :=
  Method.GET == Method.GET
    && Bool.not (Method.GET == Method.POST)
    && Method.POST == Method.POST

#[test]
def test_method_show : Bool :=
  Show.show Method.GET == "GET"
    && Show.show Method.DELETE == "DELETE"
    && Show.show Method.PATCH == "PATCH"

#[test]
def test_http_version_show : Bool :=
  Show.show HttpVersion.http1_1 == "HTTP/1.1"
    && Show.show HttpVersion.http1_0 == "HTTP/1.0"

#[test]
def test_status_constants : Bool :=
  Status.ok == 200u16
    && Status.not_found == 404u16
    && Status.internal_server_error == 500u16

def expect_some (got : Option String) (want : String) : Bool :=
  match got {
    Option.some v => v == want,
    Option.none => false
  }

#[test]
def test_headers_case_insensitive : Bool :=
  let h0 : Headers := Headers.empty in
  let h1 : Headers := Headers.set "Content-Type" "text/html" h0 in
  let h2 : Headers := Headers.add "X-Custom" "yes" h1 in
  expect_some (Headers.get "content-type" h2) "text/html"

#[test]
def test_headers_set_replaces : Bool :=
  let h0 : Headers := Headers.set "X" "1" Headers.empty in
  let h1 : Headers := Headers.set "x" "2" h0 in
  expect_some (Headers.get "X" h1) "2"

/// A removed key is gone whichever spelling looked it up.
#[test]
def test_headers_remove : Bool :=
  let h0 : Headers := Headers.set "Content-Type" "text/plain" Headers.empty in
  let h1 : Headers := Headers.remove "content-type" h0 in
  match Headers.get "Content-Type" h1 {
    Option.none => true,
    Option.some _ => false
  }

/// Removing a key that is not there leaves the rest alone rather than failing.
#[test]
def test_headers_remove_absent_keeps_others : Bool :=
  let h0 : Headers := Headers.set "X" "1" Headers.empty in
  let h1 : Headers := Headers.remove "Y" h0 in
  expect_some (Headers.get "X" h1) "1"

/// Removal takes every value, so a duplicate cannot survive it.
#[test]
def test_headers_remove_drops_duplicates : Bool :=
  let h0 : Headers := Headers.add "X" "2" (Headers.set "X" "1" Headers.empty) in
  let h1 : Headers := Headers.remove "X" h0 in
  Headers.is_empty h1

// ── response constructors ──────────────────────────────────────────────

#[test]
def test_response_text : Bool :=
  let r := Response.text 201u16 "made" in
  r.status == 201u16 && Body.is_text r.body "made" && Headers.is_empty r.headers

#[test]
def test_response_html_content_type : Bool :=
  let r := Response.html 200u16 "<p>x</p>" in
  expect_some (Headers.get "Content-Type" r.headers) "text/html; charset=utf-8"

#[test]
def test_response_json_content_type : Bool :=
  let r := Response.json 200u16 "{}" in
  expect_some (Headers.get "Content-Type" r.headers) "application/json"

#[test]
def test_response_json_bytes_content_type : Bool :=
  let r := Response.json_bytes 200u16 (String.to_list "{}") in
  expect_some (Headers.get "Content-Type" r.headers) "application/json"

#[test]
def test_response_bytes_content_type : Bool :=
  let r := Response.bytes 200u16 (String.to_list "abc") "application/octet-stream" in
  expect_some (Headers.get "Content-Type" r.headers) "application/octet-stream"

#[test]
def test_response_no_content : Bool :=
  let r := Response.no_content in
  r.status == 204u16 && Body.is_empty r.body

#[test]
def test_response_redirect_location : Bool :=
  let r := Response.redirect 302u16 "https://example.com/next" in
  r.status == 302u16
    && expect_some (Headers.get "Location" r.headers) "https://example.com/next"

#[test]
def test_response_with_header : Bool :=
  let r := Response.with_header "X-Test" "yes" (Response.text 200u16 "ok") in
  expect_some (Headers.get "X-Test" r.headers) "yes"

// ── checked header insertion ───────────────────────────────────────────

#[test]
def test_headers_set_checked_accepts : Bool :=
  match Headers.set_checked "X-Test" "ok" Headers.empty {
    Result.ok h => expect_some (Headers.get "X-Test" h) "ok",
    Result.err _ => false
  }

#[test]
def test_headers_set_checked_rejects_crlf_value : Bool :=
  match Headers.set_checked "X-Test" "ok\r\nSet-Cookie: a=b" Headers.empty {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_headers_set_checked_rejects_bad_name : Bool :=
  match Headers.set_checked "X Test" "ok" Headers.empty {
    Result.err _ => true,
    Result.ok _ => false
  }
