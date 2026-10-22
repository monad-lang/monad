/// Static-file tests: MIME, byte exactness, traversal, ETag and ranges.
///
/// These exercise the pure response builder directly (no sockets), plus one
/// real file read for the binary case. Fixtures live under `/tmp` with
/// process-scoped names so parallel worktrees do not collide.

use std::io {IO.write_file_bytes}
use std::path {Path}
use std::process {process_id}
use http::body {Body.to_bytes_pure}
use http::types {
  Body, Headers, Headers.empty, Headers.get, Headers.set, Method, Request,
  Response, Status.not_found, Status.not_modified, Status.ok,
  Status.partial_content, Status.range_not_satisfiable, Uri, http1_1,
}
use moon::static_files {
  Static.etag_matches, Static.handler, Static.mime_of, Static.range,
  Static.respond, Static.safe_path, StaticConfig, StaticConfig.default,
}

def get_path (path : String) : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

def get_with (path : String) (headers : Headers) : Request :=
  { method := Method.GET, uri := Uri.uri "" Option.none "" Option.none path Option.none Option.none, headers := headers, version := HttpVersion.http1_1, body := Body.empty }

def header (res : Response) (key : String) : String :=
  match Headers.get key res.headers {
    Option.some v => v,
    Option.none => ""
  }

#[terminating]
def bytes_eq (a : List U8) (b : List U8) : Bool :=
  match a {
    List.empty => List.is_empty b,
    List.cons x xs =>
      match b {
        List.empty => false,
        List.cons y ys => if U8.beq x y then bytes_eq xs ys else false
      }
  }

#[test]
def test_mime_types : Bool :=
  Bool.and (String.beq (Static.mime_of "/app.js") "text/javascript; charset=utf-8")
    (Bool.and (String.beq (Static.mime_of "/app.wasm") "application/wasm")
      (Bool.and (String.beq (Static.mime_of "/style.css") "text/css; charset=utf-8")
        (String.beq (Static.mime_of "/blob.unknownext") "application/octet-stream")))

#[test]
def test_static_binary_byte_exact : IO Bool := do {
  let name := String.concat "moon_static_bin_" (String.concat (I64.to_string process_id) ".wasm");
  let path := String.concat "/tmp/" name;
  let bytes : List U8 := [0u8, 1u8, 0u8, 255u8];
  let wrote <- IO.write_file_bytes (Path.path path) bytes;
  let served <- Static.handler (StaticConfig.default "/tmp") (get_path (String.concat "/" name));
  match served {
    Result.err _ => return false,
    Result.ok res =>
      return (Bool.and (Result.is_ok wrote)
        (Bool.and (U16.beq res.status Status.ok)
          (Bool.and (bytes_eq (Body.to_bytes_pure res.body) bytes)
            (String.beq (header res "Content-Type") "application/wasm"))))
  }
}

#[test]
def test_traversal_raw_rejected : Bool :=
  match Static.safe_path "/tmp" "/../etc/passwd" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_traversal_encoded_rejected : Bool :=
  match Static.safe_path "/tmp" "/%2e%2e/etc/passwd" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_traversal_nul_rejected : Bool :=
  match Static.safe_path "/tmp" "/%00bad" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_etag_then_304 : Bool :=
  let req := get_path "/app.js" in
  let res := Static.respond (StaticConfig.default "/tmp") "/app.js" req (String.to_list "hello") in
  let etag := header res "ETag" in
  let cached := get_with "/app.js" (Headers.set "If-None-Match" etag Headers.empty) in
  let res2 := Static.respond (StaticConfig.default "/tmp") "/app.js" cached (String.to_list "hello") in
  Bool.and (U16.beq res.status Status.ok)
    (Bool.and (U16.beq res2.status Status.not_modified) (Bool.not (String.is_empty etag)))

#[test]
def test_range_206 : Bool :=
  let req := get_with "/app.js" (Headers.set "Range" "bytes=0-4" Headers.empty) in
  let res := Static.respond (StaticConfig.default "/tmp") "/app.js" req (String.to_list "hello world") in
  Bool.and (U16.beq res.status Status.partial_content)
    (Bool.and (String.beq (String.from_list (Body.to_bytes_pure res.body)) "hello")
      (String.beq (header res "Content-Range") "bytes 0-4/11"))

#[test]
def test_range_unsatisfiable_416 : Bool :=
  let req := get_with "/app.js" (Headers.set "Range" "bytes=99-100" Headers.empty) in
  let res := Static.respond (StaticConfig.default "/tmp") "/app.js" req (String.to_list "hello world") in
  Bool.and (U16.beq res.status Status.range_not_satisfiable)
    (String.beq (header res "Content-Range") "bytes */11")

#[test]
def test_missing_file_is_404 : IO Bool := do {
  let name := String.concat "moon_static_missing_" (String.concat (I64.to_string process_id) ".txt");
  let served <- Static.handler (StaticConfig.default "/tmp") (get_path (String.concat "/" name));
  match served {
    Result.err _ => return false,
    Result.ok res => return (U16.beq res.status Status.not_found)
  }
}

// ── path guard: an encoded/doubled leading slash ───────────────────────
//
// Decoding `/%2F...` used to yield `//...`, whose one-slash strip produced an
// absolute path that `Path.join` then honoured, escaping the root.

#[test]
def test_traversal_encoded_leading_slash_rejected : Bool :=
  match Static.safe_path "/tmp" "/%2Fetc/passwd" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_traversal_doubled_leading_slash_rejected : Bool :=
  match Static.safe_path "/tmp" "//etc/passwd" {
    Result.err _ => true,
    Result.ok _ => false
  }

#[test]
def test_safe_path_normal_still_joins : Bool :=
  match Static.safe_path "/tmp" "/app.js" {
    Result.ok p => String.beq p "/tmp/app.js",
    Result.err _ => false
  }

// ── If-None-Match forms ────────────────────────────────────────────────

#[test]
def test_etag_star_matches : Bool :=
  Bool.and (Static.etag_matches "*" "\"abc\"")
    (Bool.and (Static.etag_matches "W/\"abc\"" "\"abc\"")
      (Bool.and (Static.etag_matches "\"x\", \"abc\"" "\"abc\"")
        (Bool.not (Static.etag_matches "\"other\"" "\"abc\""))))

#[test]
def test_etag_star_gives_304 : Bool :=
  let req := get_with "/app.js" (Headers.set "If-None-Match" "*" Headers.empty) in
  let res := Static.respond (StaticConfig.default "/tmp") "/app.js" req (String.to_list "hello") in
  U16.beq res.status Status.not_modified

// ── immutable cache policy uses the URL path, not the file path ────────

#[test]
def test_immutable_prefix_cache_control : Bool :=
  let base := StaticConfig.default "/tmp" in
  let cfg : StaticConfig := { base with immutable_prefix := "/assets/" } in
  let req := get_path "/assets/app.js" in
  let res := Static.respond cfg "/tmp/assets/app.js" req (String.to_list "hello") in
  String.beq (header res "Cache-Control") "max-age=31536000, immutable"

// ── multipart ranges are ignored, not 416 ──────────────────────────────

#[test]
def test_multi_range_is_ignored : Bool :=
  match Static.range (Option.some "bytes=0-1,4-5") 11i64 {
    Result.ok r =>
      match r {
        Option.none => true,
        Option.some _ => false
      },
    Result.err _ => false
  }
