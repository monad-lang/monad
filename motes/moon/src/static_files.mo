/// Static file serving — byte-exact, typed, and traversal-safe.
///
/// `Server.static` used to read through the text-only `IO.read_file`, so a
/// `.wasm` truncated at its first NUL and no `Content-Type` was set. This
/// module is the replacement: `IO.read_file_bytes` (no decoding), a MIME
/// table, an `ETag`, `If-None-Match` → 304, and a single `Range` → 206.
///
/// The path guard decodes first, then rejects `..` segments, control bytes,
/// backslashes and a leading slash before joining under the root. Symlink
/// escape is out of reach without a `realpath` native; serve a symlink-free
/// tree (documented limitation).

use std::io {IO.is_dir, IO.read_file_bytes}
use std::list {List.length}
use std::path {Path, Path.join, Path.of, Path.to_string}
use std::sha256 {Sha256.hash_bytes}
use std::stream {StreamError.is_not_found}
use http::types {
  Body, Headers, Headers.empty, Headers.get, Headers.set, Method, Request,
  Response, Status.internal_server_error, Status.method_not_allowed,
  Status.not_found, Status.not_modified, Status.ok, Status.partial_content,
  Status.range_not_satisfiable, Uri, http1_1,
}
use http::strings {
  Strings.drop_bytes, Strings.parse_i64, Strings.split_at_byte, Strings.split_on,
}
use http::body {Body.from_bytes}
use http::uri {Uri.percent_decode}
use http::wire {Wire.take_bytes}

pub struct StaticConfig {
  root : String,
  index : String,
  cache_control : String,
  immutable_prefix : String
}

pub def StaticConfig.default (root : String) : StaticConfig :=
  let cfg : StaticConfig :=
    { root := root, index := "index.html", cache_control := "", immutable_prefix := "/assets/" } in
  cfg

// ── path safety ─────────────────────────────────────────────────────────

/// Decode the URL path and map it under `root`. Rejects parent segments,
/// control bytes, backslashes, and an encoded absolute path. A bare `/`
/// maps to the root itself (then the index fallback applies).
pub def Static.safe_path (root : String) (url_path : String) : Result String String :=
  if Static.unsafe url_path
  then Result.err "unsafe path"
  else
    match Uri.percent_decode url_path {
      Result.err e => Result.err (String.concat "bad path encoding: " e),
      Result.ok decoded =>
        if Static.unsafe decoded
        then Result.err "unsafe path"
        else Static.join_under root (Static.strip_leading_slash decoded)
    }

def Static.join_under (root : String) (relative : String) : Result String String :=
  match Path.of root {
    Result.err e => Result.err e,
    Result.ok base =>
      if String.is_empty relative
      then Result.ok (Path.to_string base)
      else
        match Path.of relative {
          Result.err e => Result.err e,
          Result.ok rel => Result.ok (Path.to_string (Path.join base rel))
        }
  }

def Static.unsafe (path : String) : Bool :=
  Bool.or
    (Static.has_nul_escape (String.to_list path))
    (Bool.or
      (Static.has_parent_segment (Strings.split_on "/" path))
      (Static.has_bad_byte (String.to_list path)))

/// A raw `%00` escape, checked BEFORE decoding: `String.from_list` stops at a
/// NUL, so a decoded NUL would silently truncate the path the guard inspects.
#[terminating]
def Static.has_nul_escape (bytes : List U8) : Bool :=
  match bytes {
    List.empty => false,
    List.cons a rest =>
      match rest {
        List.empty => false,
        List.cons b rest2 =>
          match rest2 {
            List.empty => false,
            List.cons c rest3 =>
              if Bool.and (U8.beq a 37u8) (Bool.and (U8.beq b 48u8) (U8.beq c 48u8))
              then true
              else Static.has_nul_escape (List.cons b (List.cons c rest3))
          }
      }
  }

#[terminating]
def Static.has_parent_segment (segments : List String) : Bool :=
  match segments {
    List.empty => false,
    List.cons seg rest =>
      if String.beq seg ".." then true else Static.has_parent_segment rest
  }

#[terminating]
def Static.has_bad_byte (bytes : List U8) : Bool :=
  match bytes {
    List.empty => false,
    List.cons b rest =>
      if U8.lt b 32u8 then true
      else if U8.beq b 92u8 then true
      else if U8.beq b 127u8 then true
      else Static.has_bad_byte rest
  }

def Static.strip_leading_slash (s : String) : String :=
  if String.starts_with "/" s
  then String.slice s 1 (I64.sub (String.length s) 1)
  else s

// ── MIME ────────────────────────────────────────────────────────────────

/// An association list, not the `Map` class: the dispatch is a handful of
/// suffix comparisons next to a file read, and `Map`'s instance resolution
/// is unreliable in this compiler. Extend the table as assets appear.
def Static.mime_table : List (Pair String String) := [
  Pair.pair ".html" "text/html; charset=utf-8",
  Pair.pair ".htm" "text/html; charset=utf-8",
  Pair.pair ".css" "text/css; charset=utf-8",
  Pair.pair ".js" "text/javascript; charset=utf-8",
  Pair.pair ".mjs" "text/javascript; charset=utf-8",
  Pair.pair ".json" "application/json",
  Pair.pair ".map" "application/json",
  Pair.pair ".wasm" "application/wasm",
  Pair.pair ".svg" "image/svg+xml",
  Pair.pair ".png" "image/png",
  Pair.pair ".jpg" "image/jpeg",
  Pair.pair ".jpeg" "image/jpeg",
  Pair.pair ".gif" "image/gif",
  Pair.pair ".webp" "image/webp",
  Pair.pair ".ico" "image/x-icon",
  Pair.pair ".txt" "text/plain; charset=utf-8",
  Pair.pair ".md" "text/markdown; charset=utf-8",
  Pair.pair ".csv" "text/csv; charset=utf-8",
  Pair.pair ".xml" "application/xml",
  Pair.pair ".pdf" "application/pdf",
  Pair.pair ".woff2" "font/woff2",
  Pair.pair ".woff" "font/woff",
  Pair.pair ".ttf" "font/ttf",
  Pair.pair ".mp4" "video/mp4",
  Pair.pair ".webm" "video/webm",
  Pair.pair ".mp3" "audio/mpeg",
  Pair.pair ".zip" "application/zip",
  Pair.pair ".gz" "application/gzip"
]

/// The content type for `path`, by lowercased extension; unknown files are
/// `application/octet-stream`.
pub def Static.mime_of (path : String) : String :=
  Static.mime_lookup (String.to_lowercase path) Static.mime_table

#[terminating]
def Static.mime_lookup (path : String) (table : List (Pair String String)) : String :=
  match table {
    List.empty => "application/octet-stream",
    List.cons head rest =>
      match head {
        Pair.pair ext media =>
          if String.ends_with path ext then media else Static.mime_lookup path rest
      }
  }

// ── ETag and ranges ─────────────────────────────────────────────────────

/// A strong ETag over the bytes, quoted for the header.
pub def Static.etag (bytes : List U8) : String :=
  String.concat "\"" (String.concat (Static.hex_of_bytes (Sha256.hash_bytes bytes)) "\"")

#[terminating]
def Static.hex_of_bytes (bytes : List U8) : String :=
  String.from_list (Static.hex_digits bytes)

#[terminating]
def Static.hex_digits (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons b rest =>
      let hi := U8.div b 16u8 in
      let lo := U8.sub b (U8.mul hi 16u8) in
      List.append
        (List.cons (Static.hex_char hi) (List.cons (Static.hex_char lo) List.empty))
        (Static.hex_digits rest)
  }

def Static.hex_char (n : U8) : U8 :=
  if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 87u8

/// Parse a single `Range: bytes=...` header. `Ok none` means "no usable
/// range" (serve the whole file); `Err` means the range is unsatisfiable.
pub def Static.range (header : Option String) (len : I64) : Result String (Option (Pair I64 I64)) :=
  match header {
    Option.none => Result.ok Option.none,
    Option.some h =>
      if String.starts_with "bytes=" h
      then Static.parse_range (String.slice h 6 (I64.sub (String.length h) 6)) len
      else Result.ok Option.none
  }

def Static.parse_range (spec : String) (len : I64) : Result String (Option (Pair I64 I64)) :=
  match Strings.split_at_byte 45u8 (String.to_list spec) {
    Pair.pair start_b end_b =>
      let start_s := String.from_list start_b in
      let end_s := String.from_list end_b in
      if String.is_empty start_s
      then Static.suffix_range end_s len
      else Static.bounded_range start_s end_s len
  }

def Static.suffix_range (end_s : String) (len : I64) : Result String (Option (Pair I64 I64)) :=
  if I64.lt len 1
  then Result.err "empty file has no ranges"
  else
    match Strings.parse_i64 end_s {
      Option.none => Result.err "bad range",
      Option.some n =>
        if I64.lt n 1
        then Result.err "bad range"
        else
          let start := if I64.lt len n then 0 else I64.sub len n in
          Result.ok (Option.some (Pair.pair start (I64.sub len 1)))
    }

def Static.bounded_range (start_s : String) (end_s : String) (len : I64) : Result String (Option (Pair I64 I64)) :=
  match Strings.parse_i64 start_s {
    Option.none => Result.err "bad range start",
    Option.some start =>
      if I64.lt start 0 then Result.err "bad range start"
      else if Bool.not (I64.lt start len) then Result.err "range start past end"
      else if String.is_empty end_s
      then Result.ok (Option.some (Pair.pair start (I64.sub len 1)))
      else
        match Strings.parse_i64 end_s {
          Option.none => Result.err "bad range end",
          Option.some end =>
            if I64.lt end start then Result.err "range end before start"
            else
              let capped := if I64.lt end len then end else I64.sub len 1 in
              Result.ok (Option.some (Pair.pair start capped))
        }
  }

def Static.slice (start : I64) (end : I64) (bytes : List U8) : List U8 :=
  let count := I64.add (I64.sub end start) 1 in
  Wire.take_bytes count (Strings.drop_bytes start bytes)

// ── responses ───────────────────────────────────────────────────────────

def Static.method_not_allowed : Response :=
  { status := Status.method_not_allowed, headers := Headers.set "Allow" "GET, HEAD" Headers.empty, version := HttpVersion.http1_1, body := Body.text "Method Not Allowed" }

def Static.not_found : Response :=
  { status := Status.not_found, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Not Found" }

def Static.internal_error : Response :=
  { status := Status.internal_server_error, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Internal Server Error" }

def Static.response_headers (cfg : StaticConfig) (path : String) (etag : String) : Headers :=
  let h1 := Headers.set "Content-Type" (Static.mime_of path) Headers.empty in
  let h2 := Headers.set "ETag" etag h1 in
  let h3 := Headers.set "Accept-Ranges" "bytes" h2 in
  let cc :=
    if String.starts_with cfg.immutable_prefix path
    then "max-age=31536000, immutable"
    else cfg.cache_control in
  if String.is_empty cc then h3 else Headers.set "Cache-Control" cc h3

/// Build the response for an existing file. `If-None-Match` wins over a
/// range; an unsatisfiable range is 416 with `Content-Range: bytes */len`.
pub def Static.respond (cfg : StaticConfig) (path : String) (req : Request) (bytes : List U8) : Response :=
  let etag := Static.etag bytes in
  let len := List.length bytes in
  let headers := Static.response_headers cfg path etag in
  match Headers.get "if-none-match" req.headers {
    Option.some inm =>
      if String.beq inm etag
      then Static.not_modified_response etag
      else Static.body_response headers req len bytes,
    Option.none => Static.body_response headers req len bytes
  }

def Static.not_modified_response (etag : String) : Response :=
  { status := Status.not_modified, headers := Headers.set "ETag" etag Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

def Static.body_response (headers : Headers) (req : Request) (len : I64) (bytes : List U8) : Response :=
  match Static.range (Headers.get "range" req.headers) len {
    Result.err _ => Static.range_not_satisfiable_response headers len,
    Result.ok range_opt =>
      match range_opt {
        Option.none => Static.ok_response headers bytes,
        Option.some pr =>
          match pr {
            Pair.pair start end => Static.partial_response headers start end len bytes
          }
      }
  }

def Static.range_not_satisfiable_response (headers : Headers) (len : I64) : Response :=
  { status := Status.range_not_satisfiable, headers := Headers.set "Content-Range" (String.concat "bytes */" (I64.to_string len)) headers, version := HttpVersion.http1_1, body := Body.empty }

def Static.ok_response (headers : Headers) (bytes : List U8) : Response :=
  { status := Status.ok, headers := headers, version := HttpVersion.http1_1, body := Body.from_bytes bytes }

def Static.partial_response (headers : Headers) (start : I64) (end : I64) (len : I64) (bytes : List U8) : Response :=
  let part := Static.slice start end bytes in
  let cr := String.concat "bytes " (String.concat (I64.to_string start) (String.concat "-" (String.concat (I64.to_string end) (String.concat "/" (I64.to_string len))))) in
  { status := Status.partial_content, headers := Headers.set "Content-Range" cr headers, version := HttpVersion.http1_1, body := Body.from_bytes part }

/// The handler. A missing file (or an unsafe path) is 404; an existing file
/// with a directory path falls back to `cfg.index`.
pub def Static.handler (cfg : StaticConfig) (req : Request) : IO (Result String Response) :=
  if Bool.not (Bool.or (BEq.beq req.method Method.GET) (BEq.beq req.method Method.HEAD))
  then IO.pure (Result.ok Static.method_not_allowed)
  else Static.handler_get cfg req

def Static.handler_get (cfg : StaticConfig) (req : Request) : IO (Result String Response) :=
  match Static.safe_path cfg.root req.uri.path {
    Result.err _ => IO.pure (Result.ok Static.not_found),
    Result.ok full =>
      match Path.of full {
        Result.err _ => IO.pure (Result.ok Static.not_found),
        Result.ok p => Static.handler_path cfg req full p
      }
  }

def Static.handler_path (cfg : StaticConfig) (req : Request) (full : String) (p : Path) : IO (Result String Response) := do {
  let is_dir <- IO.is_dir p;
  let target := if is_dir then String.concat (String.concat full "/") cfg.index else full;
  let read <- Static.read_target target;
  match read {
    Result.err _ => return (Result.ok Static.internal_error),
    Result.ok found =>
      match found {
        Option.none => return (Result.ok Static.not_found),
        Option.some bytes => return (Result.ok (Static.respond cfg target req bytes))
      }
  }
}

/// Read a target path, distinguishing "not found" from a real error.
def Static.read_target (target : String) : IO (Result String (Option (List U8))) :=
  match Path.of target {
    Result.err _ => IO.pure (Result.ok Option.none),
    Result.ok p => do {
      let r <- IO.read_file_bytes p;
      match r {
        Result.ok bytes => IO.pure (Result.ok (Option.some bytes)),
        Result.err e => if StreamError.is_not_found e then IO.pure (Result.ok Option.none) else IO.pure (Result.err e.message)
      }
    }
  }
