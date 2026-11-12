/// Static file serving — byte-exact, typed, and traversal-safe.
///
/// `Server.static` used to read through the text-only `IO.read_file`, so a
/// `.wasm` truncated at its first NUL and no `Content-Type` was set. This
/// module is the replacement: `IO.read_file_bytes` (no decoding), a MIME
/// table, an `ETag`, `If-None-Match` → 304, and a single `Range` → 206.
///
/// The body is STREAMED (`Body.stream`, 64 KiB pulls): the file is never
/// materialized whole to be served. The ETag is the one remaining
/// whole-file read, and an `EtagCache` pays it once per file version
/// (keyed by path and size) instead of on every request — a 304 re-reads
/// nothing. A same-size rewrite is indistinguishable without an mtime
/// native; the size changing (the common edit) re-keys. The full fix —
/// hashing without materializing — needs an incremental SHA-256 in std.
///
/// A consumer that abandons a streamed body mid-transfer leaks the
/// descriptor: `Body.stream` has no close hook (the same reason SSE has no
/// disconnect notification). EOF and read errors close eagerly.
///
/// The path guard decodes first, then rejects `..` segments, control bytes,
/// backslashes and a leading slash before joining under the root. Symlink
/// escape is out of reach without a `realpath` native; serve a symlink-free
/// tree (documented limitation).

use std::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.length, ByteBuf.to_list}
use std::io {IO.file_size, IO.is_dir, IO.read_file_bytes}
use std::list {}
use std::path {Path, Path.is_absolute, Path.join, Path.of, Path.to_string}
use std::ref {Ref, Ref.get, Ref.new, Ref.set}
use std::sha256 {Sha256.hash_bytes}
use std::stream {
    FdStream, FdStream.open_file, FdStream.read_mode, FdStream.seek,
    FdStream.seek_start, Stream,
}
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
/// control bytes, backslashes, an encoded absolute path, and a path that
/// still begins with `/` after the request's one leading slash is removed
/// (`/%2Fetc/passwd` decodes to `//etc/passwd`). A bare `/` maps to the root
/// itself (then the index fallback applies).
pub def Static.safe_path (root : String) (url_path : String) : Result String String :=
    if Static.unsafe url_path
    then Result.err "unsafe path"
    else
        match Uri.percent_decode url_path {
            Result.err e => Result.err (String.concat "bad path encoding: " e),
            Result.ok decoded =>
                if Static.unsafe decoded
                then Result.err "unsafe path"
                else
                    match Static.relative_after_slash decoded {
                        Result.err e => Result.err e,
                        Result.ok relative => Static.join_under root relative
                    }
        }

/// Drop the URL's one leading slash, then refuse a remaining leading slash.
/// Without the second check, `Path.join`'s absolute-second-operand rule turns
/// the result into an arbitrary absolute path.
pub def Static.relative_after_slash (decoded : String) : Result String String :=
    if String.starts_with "/" decoded
    then
        let rest := String.slice decoded 1 (I64.sub (String.length decoded) 1) in
        if String.starts_with "/" rest
        then Result.err "absolute path"
        else Result.ok rest
    else Result.ok decoded

def Static.join_under (root : String) (relative : String) : Result String String :=
    match Path.of root {
        Result.err e => Result.err (PathError.to_string e),
        Result.ok base =>
            if String.is_empty relative
            then Result.ok (Path.to_string base)
            else
                match Path.of relative {
                    Result.err e => Result.err (PathError.to_string e),
                    Result.ok rel =>
                        if Path.is_absolute rel
                        then Result.err "absolute path"
                        else Result.ok (Path.to_string (Path.join base rel))
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

// ── the ETag cache ──────────────────────────────────────────────────────
//
// Keyed by path AND size: the first request for a version of a file pays
// the one whole-file read the hash needs, and every later request — a
// repeat, and above all a 304 — reuses it without touching the file. The
// cache is one entry per served file version, so it grows with the asset
// tree, not with traffic.

/// A store of `path:size` → ETag, created once per server
/// (`Static.new_cache`) and passed to `Static.handler_with`.
pub struct EtagCache {
    entries : Ref (List (Pair String String))
}

/// The empty store. One per server, not per request: the whole point is
/// that a second request for the same file version finds its ETag here.
pub def Static.new_cache : IO EtagCache := do {
    let entries : Ref (List (Pair String String)) <- Ref.new List.empty;
    let c : EtagCache := { entries := entries };
    return c
}

/// How many versions the store holds (test surface: a 304 must not add one).
pub def Static.cache_count (cache : EtagCache) : IO I64 := do {
    let entries <- Ref.get cache.entries;
    return (List.length entries)
}

#[terminating]
def Static.cache_lookup (key : String) (entries : List (Pair String String)) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                Pair.pair k v =>
                    if String.beq k key then Option.some v else Static.cache_lookup key rest
            }
    }

/// The ETag for the file at `p` (served as `path`), `size` bytes, hashed
/// once per version: a cache miss reads the file and stores the result;
/// a hit — the second request, and every 304 — answers without reading.
/// A read failure answers a constant and caches nothing (the GET below
/// reports it as a 500 anyway).
pub def Static.etag_of (cache : EtagCache) (path : String) (p : Path) (size : I64) : IO String := do {
    let key := String.concat path (String.concat ":" (I64.to_string size));
    let entries <- Ref.get cache.entries;
    match Static.cache_lookup key entries {
        Option.some etag => return etag,
        Option.none => do {
            let read <- IO.read_file_bytes p;
            match read {
                Result.err _ => return Static.unreadable_etag,
                Result.ok bytes => do {
                    let etag := Static.etag bytes;
                    let _ <- Ref.set cache.entries (List.cons (Pair.pair key etag) entries);
                    return etag
                }
            }
        }
    }
}

def Static.unreadable_etag : String := "\"unreadable\""

/// Parse a single `Range: bytes=...` header. `Ok none` means "no usable
/// range" (serve the whole file); `Err` means the range is unsatisfiable.
pub def Static.range (header : Option String) (len : I64) : Result String (Option (Pair I64 I64)) :=
    match header {
        Option.none => Result.ok Option.none,
        Option.some h =>
            if String.starts_with "bytes=" h
            then Static.single_range (String.slice h 6 (I64.sub (String.length h) 6)) len
            else Result.ok Option.none
    }

/// A multipart range (`bytes=0-1,4-5`) is not implemented; RFC 9110 lets a
/// server ignore `Range` and serve the whole representation, which is right.
/// Answering 416 would claim none of the ranges is satisfiable.
def Static.single_range (spec : String) (len : I64) : Result String (Option (Pair I64 I64)) :=
    if Static.multi_range spec
    then Result.ok Option.none
    else Static.parse_range spec len

#[terminating]
def Static.multi_range (spec : String) : Bool :=
    match Strings.split_on "," spec {
        List.empty => false,
        List.cons _ rest =>
            match rest {
                List.empty => false,
                List.cons _ _ => true
            }
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
        if String.starts_with cfg.immutable_prefix (Static.url_path_of cfg.root path)
        then "max-age=31536000, immutable"
        else cfg.cache_control in
    if String.is_empty cc then h3 else Headers.set "Cache-Control" cc h3

/// A URL-shaped path for a resolved file, so a URL prefix such as
/// `/assets/` can be compared against it. `path` is `<root>/assets/x.js`,
/// which does not start with the prefix itself.
pub def Static.url_path_of (root : String) (path : String) : String :=
    let base :=
        if String.ends_with root "/"
        then root
        else String.concat root "/" in
    if String.starts_with base path
    then String.concat "/" (String.slice path (String.length base) (I64.sub (String.length path) (String.length base)))
    else path

/// Whether an `If-None-Match` value names `etag`. Handles `*`, a
/// comma-separated list, and the weak `W/` prefix (the weak comparison is
/// what a GET uses, RFC 9110 §13.1.2).
pub def Static.etag_matches (header : String) (etag : String) : Bool :=
    let trimmed := String.trim header in
    if String.beq trimmed "*"
    then true
    else Static.etag_in_list (Strings.split_on "," trimmed) etag

#[terminating]
def Static.etag_in_list (candidates : List String) (etag : String) : Bool :=
    match candidates {
        List.empty => false,
        List.cons c rest =>
            let t := String.trim c in
            let strong :=
                if String.starts_with "W/" t
                then String.trim (String.slice t 2 (I64.sub (String.length t) 2))
                else t in
            if String.beq strong etag then true else Static.etag_in_list rest etag
    }

/// Build the response for an existing file. `If-None-Match` wins over a
/// range; an unsatisfiable range is 416 with `Content-Range: bytes */len`.
pub def Static.respond (cfg : StaticConfig) (path : String) (req : Request) (bytes : List U8) : Response :=
    let etag := Static.etag bytes in
    let len := List.length bytes in
    let headers := Static.response_headers cfg path etag in
    match Headers.get "if-none-match" req.headers {
        Option.some inm =>
            if Static.etag_matches inm etag
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
/// with a directory path falls back to `cfg.index`. The body is streamed
/// (`Body.stream`, `Static.chunk_bytes` per pull), and the ETag comes from
/// `cache`, hashed once per file version.
pub def Static.handler (cfg : StaticConfig) (req : Request) : IO (Result String Response) := do {
    let cache <- Static.new_cache;
    Static.handler_with cfg cache req
}

/// `Static.handler` with a caller-owned ETag store: create one with
/// `Static.new_cache` per server and share it across requests, so a file
/// is hashed once per version rather than once per request.
pub def Static.handler_with (cfg : StaticConfig) (cache : EtagCache) (req : Request) : IO (Result String Response) :=
    if Bool.not (Bool.or (BEq.beq req.method Method.GET) (BEq.beq req.method Method.HEAD))
    then IO.pure (Result.ok Static.method_not_allowed)
    else Static.handler_get cfg cache req

def Static.handler_get (cfg : StaticConfig) (cache : EtagCache) (req : Request) : IO (Result String Response) :=
    match Static.safe_path cfg.root req.uri.path {
        Result.err _ => IO.pure (Result.ok Static.not_found),
        Result.ok full =>
            match Path.of full {
                Result.err _ => IO.pure (Result.ok Static.not_found),
                Result.ok p => Static.handler_path cfg cache req full p
            }
    }

def Static.handler_path (cfg : StaticConfig) (cache : EtagCache) (req : Request) (full : String) (p : Path) : IO (Result String Response) := do {
    let is_dir <- IO.is_dir p;
    let target := if is_dir then String.concat (String.concat full "/") cfg.index else full;
    match Path.of target {
        Result.err _ => return (Result.ok Static.not_found),
        Result.ok tp => do {
            let found <- Static.stat_target tp;
            match found {
                Option.none => return (Result.ok Static.not_found),
                Option.some size =>
                    match Static.range_of req size {
                        Result.err _ => return (Result.ok (Static.range_not_satisfiable_response (Static.response_headers_of cfg target "") size)),
                        Result.ok ro => Static.handler_stat cfg cache req target tp size ro
                    }
            }
        }
    }
}

/// The range the request asks of a `size`-byte file: `Ok none` serves the
/// whole file.
def Static.range_of (req : Request) (size : I64) : Result String (Option (Pair I64 I64)) :=
    Static.range (Headers.get "range" req.headers) size

def Static.handler_stat (cfg : StaticConfig) (cache : EtagCache) (req : Request)
    (target : String) (tp : Path) (size : I64) (ro : Option (Pair I64 I64)) : IO (Result String Response) := do {
    let etag <- Static.etag_of cache target tp size;
    let headers := Static.response_headers cfg target etag;
    match Headers.get "if-none-match" req.headers {
        Option.some inm =>
            if Static.etag_matches inm etag
            then IO.pure (Result.ok (Static.not_modified_response etag))
            else Static.handler_body cfg req target tp size ro headers,
        Option.none => Static.handler_body cfg req target tp size ro headers
    }
}

/// Open the file for a GET (a HEAD answers the head without opening
/// anything: nothing pulls its body, so an eager open would leak the
/// descriptor), then build the streamed response.
def Static.handler_body (cfg : StaticConfig) (req : Request) (target : String) (tp : Path)
    (size : I64) (ro : Option (Pair I64 I64)) (headers : Headers) : IO (Result String Response) := do {
    if BEq.beq req.method Method.HEAD
    then IO.pure (Result.ok (Static.head_response headers size ro))
    else do {
        let opened <- FdStream.open_file tp FdStream.read_mode;
        match opened {
            Result.err _ => return (Result.ok Static.internal_error),
            Result.ok file => do {
                let res <- Static.stream_response headers file size ro;
                return (Result.ok res)
            }
        }
    }
}

/// The response head for a HEAD: the representation's `Content-Length`
/// (the range's, when a range is served), and no body to stream.
def Static.head_response (headers : Headers) (size : I64) (ro : Option (Pair I64 I64)) : Response :=
    match ro {
        Option.none => Static.head_full headers size,
        Option.some pr =>
            match pr {
                Pair.pair start end =>
                    let len := I64.add (I64.sub end start) 1 in
                    let cr := Static.content_range start end size in
                    // A 206's `Content-Length` is the range's length: the
                    // head writer takes it from here because a HEAD has no
                    // body to measure.
                    let h2 := Headers.set "Content-Range" cr headers in
                    { status := Status.partial_content,
                        headers := Headers.set "Content-Length" (I64.to_string len) h2,
                        version := HttpVersion.http1_1, body := Body.empty }
            }
    }

def Static.head_full (headers : Headers) (size : I64) : Response :=
    { status := Status.ok,
        headers := Headers.set "Content-Length" (I64.to_string size) headers,
        version := HttpVersion.http1_1, body := Body.empty }

/// The streamed GET response: `Body.stream` pulls `Static.chunk_bytes` at
/// a time, seeking to the range start when one is served. The body owns
/// the descriptor: EOF, a read error and (on a range) the last byte close
/// it, and a consumer that abandons the transfer leaks it — `Body.stream`
/// has no close hook.
///
/// A range's seek happens HERE, before the response exists, so its failure
/// is reported once instead of hiding in the body (where it would look like
/// an empty 206).
def Static.stream_response (headers : Headers) (file : FdStream) (size : I64) (ro : Option (Pair I64 I64)) : IO Response :=
    match ro {
        Option.none => IO.pure (Static.stream_full headers file),
        Option.some pr =>
            match pr {
                Pair.pair start end => do {
                    let pulls <- Static.range_pulls file start end;
                    IO.pure (Static.stream_range headers pulls start end size)
                }
            }
    }

def Static.stream_full (headers : Headers) (file : FdStream) : Response :=
    { status := Status.ok, headers := headers, version := HttpVersion.http1_1,
        body := Body.stream (Static.file_pulls file Option.none) }

/// The ranged 206: the `Content-Range`, and a body pulling through `end`
/// from the already-seeked descriptor.
def Static.stream_range (headers : Headers) (pulls : Unit -> IO (Option (List U8)))
    (start : I64) (end : I64) (size : I64) : Response :=
    let cr := Static.content_range start end size in
    { status := Status.partial_content, headers := Headers.set "Content-Range" cr headers,
        version := HttpVersion.http1_1, body := Body.stream pulls }

/// Pulls from `file` until the transfer is done, closing it at EOF, on a
/// read error, or on `bound`'s last byte.
///
/// `bound` is the absolute last byte index to send, inclusive, or
/// `Option.none` for "to EOF". It is an option rather than a numeric
/// sentinel because BYTE 0 IS A LEGAL RANGE END: `Range: bytes=0-0` asks
/// for exactly one byte, and a `bound < 1` "unbounded" test would send none.
///
/// The descriptor's own offset is the cursor (a read advances it, so a seek
/// of 0 from here reports where the chunk ended), which is why a ranged
/// stream seeks ONCE, in `Static.range_pulls`: re-seeking per pull would
/// re-read the same chunk forever. Closing on the last byte is part of the
/// same invariant -- a transfer that ended without closing leaves the offset
/// where it was, and the next pull repeats the bytes.
def Static.file_pulls (file : FdStream) (bound : Option I64) : Unit -> IO (Option (List U8)) :=
    fn (_ : Unit) => do {
        let read <- Stream.read file Static.chunk_bytes;
        match read {
            Result.err _ => do {
                let _ <- Stream.close file;
                return Option.none
            },
            Result.ok buf => do {
                let n := ByteBuf.length buf;
                if I64.beq n 0
                then do {
                    let _ <- ByteBuf.free buf;
                    let _ <- Stream.close file;
                    return Option.none
                }
                else do {
                    let bytes <- ByteBuf.to_list buf n;
                    let _ <- ByteBuf.free buf;
                    match bound {
                        Option.none => return (Option.some bytes),
                        Option.some last => do {
                            let sought <- FdStream.seek file 0i64 FdStream.seek_current;
                            match sought {
                                Result.err _ => do {
                                    let _ <- Stream.close file;
                                    return Option.none
                                },
                                Result.ok pos =>
                                    if I64.gt pos last
                                    then do {
                                        // The read crossed (or exactly
                                        // reached) the bound: keep the bytes
                                        // through `last` -- the chunk covers
                                        // pos-n .. pos-1, so the count is
                                        // last - pos + n + 1 -- and close.
                                        let _ <- Stream.close file;
                                        let want := I64.add (I64.add (I64.sub last pos) n) 1i64;
                                        return (Option.some (Wire.take_bytes want bytes))
                                    }
                                    else return (Option.some bytes)
                            }
                        }
                    }
                }
            }
        }
    }

/// Seek to the range start ONCE, then pull through `end`.
///
/// The seek is outside the closure deliberately: the file only stays at the
/// offset its last read left, so a seek per pull resets it to `start` and a
/// range longer than one `Static.chunk_bytes` chunk (`bytes=0-1048575` on a
/// 1 MiB asset) re-reads its first chunk until the consumer gives up. The
/// seek already happened by the time the response is built, so the handler
/// waits for it once instead of leaving a failed seek inside the body.
pub def Static.range_pulls (file : FdStream) (start : I64) (end : I64) : IO (Unit -> IO (Option (List U8))) := do {
    let sought <- FdStream.seek file start FdStream.seek_start;
    match sought {
        Result.err _ => do {
            let _ <- Stream.close file;
            IO.pure (fn (_ : Unit) => IO.pure Option.none)
        },
        Result.ok _ => IO.pure (Static.file_pulls file (Option.some end))
    }
}

/// One pull's read size: 64 KiB, the page-friendly middle between an fd
/// round trip per byte and another whole file in memory.
pub def Static.chunk_bytes : I64 := 65536

def Static.content_range (start : I64) (end : I64) (size : I64) : String :=
    String.concat "bytes " (String.concat (I64.to_string start) (String.concat "-" (String.concat (I64.to_string end) (String.concat "/" (I64.to_string size)))))

/// The response headers with `Content-Type`, `ETag`, `Accept-Ranges` and
/// the cache policy, for callers that already have an ETag.
pub def Static.response_headers_of (cfg : StaticConfig) (path : String) (etag : String) : Headers :=
    Static.response_headers cfg path etag

/// The size of the file at `p`, or `none` when it does not exist (the
/// directory case is resolved before this is called).
def Static.stat_target (p : Path) : IO (Option I64) :=
    IO.file_size p
