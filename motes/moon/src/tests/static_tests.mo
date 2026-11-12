/// Static-file tests: MIME, byte exactness, traversal, ETag and ranges.
///
/// These exercise the pure response builder directly (no sockets), plus one
/// real file read for the binary case. Fixtures live under `/tmp` with
/// process-scoped names so parallel worktrees do not collide.

use std::io {IO.write_file_bytes}
use std::path {Path}
use std::process {process_id}
use http::body {Body.to_bytes_pure}
use http::body_io {Body.to_bytes}
use http::types {
    Body, Headers, Headers.empty, Headers.get, Headers.set, Method, Request,
    Response, Status.not_found, Status.not_modified, Status.ok,
    Status.partial_content, Status.range_not_satisfiable, Uri, http1_1,
}
use moon::static_files {
    Static.cache_count, Static.chunk_bytes, Static.etag_matches, Static.handler,
    Static.handler_with, Static.mime_of, Static.new_cache, Static.range,
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
        Result.ok res => do {
            // The served body is a stream now: drain it, then compare.
            let drained <- Body.to_bytes res.body;
            match drained {
                Result.err _ => return false,
                Result.ok got =>
                    return (Bool.and (Result.is_ok wrote)
                        (Bool.and (U16.beq res.status Status.ok)
                            (Bool.and (bytes_eq got bytes)
                                (String.beq (header res "Content-Type") "application/wasm"))))
            }
        }
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

// ── streaming: the body is a pull, never a materialized file ────────────

/// A served file arrives as `Body.stream` in `Static.chunk_bytes` pulls;
/// draining it must give back the file's exact bytes.
#[test]
def test_streamed_body_is_byte_exact : IO Bool := do {
    let name := String.concat "moon_static_stream_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let bytes : List U8 := [0u8, 1u8, 0u8, 255u8, 7u8, 9u8];
    let _ <- IO.write_file_bytes (Path.path path) bytes;
    let cache <- Static.new_cache;
    let served <- Static.handler_with (StaticConfig.default "/tmp") cache (get_path (String.concat "/" name));
    match served {
        Result.err _ => return false,
        Result.ok res => do {
            let drained <- Body.to_bytes res.body;
            match drained {
                Result.err _ => return false,
                Result.ok got => return (bytes_eq got bytes)
            }
        }
    }
}

/// A file larger than one pull (`Static.chunk_bytes` = 64 KiB) crosses a
/// chunk boundary: the second pull must carry the rest, and the drained
/// bytes must still be the whole file.
#[test]
def test_streamed_body_multi_chunk : IO Bool := do {
    let name := String.concat "moon_static_big_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    // 66 KiB: one full pull plus a 2 KiB tail.
    let bytes := String.to_list (String.repeat "ab" 33792);
    let _ <- IO.write_file_bytes (Path.path path) bytes;
    let cache <- Static.new_cache;
    let served <- Static.handler_with (StaticConfig.default "/tmp") cache (get_path (String.concat "/" name));
    match served {
        Result.err _ => return false,
        Result.ok res => do {
            let drained <- Body.to_bytes res.body;
            match drained {
                Result.err _ => return false,
                Result.ok got => return (Bool.and (I64.beq (List.length got) 67584i64) (bytes_eq got bytes))
            }
        }
    }
}

/// The ETag store hashes once per file version: a first request pays the
/// read, a second request and a 304 answer from the SAME store, and the
/// store still holds one entry.
#[test]
def test_etag_cached_304_no_rehash : IO Bool := do {
    let name := String.concat "moon_static_cache_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let _ <- IO.write_file_bytes (Path.path path) (String.to_list "hello");
    let cache <- Static.new_cache;
    let cfg := StaticConfig.default "/tmp";
    let first <- Static.handler_with cfg cache (get_path (String.concat "/" name));
    let count1 <- Static.cache_count cache;
    match first {
        Result.err _ => return false,
        Result.ok res1 => do {
            let etag := header res1 "ETag";
            let cached := get_with (String.concat "/" name) (Headers.set "If-None-Match" etag Headers.empty);
            let second <- Static.handler_with cfg cache cached;
            let count2 <- Static.cache_count cache;
            match second {
                Result.err _ => return false,
                Result.ok res2 =>
                    return (Bool.and (U16.beq res2.status Status.not_modified)
                        (Bool.and (I64.beq count1 1i64) (I64.beq count2 1i64)))
            }
        }
    }
}

/// A ranged request streams the slice: seek to the start, pull through the
/// end, and close at the last byte. The drained body is the range's bytes.
#[test]
def test_streamed_range_206 : IO Bool := do {
    let name := String.concat "moon_static_range_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let _ <- IO.write_file_bytes (Path.path path) (String.to_list "hello world");
    let cache <- Static.new_cache;
    let req := get_with (String.concat "/" name) (Headers.set "Range" "bytes=0-4" Headers.empty);
    let served <- Static.handler_with (StaticConfig.default "/tmp") cache req;
    match served {
        Result.err _ => return false,
        Result.ok res => do {
            let drained <- Body.to_bytes res.body;
            match drained {
                Result.err _ => return false,
                Result.ok got =>
                    return (Bool.and (U16.beq res.status Status.partial_content)
                        (Bool.and (String.beq (String.from_list got) "hello")
                            (String.beq (header res "Content-Range") "bytes 0-4/11")))
            }
        }
    }
}

// ── the streamed range over more than one pull ─────────────────────────
//
// `Static.range_pulls` used to re-seek to the range start on EVERY pull, so
// a range longer than one `Static.chunk_bytes` chunk re-read the same bytes
// until the consumer gave up (the drain hung; a socket peer saw a repeated
// prefix). The fixtures below are padded just past a chunk boundary so the
// transfer needs a second pull.

/// `n` bytes of `a, b, c, ...` repeating, so a slice can be located by
/// content (a repeated block would hide a re-read).
#[terminating]
def pattern (n : I64) (b : U8) (acc : List U8) : List U8 :=
    if I64.lt n 1i64
    then List.reverse acc
    else pattern (I64.sub n 1i64) (if U8.beq b 122u8 then 97u8 else U8.add b 1u8) (List.cons b acc)

/// The first `count` bytes of the pattern, for comparison.
def expect (count : I64) : List U8 := pattern count 97u8 List.empty

/// A file of `Static.chunk_bytes + 64` bytes, so a range covering all of it
/// needs two pulls.
def write_two_chunk_file (path : String) : IO Bool := do {
    let n := I64.add Static.chunk_bytes 64i64;
    let written <- IO.write_file_bytes (Path.path path) (pattern n 97u8 List.empty);
    match written {
        Result.err _ => IO.pure false,
        Result.ok _ => IO.pure true
    }
}

/// The whole file as a range: two pulls, and the bytes must be the file's
/// own once -- not the first chunk repeated.
#[test]
def test_streamed_range_spans_two_chunks : IO Bool := do {
    let name := String.concat "moon_static_range_two_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let wrote <- write_two_chunk_file path;
    if Bool.not wrote
    then IO.pure false
    else do {
        let cache <- Static.new_cache;
        let n := I64.add Static.chunk_bytes 64i64;
        let spec := String.concat "bytes=0-" (I64.to_string (I64.sub n 1i64));
        let req := get_with (String.concat "/" name) (Headers.set "Range" spec Headers.empty);
        let served <- Static.handler_with (StaticConfig.default "/tmp") cache req;
        match served {
            Result.err _ => IO.pure false,
            Result.ok res => do {
                let drained <- Body.to_bytes res.body;
                match drained {
                    Result.err _ => IO.pure false,
                    Result.ok got =>
                        IO.pure (Bool.and (U16.beq res.status Status.partial_content)
                            (bytes_eq got (expect n)))
                }
            }
        }
    }
}

/// A range that STARTS inside the first chunk and ends past it: the second
/// pull must continue from where the first stopped, not restart.
#[test]
def test_streamed_range_crosses_boundary_offset : IO Bool := do {
    let name := String.concat "moon_static_range_off_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let wrote <- write_two_chunk_file path;
    if Bool.not wrote
    then IO.pure false
    else do {
        let cache <- Static.new_cache;
        let n := I64.add Static.chunk_bytes 64i64;
        let start := I64.sub Static.chunk_bytes 16i64;
        let count := 32i64;
        let spec := String.concat "bytes=" (String.concat (I64.to_string start)
            (String.concat "-" (I64.to_string (I64.sub (I64.add start count) 1i64))));
        let req := get_with (String.concat "/" name) (Headers.set "Range" spec Headers.empty);
        let served <- Static.handler_with (StaticConfig.default "/tmp") cache req;
        match served {
            Result.err _ => IO.pure false,
            Result.ok res => do {
                let drained <- Body.to_bytes res.body;
                match drained {
                    Result.err _ => IO.pure false,
                    Result.ok got =>
                        IO.pure (Bool.and (U16.beq res.status Status.partial_content)
                            (bytes_eq got (expect count)))
                }
            }
        }
    }
}

/// `bytes=0-0` is a legal one-byte range, and byte 0 is the one end index a
/// numeric "unbounded" sentinel would swallow (the body came back EMPTY).
#[test]
def test_streamed_range_single_byte_zero : IO Bool := do {
    let name := String.concat "moon_static_range_zero_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let _ <- IO.write_file_bytes (Path.path path) (pattern 4i64 97u8 List.empty);
    let cache <- Static.new_cache;
    let req := get_with (String.concat "/" name) (Headers.set "Range" "bytes=0-0" Headers.empty);
    let served <- Static.handler_with (StaticConfig.default "/tmp") cache req;
    match served {
        Result.err _ => IO.pure false,
        Result.ok res => do {
            let drained <- Body.to_bytes res.body;
            match drained {
                Result.err _ => IO.pure false,
                Result.ok got =>
                    IO.pure (Bool.and (U16.beq res.status Status.partial_content)
                        (bytes_eq got (expect 1i64)))
            }
        }
    }
}

/// A HEAD naming a range is the 206 head: the range's `Content-Length`, no
/// body, and the fd is never opened (nothing would pull it).
#[test]
def test_head_range_reports_range_length : IO Bool := do {
    let name := String.concat "moon_static_head_range_" (I64.to_string process_id);
    let path := String.concat "/tmp/" name;
    let _ <- IO.write_file_bytes (Path.path path) (pattern 10i64 97u8 List.empty);
    let cache <- Static.new_cache;
    let req : Request := { method := Method.HEAD, uri := Uri.uri "" Option.none "" Option.none (String.concat "/" name) Option.none Option.none,
        headers := Headers.set "Range" "bytes=2-5" Headers.empty, version := HttpVersion.http1_1, body := Body.empty };
    let served <- Static.handler_with (StaticConfig.default "/tmp") cache req;
    match served {
        Result.err _ => IO.pure false,
        Result.ok res =>
            IO.pure (Bool.and (U16.beq res.status Status.partial_content)
                (Bool.and (String.beq (header res "Content-Length") "4")
                    (String.beq (header res "Content-Range") "bytes 2-5/10")))
    }
}
