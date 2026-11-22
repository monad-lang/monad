/// The WebSocket client: an HTTP upgrade over `Client.transport`, then the
/// shared session from `http::websocket_io`.
///
/// `ws://` is plain TCP and `wss://` is the verified TLS transport `moose`
/// already builds, so the same call speaks either. The key and the per-frame
/// masks are drawn from a clock-seeded counter: RFC 6455 requires them to be
/// unpredictable enough that a cache cannot be poisoned by a chosen key, not
/// to be a secret, and a caller that wants its own source uses
/// `MooseWs.connect_with_key`.
///
/// After `MooseWs.connect` the session is a `http::websocket_io` `WsConn`
/// used exactly like the server's: `Ws.send`/`Ws.recv`, or `Ws.recv_timeout`
/// when one fiber must also write (which a `wss` connection requires, since
/// one `SSL*` must not be read and written concurrently).

use http::types {
    Body, Headers, Headers.empty, Headers.set, HttpVersion, Method, Request, Transport, Uri,
    Transport.read_bytes, Transport.write_bytes,
}
use http::uri {Uri.parse}
use http::wire {Wire.find_body_start, Wire.format_request, Wire.parse_response, Wire.take_bytes}
use http::strings {Strings.drop_bytes}
use http::websocket {Ws.client_headers, Ws.check_accept}
use http::websocket_io {WsConfig, WsConn, WsRole, Ws.start}
use std::base64 {B64.encode_std}
use std::io {IO.current_time}
use lib::client {Client.transport}

/// A 16-byte key as base64, expanded from `seed` (xorshift64, the same
/// mixing the session uses for masks).
pub def MooseWs.key_from (seed : I64) : String :=
    let s := MooseWs.mix (I64.add seed 0x9e37i64) in
    B64.encode_std (MooseWs.key_bytes s)

def MooseWs.mix (x : I64) : I64 :=
    let a := I64.xor x (I64.shl x 13i64) in
    let b := I64.xor a (I64.shr a 7i64) in
    I64.xor b (I64.shl b 17i64)

/// The key's bytes: 16 bytes from two mixed words.
def MooseWs.key_bytes (s : I64) : List U8 :=
    let a := s in
    let b := MooseWs.mix s in
    List.append (MooseWs.word_bytes a) (MooseWs.word_bytes b)

def MooseWs.word_bytes (w : I64) : List U8 :=
    [MooseWs.byte_of (I64.shr w 56i64), MooseWs.byte_of (I64.shr w 48i64),
        MooseWs.byte_of (I64.shr w 40i64), MooseWs.byte_of (I64.shr w 32i64),
        MooseWs.byte_of (I64.shr w 24i64), MooseWs.byte_of (I64.shr w 16i64),
        MooseWs.byte_of (I64.shr w 8i64), MooseWs.byte_of w]

def MooseWs.byte_of (x : I64) : U8 :=
    U32.to_u8 (I64.to_u32 (I64.and x 255i64))

/// The origin-form target of `url` (path plus query, `/` when empty).
def MooseWs.target (path : String) (query : String) : String :=
    let p := if String.beq path "" then "/" else path in
    if String.beq query "" then p else String.concat p (String.concat "?" query)

/// Connect and complete the upgrade: `ok conn` is a live client session.
pub def MooseWs.connect (url : String) (protocols : List String) (headers : Headers)
    (cfg : WsConfig) : IO (Result String WsConn) := do {
    let now <- IO.current_time;
    MooseWs.connect_with_key (MooseWs.key_from now) url protocols headers cfg
}

/// `MooseWs.connect` with an explicit `Sec-WebSocket-Key` (16 bytes,
/// base64).
pub def MooseWs.connect_with_key (key : String) (url : String) (protocols : List String)
    (headers : Headers) (cfg : WsConfig) : IO (Result String WsConn) := do {
    match Uri.parse url {
        Result.err e => IO.pure (Result.err e),
        Result.ok u => MooseWs.connect_uri key u protocols headers cfg
    }
}

def MooseWs.host_header (u : Uri) : Headers :=
    Headers.set "Host" u.host Headers.empty

def MooseWs.request (u : Uri) (key : String) (protocols : List String) (headers : Headers) : Request :=
    let hs := Ws.client_headers key protocols (MooseWs.merge_headers (MooseWs.host_header u) headers) in
    let req : Request := { method := Method.GET, uri := u, headers := hs, version := HttpVersion.http1_1,
        body := Body.empty } in
    req

/// `base`'s headers, overridden by `extra`.
#[terminating]
def MooseWs.merge_headers (base : Headers) (extra : Headers) : Headers :=
    match extra {
        Headers.headers pairs =>
            match pairs {
                List.empty => base,
                List.cons p rest =>
                    match p {
                        Pair.pair k v => MooseWs.merge_headers (Headers.set k v base) (Headers.headers rest)
                    }
            }
    }

def MooseWs.connect_uri (key : String) (u : Uri) (protocols : List String) (headers : Headers)
    (cfg : WsConfig) : IO (Result String WsConn) := do {
    let url := MooseWs.url_of u;
    let opened <- Client.transport url cfg.max_message cfg.poll_ms;
    match opened {
        Result.err e => IO.pure (Result.err e),
        Result.ok t => MooseWs.write_and_read key u protocols headers cfg t
    }
}

def MooseWs.write_and_read (key : String) (u : Uri) (protocols : List String)
    (headers : Headers) (cfg : WsConfig) (t : Transport) : IO (Result String WsConn) := do {
    let req := MooseWs.request u key protocols headers;
    match Wire.format_request req {
        Result.err e => IO.pure (Result.err e),
        Result.ok bytes => do {
            let w <- Transport.write_bytes t bytes;
            match w {
                Result.err e => IO.pure (Result.err e),
                Result.ok _ => do {
                    let r <- MooseWs.read_response_head t List.empty;
                    match r {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok pr => MooseWs.finish_upgrade key protocols cfg t pr
                    }
                }
            }
        }
    }
}

def MooseWs.finish_upgrade (key : String) (protocols : List String) (cfg : WsConfig)
    (t : Transport) (pr : Pair (Pair U16 Headers) (List U8)) : IO (Result String WsConn) := do {
    match pr {
        Pair.pair head rest =>
            match head {
                Pair.pair status res_headers =>
                    match Ws.check_accept key (Shared.of protocols) status (Shared.of res_headers) {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok _ => do {
                            let started <- Ws.start cfg WsRole.client t rest;
                            match started {
                                Result.err _ => IO.pure (Result.err "websocket session failed to start"),
                                Result.ok conn => IO.pure (Result.ok conn)
                            }
                        }
                    }
            }
    }
}

/// The full URL to connect to, rebuilt from the parsed Uri (scheme,
/// authority, path and query; the fragment is dropped).
pub def MooseWs.url_of (u : Uri) : String :=
    match u {
        { scheme, host, port, path, query, .. } =>
            let authority :=
                match port {
                    Option.none => host,
                    Option.some p => String.concat host (String.concat ":" (U16.to_string p))
                } in
            let target := MooseWs.target path (match query { Option.none => "", Option.some q => q }) in
            String.concat scheme (String.concat "://" (String.concat authority target))
    }

#[terminating]
def MooseWs.read_response_head (t : Transport) (acc : List U8)
    : IO (Result String (Pair (Pair U16 Headers) (List U8))) := do {
    let r <- Transport.read_bytes t 4096i64;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok chunk => do {
            let all := List.append acc chunk;
            match Wire.find_body_start all {
                Option.none => MooseWs.read_response_head t all,
                Option.some end => do {
                    let head := Wire.take_bytes end all;
                    match Wire.parse_response head {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok res =>
                            let sh : Pair U16 Headers := Pair.pair res.status res.headers in
                            IO.pure (Result.ok (Pair.pair sh (Strings.drop_bytes end all)))
                    }
                }
            }
        }
    }
}
