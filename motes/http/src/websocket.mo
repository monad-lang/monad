/// WebSocket (RFC 6455) — Layer 0, pure Monad.
///
/// The opening handshake (both halves) and the frame codec: bytes go in,
/// complete messages and control frames come out, in the `Sse.push` shape.
/// The session over a `Transport` (pings, the close handshake, locking) is
/// `http::websocket_io`; `moon` and `moose` add the server upgrade and the
/// client connect on top.
///
/// The decoder enforces the protocol rules that make a peer's frames
/// unambiguous, and answers a violation with the close frame RFC 6455 §7.4
/// names for it:
///
/// - reserved bits set, an unknown opcode, a client frame without a mask or a
///   server frame with one, a fragmented or over-125-byte control frame, a
///   continuation with no message open or a new message while one is open,
///   a malformed close payload: 1002 (protocol error);
/// - a text message (or close reason) that is not UTF-8: 1007;
/// - a message whose total payload exceeds `max_message`: 1009, decided from
///   the frame header, before its payload is buffered.
///
/// No extension is negotiated (a server that answers with one is refused),
/// so the reserved bits are never legitimately set.
///
/// Buffering is linear: pushed chunks are kept reversed with a running
/// length and flattened only once the bytes a header said it needs are all
/// there, so a large frame arriving in many reads is not re-copied per read.

use init::copy {Copy}
use std::base64 {B64.encode_std}
use std::sha1 {Sha1.hash_bytes}
use http::strings {Strings.base64_decode, Strings.drop_bytes, Strings.split_on}
use http::types {
    Body, Headers, Headers.empty, Headers.set, HttpVersion, Method, Response,
    Status.upgrade_required, Status.switching_protocols,
}

// ── message and close values ────────────────────────────────────────────

/// One complete WebSocket message (fragments already joined).
pub type WsMessage {
    text (s : String),
    binary (bytes : List U8)
}

/// A close frame's status code and reason.
pub struct WsClose { code : I64, reason : String }

/// What one decoded unit of the wire is: a whole data message or a control
/// frame. Pings and pongs carry their application data.
pub type WsInbound {
    message (m : WsMessage),
    ping (payload : List U8),
    pong (payload : List U8),
    close (c : WsClose)
}

/// 1000 — normal closure.
pub def Ws.close_normal : I64 := 1000
/// 1001 — the endpoint is going away (server shutdown, page navigation).
pub def Ws.close_going_away : I64 := 1001
/// 1002 — the peer broke the protocol.
pub def Ws.close_protocol_error : I64 := 1002
/// 1003 — a data type the endpoint does not accept.
pub def Ws.close_unsupported : I64 := 1003
/// 1005 — no status code was present (never sent on the wire).
pub def Ws.close_no_status : I64 := 1005
/// 1006 — the connection dropped without a close frame (never sent).
pub def Ws.close_abnormal : I64 := 1006
/// 1007 — a text payload that is not UTF-8.
pub def Ws.close_invalid_data : I64 := 1007
/// 1008 — a policy violation (generic refusal).
pub def Ws.close_policy : I64 := 1008
/// 1009 — a message too big to process.
pub def Ws.close_too_big : I64 := 1009
/// 1011 — the server hit an unexpected condition.
pub def Ws.close_internal_error : I64 := 1011

/// A `WsClose` value.
pub def WsClose.of (code : I64) (reason : String) : WsClose :=
    let c : WsClose := { code := code, reason := reason } in
    c

// ── handshake ───────────────────────────────────────────────────────────

/// The RFC 6455 §1.3 GUID appended to the client's key.
pub def Ws.guid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/// `Sec-WebSocket-Accept` for a client's `Sec-WebSocket-Key`:
/// base64(SHA-1(key ++ GUID)).
pub def Ws.accept_key (key : String) : String :=
    B64.encode_std (Sha1.hash_bytes (String.to_list (String.concat key Ws.guid)))

/// An upgrade request the server can accept: the client's key and the
/// subprotocols it offered, in its order of preference.
pub struct WsOffer { key : String, protocols : List String }

/// The handshake headers, read once: every value of each, joined with
/// `,` (so a split header still parses as one list). All `String`, so the
/// view is `Copy` and the checks below may read it freely.
pub struct WsHeaders {
    upgrade : String,
    connection : String,
    version : String,
    key : String,
    protocol : String,
    accept : String,
    extensions : String
}

pub instance Copy WsHeaders {
    def copy (h : WsHeaders) : Pair WsHeaders WsHeaders := Pair.pair h h
}

/// Read the handshake headers out of a shared header list.
pub def WsHeaders.of (h : Shared Headers) : WsHeaders :=
    match Shared.get h {
        Headers.headers pairs =>
            let ps := Shared.of pairs in
            let v : WsHeaders :=
                { upgrade := Ws.joined "upgrade" ps, connection := Ws.joined "connection" ps,
                    version := Ws.joined "sec-websocket-version" ps, key := Ws.joined "sec-websocket-key" ps,
                    protocol := Ws.joined "sec-websocket-protocol" ps,
                    accept := Ws.joined "sec-websocket-accept" ps,
                    extensions := Ws.joined "sec-websocket-extensions" ps } in
            v
    }

/// Every value stored under the lowercase `name`, joined with `,`, in
/// stored order (keys are lowercased on insert).
#[terminating]
def Ws.joined (name : String) (pairs : Shared (List (Pair String String))) : String :=
    match Shared.get pairs {
        List.empty => "",
        List.cons p rest =>
            let tail := Ws.joined name (Shared.of rest) in
            match p {
                Pair.pair k v =>
                    if Bool.not (String.beq k name) then tail
                    else if String.beq tail "" then String.concat v ""
                    else String.concat v (String.concat "," tail)
            }
    }

/// The comma-separated, trimmed, non-empty elements of a header value.
pub def Ws.header_list (value : String) : List String :=
    Ws.trimmed_parts (Strings.split_on "," value)

#[terminating]
def Ws.trimmed_parts (parts : List String) : List String :=
    match parts {
        List.empty => List.empty,
        List.cons p rest =>
            let t := String.trim p in
            if String.beq t "" then Ws.trimmed_parts rest else List.cons t (Ws.trimmed_parts rest)
    }

/// Whether a comma-separated header value holds `token`, case-insensitively
/// (`Connection: keep-alive, Upgrade`).
pub def Ws.has_token (value : String) (token : String) : Bool :=
    Ws.any_token (Strings.split_on "," value) token

#[terminating]
def Ws.any_token (parts : List String) (token : String) : Bool :=
    match parts {
        List.empty => false,
        List.cons p rest =>
            Bool.or (String.beq (String.to_lowercase (String.trim p)) token) (Ws.any_token rest token)
    }

def Ws.is_get (m : Method) : Bool :=
    match m {
        Method.GET => true,
        _ => false
    }

/// A refusal response with a plain-text reason.
def Ws.refusal (status : U16) (extra : Headers) (reason : String) : Response :=
    let r : Response :=
        { status := status, headers := Headers.set "Content-Type" "text/plain; charset=utf-8" extra,
            version := HttpVersion.http1_1, body := Body.text reason } in
    r

/// The 426 a server answers a non-WebSocket request on a WebSocket route
/// with; it names the one version this implementation speaks.
pub def Ws.upgrade_required (reason : String) : Response :=
    Ws.refusal Status.upgrade_required
        (Headers.set "Upgrade" "websocket" (Headers.set "Sec-WebSocket-Version" "13" Headers.empty))
        reason

/// Validate a server-side upgrade request (RFC 6455 §4.2.1). The error is
/// the response to send instead: 426 when the request is not a version-13
/// WebSocket upgrade, 400 when it is one but malformed, 405 for a method
/// other than GET.
///
/// The request's HTTP version is not checked (it is not a parameter): an
/// `HTTP/1.0` request that carries the upgrade headers is accepted, which
/// the RFC does not allow but which no browser sends.
pub def Ws.check_upgrade (method : Method) (headers : Shared Headers) : Result Response WsOffer :=
    let h := WsHeaders.of headers in
    let key := String.trim h.key in
    if Bool.not (Ws.is_get method)
    then Result.err (Ws.refusal 405u16 (Headers.set "Allow" "GET" Headers.empty) "WebSocket upgrade must be GET")
    else if Bool.not (Ws.has_token h.upgrade "websocket")
    then Result.err (Ws.upgrade_required "expected Upgrade: websocket")
    else if Bool.not (Ws.has_token h.connection "upgrade")
    then Result.err (Ws.upgrade_required "expected Connection: Upgrade")
    else if Bool.not (String.trim h.version == "13")
    then Result.err (Ws.upgrade_required "unsupported Sec-WebSocket-Version (want 13)")
    else if String.beq key ""
    then Result.err (Ws.refusal 400u16 Headers.empty "missing Sec-WebSocket-Key")
    else if Bool.not (Ws.key_valid key)
    then Result.err (Ws.refusal 400u16 Headers.empty "Sec-WebSocket-Key must be 16 base64-encoded bytes")
    else
        let offer : WsOffer := { key := key, protocols := Ws.header_list h.protocol } in
        Result.ok offer

/// A key is the base64 encoding of exactly 16 bytes (24 characters).
pub def Ws.key_valid (key : String) : Bool :=
    match Strings.base64_decode key {
        Result.ok bytes => Bool.and (List.length bytes == 16) (String.length key == 24),
        Result.err _ => false
    }

/// The server's choice among the client's offered subprotocols: the first
/// of `supported` (server preference order) that the client offered.
#[terminating]
pub def Ws.select_protocol (offered : Shared (List String)) (supported : List String) : Option String :=
    match supported {
        List.empty => Option.none,
        List.cons s rest =>
            if Ws.contains offered s then Option.some s else Ws.select_protocol offered rest
    }

#[terminating]
def Ws.contains (xs : Shared (List String)) (x : String) : Bool :=
    match Shared.get xs {
        List.empty => false,
        List.cons y rest => Bool.or (String.beq x y) (Ws.contains (Shared.of rest) x)
    }

/// The 101 that accepts `key`, naming the selected subprotocol if any.
pub def Ws.accept_response (key : String) (protocol : Option String) : Response :=
    let base :=
        Headers.set "Sec-WebSocket-Accept" (Ws.accept_key key)
            (Headers.set "Connection" "Upgrade" (Headers.set "Upgrade" "websocket" Headers.empty)) in
    let hs :=
        match protocol {
            Option.none => base,
            Option.some p => Headers.set "Sec-WebSocket-Protocol" p base
        } in
    let r : Response :=
        { status := Status.switching_protocols, headers := hs, version := HttpVersion.http1_1,
            body := Body.empty } in
    r

/// The headers a client adds to its GET to ask for an upgrade with `key`
/// (16 random bytes, base64) and the subprotocols it offers.
pub def Ws.client_headers (key : String) (protocols : List String) (h : Headers) : Headers :=
    let base :=
        Headers.set "Sec-WebSocket-Version" "13"
            (Headers.set "Sec-WebSocket-Key" key
                (Headers.set "Connection" "Upgrade" (Headers.set "Upgrade" "websocket" h))) in
    match Ws.join_comma protocols {
        Option.none => base,
        Option.some joined => Headers.set "Sec-WebSocket-Protocol" joined base
    }

/// `a, b, c`; `none` for an empty list.
#[terminating]
def Ws.join_comma (xs : List String) : Option String :=
    match xs {
        List.empty => Option.none,
        List.cons x rest =>
            match Ws.join_comma rest {
                Option.none => Option.some x,
                Option.some tail => Option.some (String.concat x (String.concat ", " tail))
            }
    }

/// Validate the server's answer to a client upgrade (RFC 6455 §4.1): a
/// 101 with the right `Upgrade`, `Connection` and `Sec-WebSocket-Accept`,
/// no extension, and a subprotocol that is one the client offered (or
/// none). The success value is the selected subprotocol.
pub def Ws.check_accept (key : String) (offered : Shared (List String)) (status : U16) (headers : Shared Headers)
    : Result String (Option String) :=
    let h := WsHeaders.of headers in
    if Bool.not (U16.beq status Status.switching_protocols)
    then Result.err (String.concat "server answered " (String.concat (U16.to_string status) " instead of 101"))
    else if Bool.not (Ws.has_token h.upgrade "websocket")
    then Result.err "101 without Upgrade: websocket"
    else if Bool.not (Ws.has_token h.connection "upgrade")
    then Result.err "101 without Connection: Upgrade"
    else if Bool.not (String.trim h.accept == Ws.accept_key key)
    then Result.err "Sec-WebSocket-Accept does not match the key"
    else if Bool.not (List.is_empty (Ws.header_list h.extensions))
    then Result.err "server selected an extension the client did not offer"
    else Ws.check_selected offered (Ws.header_list h.protocol)

def Ws.check_selected (offered : Shared (List String)) (selected : List String) : Result String (Option String) :=
    match selected {
        List.empty => Result.ok Option.none,
        List.cons p rest =>
            if Bool.and (List.is_empty rest) (Ws.contains offered p)
            then Result.ok (Option.some p)
            else Result.err "server selected a subprotocol the client did not offer"
    }

// ── byte helpers ────────────────────────────────────────────────────────

def Ws.byte (n : I64) : U8 := U32.to_u8 (I64.to_u32 (I64.and n 255))

def Ws.bits (b : U8) (m : I64) : I64 := I64.and (U8.to_i64 b) m

def Ws.xor (a : U8) (b : U8) : U8 := U32.to_u8 (U32.xor (U8.to_u32 a) (U8.to_u32 b))

/// `n` as `width` big-endian bytes.
#[terminating]
def Ws.be_bytes (n : I64) (width : I64) (acc : List U8) : List U8 :=
    if Bool.not (I64.gt width 0) then acc
    else Ws.be_bytes (I64.shr n 8) (width - 1) (List.cons (Ws.byte n) acc)

/// Big-endian bytes as an unsigned value (at most 8 bytes; the caller
/// rejects a set top bit before calling).
#[terminating]
def Ws.be_value (bytes : List U8) (acc : I64) : I64 :=
    match bytes {
        List.empty => acc,
        List.cons b rest => Ws.be_value rest (I64.or (I64.shl acc 8) (U8.to_i64 b))
    }

/// Split after `n` bytes (tail-recursive: payloads can be large).
#[terminating]
def Ws.split_at (n : I64) (xs : List U8) (acc : List U8) : Pair (List U8) (List U8) :=
    if Bool.not (I64.gt n 0) then Pair.pair (List.reverse acc) xs
    else match xs {
        List.empty => Pair.pair (List.reverse acc) List.empty,
        List.cons x rest => Ws.split_at (n - 1) rest (List.cons x acc)
    }

/// A frame's 4-byte masking key (RFC 6455 §5.3). A client draws a fresh
/// one per frame; four bytes, so duplicating it is free.
pub struct WsMask { k0 : U8, k1 : U8, k2 : U8, k3 : U8 }

pub instance Copy WsMask {
    def copy (m : WsMask) : Pair WsMask WsMask := Pair.pair m m
}

/// The mask from its wire bytes (missing bytes are zero; extra ignored).
pub def WsMask.of_bytes (bytes : List U8) : WsMask :=
    match Ws.split_at 4 bytes List.empty {
        Pair.pair head _ => Ws.mask_bytes head 0u8 0u8 0u8 0u8
    }

#[terminating]
def Ws.mask_bytes (bytes : List U8) (k0 : U8) (k1 : U8) (k2 : U8) (k3 : U8) : WsMask :=
    match bytes {
        List.empty =>
            let m : WsMask := { k0 := k0, k1 := k1, k2 := k2, k3 := k3 } in
            m,
        List.cons x rest => Ws.mask_bytes rest k1 k2 k3 x
    }

/// The mask's wire bytes.
pub def WsMask.to_bytes (m : WsMask) : List U8 := [m.k0, m.k1, m.k2, m.k3]

def WsMask.at (m : WsMask) (i : I64) : U8 :=
    if i == 0 then m.k0 else if i == 1 then m.k1 else if i == 2 then m.k2 else m.k3

/// XOR `payload` with the mask, cycling. Masking and unmasking are the
/// same operation.
pub def Ws.apply_mask (m : WsMask) (payload : List U8) : List U8 :=
    Ws.mask_go m 0 payload List.empty

#[terminating]
def Ws.mask_go (m : WsMask) (i : I64) (payload : List U8) (acc : List U8) : List U8 :=
    match payload {
        List.empty => List.reverse acc,
        List.cons p rest => Ws.mask_go m (I64.and (I64.add i 1) 3) rest (List.cons (Ws.xor p (WsMask.at m i)) acc)
    }

/// The number of bytes behind a shared list.
#[terminating]
def Ws.count (xs : Shared (List U8)) (n : I64) : I64 :=
    match Shared.get xs {
        List.empty => n,
        List.cons _ rest => Ws.count (Shared.of rest) (I64.add n 1)
    }

/// Concatenate chunks given most-recent-first, tail-recursively.
#[terminating]
def Ws.join_rev (chunks : List (List U8)) (acc : List U8) : List U8 :=
    match chunks {
        List.empty => acc,
        List.cons c rest => Ws.join_rev rest (Ws.prepend_rev (List.reverse c) acc)
    }

/// `reverse rc ++ acc` without non-tail recursion.
#[terminating]
def Ws.prepend_rev (rc : List U8) (acc : List U8) : List U8 :=
    match rc {
        List.empty => acc,
        List.cons x rest => Ws.prepend_rev rest (List.cons x acc)
    }

// ── UTF-8 validation ────────────────────────────────────────────────────

/// Whether `bytes` is well-formed UTF-8 (no overlongs, no surrogates,
/// nothing above U+10FFFF) — RFC 3629 §4's table. Takes a shared list so a
/// caller can still use the bytes after asking.
pub def Ws.valid_utf8 (bytes : Shared (List U8)) : Bool :=
    Ws.utf8_go bytes

#[terminating]
def Ws.utf8_go (bytes : Shared (List U8)) : Bool :=
    match Shared.get bytes {
        List.empty => true,
        List.cons b rest =>
            let v := U8.to_i64 b in
            if I64.lt v 0x80 then Ws.utf8_go (Shared.of rest)
            else if I64.lt v 0xc2 then false
            else if I64.lt v 0xe0 then Ws.utf8_tail (Shared.of rest) 1 0x80 0xbf
            else if v == 0xe0 then Ws.utf8_tail (Shared.of rest) 2 0xa0 0xbf
            else if v == 0xed then Ws.utf8_tail (Shared.of rest) 2 0x80 0x9f
            else if I64.lt v 0xf0 then Ws.utf8_tail (Shared.of rest) 2 0x80 0xbf
            else if v == 0xf0 then Ws.utf8_tail (Shared.of rest) 3 0x90 0xbf
            else if I64.lt v 0xf4 then Ws.utf8_tail (Shared.of rest) 3 0x80 0xbf
            else if v == 0xf4 then Ws.utf8_tail (Shared.of rest) 3 0x80 0x8f
            else false
    }

/// `n` continuation bytes, the first in `[lo, hi]` and the rest in
/// `[0x80, 0xbf]`, then the rest of the input.
#[terminating]
def Ws.utf8_tail (bytes : Shared (List U8)) (n : I64) (lo : I64) (hi : I64) : Bool :=
    if Bool.not (I64.gt n 0) then Ws.utf8_go bytes
    else match Shared.get bytes {
        List.empty => false,
        List.cons b rest =>
            let v := U8.to_i64 b in
            if Bool.and (Bool.not (I64.lt v lo)) (Bool.not (I64.gt v hi))
            then Ws.utf8_tail (Shared.of rest) (n - 1) 0x80 0xbf
            else false
    }

// ── frames ──────────────────────────────────────────────────────────────

pub type WsOpcode {
    continuation,
    text,
    binary,
    close,
    ping,
    pong
}

/// A nullary enum; duplicating it copies a tag.
pub instance Copy WsOpcode {
    def copy (op : WsOpcode) : Pair WsOpcode WsOpcode := Pair.pair op op
}

pub def WsOpcode.code (op : WsOpcode) : I64 :=
    match op {
        WsOpcode.continuation => 0,
        WsOpcode.text => 1,
        WsOpcode.binary => 2,
        WsOpcode.close => 8,
        WsOpcode.ping => 9,
        WsOpcode.pong => 10
    }

pub def WsOpcode.of_code (c : I64) : Option WsOpcode :=
    if c == 0 then Option.some WsOpcode.continuation
    else if c == 1 then Option.some WsOpcode.text
    else if c == 2 then Option.some WsOpcode.binary
    else if c == 8 then Option.some WsOpcode.close
    else if c == 9 then Option.some WsOpcode.ping
    else if c == 10 then Option.some WsOpcode.pong
    else Option.none

/// One frame: the FIN bit, the opcode and the (unmasked) payload.
pub struct WsFrame { fin : Bool, opcode : WsOpcode, payload : List U8 }

/// The wire bytes of `f`. A client passes the frame's fresh mask; a
/// server passes `none`.
pub def Ws.encode_frame (mask : Option WsMask) (f : WsFrame) : List U8 :=
    match f {
        { fin, opcode, payload } =>
            let len := Ws.count (Shared.of payload) 0 in
            let b0 := Ws.byte (I64.or (if fin then 0x80 else 0) (WsOpcode.code opcode)) in
            match mask {
                Option.none => List.cons b0 (List.append (Ws.length_field 0 len) payload),
                Option.some m0 =>
                    let m : WsMask := m0 in
                    List.cons b0 (List.append (Ws.length_field 0x80 len)
                        (List.append (WsMask.to_bytes m) (Ws.apply_mask m payload)))
            }
    }

/// The second header byte (with the mask bit `mbit`) and any extended
/// length bytes.
def Ws.length_field (mbit : I64) (len : I64) : List U8 :=
    if I64.lt len 126 then [Ws.byte (I64.or mbit len)]
    else if I64.lt len 65536 then List.cons (Ws.byte (I64.or mbit 126)) (Ws.be_bytes len 2 List.empty)
    else List.cons (Ws.byte (I64.or mbit 127)) (Ws.be_bytes len 8 List.empty)

/// A whole data message as one unfragmented frame.
pub def Ws.message_frame (m : WsMessage) : WsFrame :=
    let f : WsFrame :=
        match m {
            WsMessage.text s => { fin := true, opcode := WsOpcode.text, payload := String.to_list s },
            WsMessage.binary b => { fin := true, opcode := WsOpcode.binary, payload := b }
        } in
    f

/// A control frame (ping, pong or close) carrying `payload` (≤125 bytes).
pub def Ws.control_frame (op : WsOpcode) (payload : List U8) : WsFrame :=
    let f : WsFrame := { fin := true, opcode := op, payload := payload } in
    f

/// A close frame's payload: the code as two big-endian bytes, then the
/// reason. 1005/1006/1015 are never sent; asking for one sends an empty
/// payload (which the peer reads as 1005). The reason is cut to fit the
/// 125-byte control limit.
pub def Ws.encode_close (c : WsClose) : List U8 :=
    match c {
        { code, reason } =>
            if Bool.or (code == 1005) (Bool.or (code == 1006) (code == 1015)) then List.empty
            else List.append (Ws.be_bytes code 2 List.empty)
                (Ws.utf8_prefix (String.to_list reason) 123)
    }

/// The longest prefix of at most `n` bytes that ends on a character
/// boundary (the input is a `String`'s UTF-8).
def Ws.utf8_prefix (bytes : List U8) (n : I64) : List U8 :=
    Ws.prefix_go bytes n List.empty

#[terminating]
def Ws.prefix_go (bytes : List U8) (room : I64) (acc : List U8) : List U8 :=
    match bytes {
        List.empty => List.reverse acc,
        List.cons b rest =>
            let w := Ws.char_width b in
            if I64.gt w room then List.reverse acc
            else Ws.take_char (w - 1) rest (room - w) (List.cons b acc)
    }

#[terminating]
def Ws.take_char (k : I64) (bytes : List U8) (room : I64) (acc : List U8) : List U8 :=
    if Bool.not (I64.gt k 0) then Ws.prefix_go bytes room acc
    else match bytes {
        List.empty => List.reverse acc,
        List.cons b rest => Ws.take_char (k - 1) rest room (List.cons b acc)
    }

/// A character's byte width from its lead byte.
def Ws.char_width (b : U8) : I64 :=
    let v := U8.to_i64 b in
    if I64.lt v 0xc0 then 1 else if I64.lt v 0xe0 then 2 else if I64.lt v 0xf0 then 3 else 4

/// Whether a code may appear in a received close frame (RFC 6455 §7.4).
pub def Ws.close_code_valid (code : I64) : Bool :=
    if I64.lt code 1000 then false
    else if Bool.not (I64.gt code 1003) then true
    else if I64.lt code 1007 then false
    else if Bool.not (I64.gt code 1014) then true
    else if I64.lt code 3000 then false
    else I64.lt code 5000

/// Decode a received close payload: empty is 1005; one byte, an invalid
/// code or a non-UTF-8 reason is the violation to answer with.
pub def Ws.decode_close (payload : List U8) : Result WsClose WsClose :=
    match payload {
        List.empty => Result.ok (WsClose.of Ws.close_no_status ""),
        List.cons b0 rest =>
            match rest {
                List.empty => Result.err (WsClose.of Ws.close_protocol_error "one-byte close payload"),
                List.cons b1 reason =>
                    let code := I64.or (I64.shl (U8.to_i64 b0) 8) (U8.to_i64 b1) in
                    if Bool.not (Ws.close_code_valid code)
                    then Result.err (WsClose.of Ws.close_protocol_error "invalid close code")
                    else if Bool.not (Ws.valid_utf8 (Shared.of reason))
                    then Result.err (WsClose.of Ws.close_invalid_data "close reason is not UTF-8")
                    else Result.ok (WsClose.of code (String.from_list reason))
            }
    }

// ── decoder ─────────────────────────────────────────────────────────────

/// The data message being reassembled from fragments: its opcode and its
/// payload chunks, most recent first.
pub struct WsFragments { op : WsOpcode, chunks : List (List U8) }

/// The incremental decoder's state.
///
/// - `chunks`/`len`: bytes received and not yet consumed, most recent
///   chunk first, and their total length;
/// - `need`: how many buffered bytes the next frame needs before parsing is
///   worth trying again (2 for a bare header; the full frame once its header
///   has been read);
/// - `frag`/`frag_len`: the fragmented data message in progress, if any,
///   and its payload length so far;
/// - `from_client`: the frames come from a client, so each must be masked
///   (a server's must not be);
/// - `max_message`: the largest message payload accepted.
pub struct WsDecoder {
    chunks : List (List U8) := List.empty,
    len : I64 := 0,
    need : I64 := 2,
    frag : Option WsFragments := Option.none,
    frag_len : I64 := 0,
    from_client : Bool,
    max_message : I64
}

/// A decoder for frames sent by a client (`from_client = true`, used by a
/// server) or by a server (`false`, used by a client).
pub def WsDecoder.new (from_client : Bool) (max_message : I64) : WsDecoder :=
    let d : WsDecoder := { from_client := from_client, max_message := max_message } in
    d

/// The decoder's fixed settings, which every step reads.
struct WsRules { from_client : Bool, max_message : I64 }

pub instance Copy WsRules {
    def copy (r : WsRules) : Pair WsRules WsRules := Pair.pair r r
}

/// The reassembly state after a frame, and the unit the frame completed.
struct WsFolded { frag : Option WsFragments, frag_len : I64, emitted : Option WsInbound }

/// Feed `bytes` in: the new state and every unit the push completed, in
/// wire order, or the close the peer's violation calls for (the session
/// sends it and drops the connection).
pub def Ws.push (d : WsDecoder) (bytes : List U8) : Result WsClose (Pair WsDecoder (List WsInbound)) :=
    match d {
        { chunks, len, need, frag, frag_len, from_client, max_message } =>
            let total := I64.add len (Ws.count (Shared.of bytes) 0) in
            let all := List.cons bytes chunks in
            let rules : WsRules := { from_client := from_client, max_message := max_message } in
            if I64.lt total need
            then
                let d2 : WsDecoder :=
                    { chunks := all, len := total, need := need, frag := frag, frag_len := frag_len,
                        from_client := from_client, max_message := max_message } in
                Result.ok (Pair.pair d2 List.empty)
            else Ws.parse_loop rules frag frag_len (Ws.join_rev all List.empty) total List.empty
    }

/// Parse every complete frame at the front of `buf` (`blen` bytes long).
/// The buffer is split once into its first 14 bytes (a whole header) and
/// the rest, so each piece is moved once into the frame or back into the
/// decoder's buffer.
#[terminating]
def Ws.parse_loop (rules : WsRules) (frag : Option WsFragments) (frag_len : I64) (buf : List U8) (blen : I64)
    (out : List WsInbound) : Result WsClose (Pair WsDecoder (List WsInbound)) :=
    match Ws.split_head buf {
        Pair.pair head rest =>
            match Ws.parse_header rules frag_len head blen {
                Result.err c => Result.err c,
                Result.ok step =>
                    match step {
                        WsStep.more need =>
                            let d2 : WsDecoder :=
                                { chunks := [List.append head rest], len := blen, need := need, frag := frag,
                                    frag_len := frag_len, from_client := rules.from_client,
                                    max_message := rules.max_message } in
                            Result.ok (Pair.pair d2 (List.reverse out)),
                        WsStep.frame hdr_len mask payload_len fin op =>
                            let frame_len := I64.add hdr_len payload_len in
                            match Ws.take_frame frame_len (Ws.head_len blen) (Clone.clone (Shared.of head)) rest {
                                Pair.pair frame_bytes rest2 =>
                                    let raw := Strings.drop_bytes hdr_len frame_bytes in
                                    let payload :=
                                        match mask {
                                            Option.none => raw,
                                            Option.some m => Ws.apply_mask m raw
                                        } in
                                    match Ws.on_frame frag frag_len fin op payload payload_len {
                                        Result.err c => Result.err c,
                                        Result.ok folded =>
                                            match folded {
                                                { frag := frag2, frag_len := len2, emitted } =>
                                                    Ws.parse_loop rules frag2 len2 rest2
                                                        (I64.sub blen frame_len) (Ws.emit emitted out)
                                            }
                                    }
                            }
                    }
            }
    }

/// How many bytes `Ws.split_head` kept for a buffer `blen` long.
def Ws.head_len (blen : I64) : I64 :=
    if I64.gt blen 14 then 14 else blen

/// The first `n` bytes of `head ++ rest` (with `head` `head_len` long),
/// and what is left after them.
def Ws.take_frame (n : I64) (head_len : I64) (head : List U8) (rest : List U8) : Pair (List U8) (List U8) :=
    match Ws.split_at n head List.empty {
        Pair.pair fh rest_after =>
            if I64.gt n head_len then
                match Ws.split_at (I64.sub n head_len) rest List.empty {
                    Pair.pair fr rr => Pair.pair (List.append fh fr) rr
                }
            else Pair.pair fh (List.append rest_after rest)
    }

def Ws.emit (emitted : Option WsInbound) (out : List WsInbound) : List WsInbound :=
    match emitted {
        Option.none => out,
        Option.some u => List.cons u out
    }

/// What the bytes at the front of the buffer say: more bytes are needed
/// (how many in total), or a whole frame is there.
type WsStep {
    more (need : I64),
    frame (hdr_len : I64) (mask : Option WsMask) (payload_len : I64) (fin : Bool) (op : WsOpcode)
}

/// `buf` split after its first ≤14 bytes — enough for any frame header.
def Ws.split_head (buf : List U8) : Pair (List U8) (List U8) :=
    Ws.split_at 14 buf List.empty

/// Read a frame header from `head` (the buffer's first ≤14 bytes; the
/// buffer is `blen` long).
def Ws.parse_header (rules : WsRules) (frag_len : I64) (head : List U8) (blen : I64) : Result WsClose WsStep :=
    match head {
        List.empty => Result.ok (WsStep.more 2),
        List.cons b0 rest0 =>
            match rest0 {
                List.empty => Result.ok (WsStep.more 2),
                List.cons b1 rest1 => Ws.parse_header2 rules frag_len b0 b1 rest1 blen
            }
    }

def Ws.protocol_error (reason : String) : Result WsClose WsStep :=
    Result.err (WsClose.of Ws.close_protocol_error reason)

def Ws.parse_header2 (rules : WsRules) (frag_len : I64) (b0 : U8) (b1 : U8) (rest : List U8) (blen : I64)
    : Result WsClose WsStep :=
    let fin := Ws.bits b0 0x80 == 0x80 in
    let masked := Ws.bits b1 0x80 == 0x80 in
    let len7 := Ws.bits b1 0x7f in
    let code := Ws.bits b0 0x0f in
    let control := Bool.not (I64.lt code 8) in
    if Bool.not (Ws.bits b0 0x70 == 0) then Ws.protocol_error "reserved bits set"
    else if Bool.not (masked == rules.from_client)
    then Ws.protocol_error (if rules.from_client then "client frame not masked" else "server frame masked")
    else if Bool.and control (Bool.not fin) then Ws.protocol_error "fragmented control frame"
    else if Bool.and control (I64.gt len7 125) then Ws.protocol_error "control frame over 125 bytes"
    else
        match WsOpcode.of_code code {
            Option.none => Ws.protocol_error "unknown opcode",
            Option.some op =>
                let ext := if len7 == 126 then 2 else if len7 == 127 then 8 else 0 in
                let hdr_len := I64.add 2 (I64.add ext (if masked then 4 else 0)) in
                if I64.lt blen hdr_len then Result.ok (WsStep.more hdr_len)
                else
                    match Ws.split_at ext rest List.empty {
                        Pair.pair ext_bytes after_ext =>
                            let mask : Option WsMask := if masked then Option.some (WsMask.of_bytes after_ext) else Option.none in
                            let plen : I64 := Ws.payload_length len7 ext_bytes in
                            if I64.lt plen 0 then Ws.protocol_error "64-bit length with the top bit set"
                            else if Bool.and (Bool.not control) (I64.gt (I64.add frag_len plen) rules.max_message)
                            then Result.err (WsClose.of Ws.close_too_big "message exceeds the size limit")
                            else if I64.lt blen (I64.add hdr_len plen) then Result.ok (WsStep.more (I64.add hdr_len plen))
                            else Result.ok (WsStep.frame hdr_len mask plen fin op)
                    }
        }

/// The payload length the 7-bit field and its extension name; -1 for a
/// 64-bit length with the top bit set (RFC 6455 §5.2).
def Ws.payload_length (len7 : I64) (ext_bytes : List U8) : I64 :=
    if I64.lt len7 126 then len7
    else match ext_bytes {
        List.empty => -1,
        List.cons first rest =>
            if Bool.and (len7 == 127) (Ws.bits first 0x80 == 0x80) then -1
            else Ws.be_value rest (U8.to_i64 first)
    }

def Ws.folded (frag : Option WsFragments) (frag_len : I64) (emitted : Option WsInbound) : Result WsClose WsFolded :=
    let f : WsFolded := { frag := frag, frag_len := frag_len, emitted := emitted } in
    Result.ok f

/// Fold one complete, unmasked frame into the reassembly state.
def Ws.on_frame (frag : Option WsFragments) (frag_len : I64) (fin : Bool) (op : WsOpcode) (payload : List U8)
    (plen : I64) : Result WsClose WsFolded :=
    match op {
        WsOpcode.ping => Ws.folded frag frag_len (Option.some (WsInbound.ping payload)),
        WsOpcode.pong => Ws.folded frag frag_len (Option.some (WsInbound.pong payload)),
        WsOpcode.close =>
            match Ws.decode_close payload {
                Result.err c => Result.err c,
                Result.ok c => Ws.folded frag frag_len (Option.some (WsInbound.close c))
            },
        WsOpcode.continuation =>
            match frag {
                Option.none => Result.err (WsClose.of Ws.close_protocol_error "continuation with no message open"),
                Option.some f =>
                    match f {
                        { op := mop, chunks } =>
                            let all := List.cons payload chunks in
                            if fin
                            then Ws.finish_message mop (Ws.join_rev all List.empty)
                            else
                                let open_f : WsFragments := { op := mop, chunks := all } in
                                Ws.folded (Option.some open_f) (I64.add frag_len plen) Option.none
                    }
            },
        _ =>
            match frag {
                Option.some _ =>
                    Result.err (WsClose.of Ws.close_protocol_error "new message while a fragmented one is open"),
                Option.none =>
                    if fin then Ws.finish_message op payload
                    else
                        let open_f : WsFragments := { op := op, chunks := [payload] } in
                        Ws.folded (Option.some open_f) plen Option.none
            }
    }

/// A completed data message (no fragments remain open).
def Ws.finish_message (op : WsOpcode) (payload : List U8) : Result WsClose WsFolded :=
    match op {
        WsOpcode.text =>
            if Ws.valid_utf8 (Shared.of payload)
            then Ws.folded Option.none 0 (Option.some (WsInbound.message (WsMessage.text (String.from_list payload))))
            else Result.err (WsClose.of Ws.close_invalid_data "text message is not UTF-8"),
        _ => Ws.folded Option.none 0 (Option.some (WsInbound.message (WsMessage.binary payload)))
    }
