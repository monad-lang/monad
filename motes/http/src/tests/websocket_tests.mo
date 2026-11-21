/// WebSocket handshake and frame codec tests — RFC 6455 §1.3 / §5.7 vectors,
/// length boundaries, split feeding, and one test per protocol violation.

use http::websocket {
    WsClose, WsDecoder, WsDecoder.new, WsFrame, WsInbound, WsMask, WsMessage,
    WsOffer, WsOpcode, Ws.accept_key, Ws.accept_response, Ws.apply_mask, Ws.check_accept,
    Ws.check_upgrade, Ws.client_headers, Ws.control_frame, Ws.decode_close, Ws.encode_close,
    Ws.encode_frame, Ws.message_frame, Ws.push, Ws.select_protocol, Ws.valid_utf8, WsClose.of,
}
use http::types {Headers, Headers.empty, Headers.get, Headers.set, Method, Response, Status.switching_protocols}
use std::list {}

def hello : List U8 := [0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
def mask_key : List U8 := [0x37u8, 0xfau8, 0x21u8, 0x3du8]

/// `n` copies of byte `b`.
#[terminating]
def fill (n : I64) (b : U8) (acc : List U8) : List U8 :=
    if I64.gt n 0 then fill (n - 1) b (List.cons b acc) else acc

/// Everything one push of `bytes` into a fresh decoder yields; `none` on a
/// protocol error.
def decode_all (from_client : Bool) (bytes : List U8) : Option (List WsInbound) :=
    match Ws.push (WsDecoder.new from_client 1048576) bytes {
        Result.ok pr => match pr { Pair.pair _ out => Option.some out },
        Result.err _ => Option.none
    }

/// The close code a push of `bytes` fails with (0 when it succeeds).
def error_code (from_client : Bool) (max : I64) (bytes : List U8) : I64 :=
    match Ws.push (WsDecoder.new from_client max) bytes {
        Result.ok _ => 0,
        Result.err c => c.code
    }

/// Feed `bytes` one byte at a time, collecting every unit.
#[terminating]
def feed_bytes (d : WsDecoder) (bytes : List U8) (acc : List WsInbound) : Option (List WsInbound) :=
    match bytes {
        List.empty => Option.some acc,
        List.cons b rest =>
            match Ws.push d [b] {
                Result.err _ => Option.none,
                Result.ok pr => match pr { Pair.pair d2 out => feed_bytes d2 rest (List.append acc out) }
            }
    }

def is_text (u : WsInbound) (s : String) : Bool :=
    match u {
        WsInbound.message m => match m { WsMessage.text t => t == s, _ => false },
        _ => false
    }

def is_binary_len (u : WsInbound) (n : I64) : Bool :=
    match u {
        WsInbound.message m => match m { WsMessage.binary b => List.length b == n, _ => false },
        _ => false
    }

def one_text (r : Option (List WsInbound)) (s : String) : Bool :=
    match r {
        Option.some us => match us { List.cons u rest => List.is_empty rest && is_text u s, _ => false },
        Option.none => false
    }

def accepted (r : Result String (Option String)) : Option String :=
    match r { Result.ok p => p, Result.err _ => Option.some "<refused>" }

def refused (r : Result String (Option String)) : Bool :=
    match r { Result.ok _ => false, Result.err _ => true }

// ── handshake ───────────────────────────────────────────────────────────

#[test]
def test_accept_key_rfc_example : Bool :=
    Ws.accept_key "dGhlIHNhbXBsZSBub25jZQ==" == "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="

def upgrade_headers : Headers :=
    Headers.set "Sec-WebSocket-Protocol" "chat, superchat"
        (Headers.set "Sec-WebSocket-Version" "13"
            (Headers.set "Sec-WebSocket-Key" "dGhlIHNhbXBsZSBub25jZQ=="
                (Headers.set "Connection" "keep-alive, Upgrade"
                    (Headers.set "Upgrade" "WebSocket" Headers.empty))))

#[test]
def test_check_upgrade_accepts : Bool :=
    match Ws.check_upgrade Method.GET (Shared.of upgrade_headers) {
        Result.ok offer => offer.key == "dGhlIHNhbXBsZSBub25jZQ==" && offer.protocols == ["chat", "superchat"],
        Result.err _ => false
    }

def refusal_status (method : Method) (h : Headers) : U16 :=
    match Ws.check_upgrade method (Shared.of h) {
        Result.ok _ => 0u16,
        Result.err r => r.status
    }

#[test]
def test_check_upgrade_refusals : Bool :=
    refusal_status Method.POST upgrade_headers == 405u16
        && refusal_status Method.GET Headers.empty == 426u16
        && refusal_status Method.GET (Headers.set "Sec-WebSocket-Version" "8" upgrade_headers) == 426u16
        && refusal_status Method.GET (Headers.set "Sec-WebSocket-Key" "c2hvcnQ=" upgrade_headers) == 400u16
        && refusal_status Method.GET (Headers.set "Connection" "keep-alive" upgrade_headers) == 426u16

#[test]
def test_select_protocol_server_preference : Bool :=
    Ws.select_protocol (Shared.of ["chat", "superchat"]) ["superchat", "chat"] == Option.some "superchat"
        && Ws.select_protocol (Shared.of ["chat"]) ["v2"] == Option.none

#[test]
def test_accept_response_round_trip : Bool :=
    let key := "dGhlIHNhbXBsZSBub25jZQ==" in
    let r := Ws.accept_response key (Option.some "chat") in
    r.status == Status.switching_protocols
        && Headers.get "Sec-WebSocket-Accept" r.headers == Option.some "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        && accepted (Ws.check_accept key (Shared.of ["chat", "v2"]) r.status (Shared.of r.headers)) == Option.some "chat"

#[test]
def test_check_accept_rejects : Bool :=
    let key := "dGhlIHNhbXBsZSBub25jZQ==" in
    let good := Ws.accept_response key Option.none in
    refused (Ws.check_accept key (Shared.of []) 200u16 (Shared.of good.headers))
        && refused (Ws.check_accept "AAAAAAAAAAAAAAAAAAAAAA==" (Shared.of []) good.status (Shared.of good.headers))
        && refused (Ws.check_accept key (Shared.of []) good.status (Shared.of (Headers.set "Sec-WebSocket-Protocol" "x" good.headers)))
        && refused (Ws.check_accept key (Shared.of []) good.status (Shared.of (Headers.set "Sec-WebSocket-Extensions" "permessage-deflate" good.headers)))

#[test]
def test_client_headers : Bool :=
    let h := Ws.client_headers "k" ["a", "b"] Headers.empty in
    Headers.get "Upgrade" h == Option.some "websocket"
        && Headers.get "Sec-WebSocket-Version" h == Option.some "13"
        && Headers.get "Sec-WebSocket-Protocol" h == Option.some "a, b"

// ── encoding (RFC 6455 §5.7) ────────────────────────────────────────────

#[test]
def test_encode_unmasked_hello : Bool :=
    Ws.encode_frame Option.none (Ws.message_frame (WsMessage.text "Hello"))
        == [0x81u8, 0x05u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]

#[test]
def test_encode_masked_hello : Bool :=
    Ws.encode_frame (Option.some (WsMask.of_bytes mask_key)) (Ws.message_frame (WsMessage.text "Hello"))
        == [0x81u8, 0x85u8, 0x37u8, 0xfau8, 0x21u8, 0x3du8, 0x7fu8, 0x9fu8, 0x4du8, 0x51u8, 0x58u8]

#[test]
def test_encode_length_16 : Bool :=
    match Ws.encode_frame Option.none (Ws.message_frame (WsMessage.binary (fill 256 7u8 List.empty))) {
        List.cons b0 r0 => match r0 {
            List.cons b1 r1 => match r1 {
                List.cons b2 r2 => match r2 {
                    List.cons b3 r3 =>
                        b0 == 0x82u8 && b1 == 0x7eu8 && b2 == 0x01u8 && b3 == 0x00u8 && List.length r3 == 256,
                    _ => false
                },
                _ => false
            },
            _ => false
        },
        _ => false
    }

#[test]
def test_encode_length_64 : Bool :=
    let frame := Ws.encode_frame Option.none (Ws.message_frame (WsMessage.binary (fill 65536 1u8 List.empty))) in
    List.length frame == 65546
        && List.get 1 frame == Option.some 0x7fu8
        && List.get 7 frame == Option.some 0x01u8
        && List.get 8 frame == Option.some 0x00u8

#[test]
def test_mask_is_involution : Bool :=
    Ws.apply_mask (WsMask.of_bytes mask_key) (Ws.apply_mask (WsMask.of_bytes mask_key) hello) == hello

#[test]
def test_close_payload_round_trip : Bool :=
    (match Ws.decode_close (Ws.encode_close (WsClose.of 1000 "bye")) {
        Result.ok c => c.code == 1000 && c.reason == "bye",
        Result.err _ => false
    })
        && Ws.encode_close (WsClose.of 1005 "x") == List.empty

// ── decoding ────────────────────────────────────────────────────────────

#[test]
def test_decode_unmasked_hello : Bool :=
    one_text (decode_all false [0x81u8, 0x05u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]) "Hello"

#[test]
def test_decode_masked_hello : Bool :=
    one_text (decode_all true [0x81u8, 0x85u8, 0x37u8, 0xfau8, 0x21u8, 0x3du8, 0x7fu8, 0x9fu8, 0x4du8, 0x51u8, 0x58u8]) "Hello"

#[test]
def test_decode_fragmented_with_interleaved_ping : Bool :=
    match decode_all false [0x01u8, 0x03u8, 0x48u8, 0x65u8, 0x6cu8, 0x89u8, 0x00u8, 0x80u8, 0x02u8, 0x6cu8, 0x6fu8] {
        Option.some us => match us {
            List.cons p rest => match rest {
                List.cons m rest2 =>
                    List.is_empty rest2
                        && (match p { WsInbound.ping pl => List.is_empty pl, _ => false })
                        && is_text m "Hello",
                _ => false
            },
            _ => false
        },
        Option.none => false
    }

#[test]
def test_decode_byte_at_a_time : Bool :=
    let wire :=
        List.append [0x81u8, 0x85u8, 0x37u8, 0xfau8, 0x21u8, 0x3du8, 0x7fu8, 0x9fu8, 0x4du8, 0x51u8, 0x58u8]
            (Ws.encode_frame (Option.some (WsMask.of_bytes mask_key)) (Ws.message_frame (WsMessage.binary (fill 300 9u8 List.empty)))) in
    match feed_bytes (WsDecoder.new true 1048576) wire List.empty {
        Option.some us => match us {
            List.cons a rest => match rest {
                List.cons b rest2 => List.is_empty rest2 && is_text a "Hello" && is_binary_len b 300,
                _ => false
            },
            _ => false
        },
        Option.none => false
    }

#[test]
def test_decode_two_frames_one_push : Bool :=
    let one := Ws.encode_frame Option.none (Ws.message_frame (WsMessage.text "a")) in
    let two := Ws.encode_frame Option.none (Ws.message_frame (WsMessage.text "b")) in
    match decode_all false (List.append one two) {
        Option.some us => List.length us == 2,
        Option.none => false
    }

#[test]
def test_decode_close_frame : Bool :=
    match decode_all false (Ws.encode_frame Option.none (Ws.control_frame WsOpcode.close (Ws.encode_close (WsClose.of 1001 "away")))) {
        Option.some us => match us {
            List.cons u _ => match u { WsInbound.close c => c.code == 1001 && c.reason == "away", _ => false },
            _ => false
        },
        Option.none => false
    }

// ── violations → close codes ────────────────────────────────────────────

#[test]
def test_unmasked_client_frame_is_1002 : Bool :=
    error_code true 1024 [0x81u8, 0x01u8, 0x41u8] == 1002

#[test]
def test_masked_server_frame_is_1002 : Bool :=
    error_code false 1024 [0x81u8, 0x81u8, 0u8, 0u8, 0u8, 0u8, 0x41u8] == 1002

#[test]
def test_reserved_bits_are_1002 : Bool :=
    error_code false 1024 [0xc1u8, 0x01u8, 0x41u8] == 1002

#[test]
def test_unknown_opcode_is_1002 : Bool :=
    error_code false 1024 [0x83u8, 0x00u8] == 1002

#[test]
def test_fragmented_control_is_1002 : Bool :=
    error_code false 1024 [0x09u8, 0x00u8] == 1002

#[test]
def test_long_control_is_1002 : Bool :=
    error_code false 1024 [0x89u8, 0x7eu8, 0x00u8, 0x80u8] == 1002

#[test]
def test_orphan_continuation_is_1002 : Bool :=
    error_code false 1024 [0x80u8, 0x01u8, 0x41u8] == 1002

#[test]
def test_new_message_inside_fragment_is_1002 : Bool :=
    error_code false 1024 [0x01u8, 0x01u8, 0x41u8, 0x81u8, 0x01u8, 0x42u8] == 1002

#[test]
def test_invalid_utf8_text_is_1007 : Bool :=
    error_code false 1024 [0x81u8, 0x02u8, 0xc3u8, 0x28u8] == 1007

#[test]
def test_too_big_is_1009_from_header : Bool :=
    // The header alone claims 200 bytes over a 100-byte limit: refused
    // before any payload arrives.
    error_code false 100 [0x82u8, 0x7eu8, 0x00u8, 0xc8u8] == 1009

#[test]
def test_fragments_sum_past_limit_is_1009 : Bool :=
    error_code false 3 [0x02u8, 0x02u8, 1u8, 2u8, 0x80u8, 0x02u8, 3u8, 4u8] == 1009

#[test]
def test_bad_close_code_is_1002 : Bool :=
    error_code false 1024 [0x88u8, 0x02u8, 0x03u8, 0xedu8] == 1002
        && error_code false 1024 [0x88u8, 0x01u8, 0x03u8] == 1002

// ── UTF-8 ───────────────────────────────────────────────────────────────

#[test]
def test_utf8_validator : Bool :=
    Ws.valid_utf8 (Shared.of (String.to_list "héllo — ✓ 𝄞"))
        && Bool.not (Ws.valid_utf8 (Shared.of [0xc0u8, 0x80u8])) // overlong NUL
        && Bool.not (Ws.valid_utf8 (Shared.of [0xedu8, 0xa0u8, 0x80u8])) // surrogate
        && Bool.not (Ws.valid_utf8 (Shared.of [0xf4u8, 0x90u8, 0x80u8, 0x80u8])) // > U+10FFFF
        && Bool.not (Ws.valid_utf8 (Shared.of [0xe2u8, 0x82u8])) // truncated
