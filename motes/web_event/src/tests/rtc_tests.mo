/// The WebRTC codecs are pure, so they test natively. Every assertion here
/// pins a shape `wasm/web/web_runtime.js` has to produce, so a host that
/// renumbers a state or reorders a candidate blob fails the suite instead of
/// silently reporting the wrong thing.
///
/// Every `Option.some` result is destructured exactly ONCE. Binding it and
/// then reading two projections of it reports a false affine violation: a
/// pattern binder is attributed to its constructor's declared field type (a
/// type variable) rather than to the concrete type the scrutinee gives it.

use lib::rtc {
    RtcSdp, RtcIce, RtcState, RtcData, RtcChannel, RtcIceServer,
    encode_sdp, decode_sdp, encode_ice, decode_ice, state_of_code,
    encode_ice_servers, decode_message,
    RtcSdp.kind_of, RtcSdp.text_of, RtcData.text_of, RtcData.bytes_of,
    RtcState.channel_name, RtcState.connection_name,
}
use std::list {}

// ═══ Description codec ═══

#[test]
def test_sdp_round_trips_an_offer : Bool :=
    let d : RtcSdp := { kind := "offer", text := "v=0\r\no=- 1 2 IN IP4 127.0.0.1\r\n" } in
    match decode_sdp (encode_sdp d) {
        Option.none => false,
        Option.some back => match back {
            { kind, text } =>
                String.beq kind "offer"
                    && String.beq text "v=0\r\no=- 1 2 IN IP4 127.0.0.1\r\n",
        },
    }

/// An empty document is still a valid description: `setRemoteDescription`
/// accepts one, and the codec must not confuse "no text" with "no prefix".
#[test]
def test_sdp_round_trips_an_empty_document : Bool :=
    let d : RtcSdp := { kind := "answer", text := "" } in
    match decode_sdp (encode_sdp d) {
        Option.none => false,
        Option.some back => match back {
            { kind, text } => String.beq kind "answer" && String.beq text "",
        },
    }

/// The SDP body contains colons and `\r\n`, so nothing but the length prefix
/// delimits it.
#[test]
def test_sdp_body_may_contain_colons_and_newlines : Bool :=
    let body : String := "a:m=audio 9 UDP/TLS/RTP/SAVPF 111:b\r\nc:IN IP4 0.0.0.0\r\n" in
    let d : RtcSdp := { kind := "offer", text := body } in
    match decode_sdp (encode_sdp d) {
        Option.none => false,
        Option.some back => String.beq (RtcSdp.text_of back) body,
    }

#[test]
def test_sdp_rejects_a_missing_prefix : Bool :=
    match decode_sdp "no-prefix-here" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_sdp_rejects_an_overlong_type_length : Bool :=
    // Declares a 99-byte type in a 4-byte string.
    match decode_sdp "99:ab" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_sdp_rejects_the_empty_string : Bool :=
    match decode_sdp "" {
        Option.none => true,
        Option.some _ => false,
    }

// ═══ Candidate codec ═══

#[test]
def test_ice_round_trips_a_candidate : Bool :=
    let c : RtcIce := { candidate := "candidate:1 1 udp 2113937151 192.168.0.2 50000 typ host",
        sdp_mid := "0", sdp_mline_index := 0i64, username_fragment := "abcd" } in
    match decode_ice (encode_ice c) {
        Option.none => false,
        Option.some back => match back {
            { candidate, sdp_mid, sdp_mline_index, username_fragment } =>
                String.beq candidate "candidate:1 1 udp 2113937151 192.168.0.2 50000 typ host"
                    && String.beq sdp_mid "0"
                    && I64.beq sdp_mline_index 0i64
                    && String.beq username_fragment "abcd",
        },
    }

/// The end-of-candidates marker: an empty `candidate`, empty mid, `-1`.
#[test]
def test_ice_round_trips_the_end_of_candidates_marker : Bool :=
    let marker : RtcIce := { candidate := "", sdp_mid := "",
        sdp_mline_index := 0i64 - 1i64, username_fragment := "" } in
    match decode_ice (encode_ice marker) {
        Option.none => false,
        Option.some back => match back {
            { candidate, sdp_mid, sdp_mline_index, username_fragment } =>
                String.beq candidate "" && String.beq sdp_mid ""
                    && I64.beq sdp_mline_index (0i64 - 1i64)
                    && String.beq username_fragment "",
        },
    }

/// A candidate line contains spaces, so a separator-delimited codec would
/// split it; the length prefix must carry it whole.
#[test]
def test_ice_candidate_line_survives_spaces : Bool :=
    let line : String := "candidate:842163049 1 udp 1677729535 8.8.8.8 51820 typ srflx" in
    let c : RtcIce := { candidate := line, sdp_mid := "data",
        sdp_mline_index := 2i64, username_fragment := "u" } in
    match decode_ice (encode_ice c) {
        Option.none => false,
        Option.some back => match back {
            { candidate, sdp_mid, sdp_mline_index, .. } =>
                String.beq candidate line && String.beq sdp_mid "data"
                    && I64.beq sdp_mline_index 2i64,
        },
    }

/// A negative index round-trips: `-1` is a real value, not a parse failure.
#[test]
def test_ice_negative_media_index_round_trips : Bool :=
    let c : RtcIce := { candidate := "c", sdp_mid := "0",
        sdp_mline_index := 0i64 - 2i64, username_fragment := "u" } in
    match decode_ice (encode_ice c) {
        Option.none => false,
        Option.some back => match back {
            { sdp_mline_index, .. } => I64.beq sdp_mline_index (0i64 - 2i64),
        },
    }

/// A truncated blob is rejected rather than read as end-of-candidates.
#[test]
def test_ice_rejects_a_truncated_blob : Bool :=
    match decode_ice "5:abcd" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_ice_rejects_a_missing_prefix : Bool :=
    match decode_ice "x" {
        Option.none => true,
        Option.some _ => false,
    }

// ═══ State vocabulary ═══

/// The numbers are `web_runtime.js`'s; pin every one.
#[test]
def test_state_codes_map_to_the_host_numbers : Bool :=
    String.beq (RtcState.channel_name (state_of_code 0i64)) "connecting"
        && String.beq (RtcState.channel_name (state_of_code 1i64)) "open"
        && String.beq (RtcState.channel_name (state_of_code 2i64)) "closing"
        && String.beq (RtcState.channel_name (state_of_code 3i64)) "closed"
        && String.beq (RtcState.channel_name (state_of_code 4i64)) "failed"
        && String.beq (RtcState.channel_name (state_of_code 99i64)) "unknown"

/// An unrecognised code is `unknown`, never `ready`: a future browser state
/// must not read as "this channel works".
#[test]
def test_unknown_state_code_is_not_ready : Bool :=
    Bool.not (String.beq (RtcState.channel_name (state_of_code 7i64)) "open")

#[test]
def test_connection_names_use_the_connection_vocabulary : Bool :=
    String.beq (RtcState.connection_name (state_of_code 0i64)) "new"
        && String.beq (RtcState.connection_name (state_of_code 1i64)) "connected"
        && String.beq (RtcState.connection_name (state_of_code 4i64)) "failed"
        && String.beq (RtcState.connection_name (state_of_code 3i64)) "closed"

// ═══ Payload accessors ═══

#[test]
def test_rtc_data_text_payload : Bool :=
    String.beq (RtcData.text_of (RtcData.text "hi")) "hi"

#[test]
def test_rtc_data_text_payload_bytes_are_utf8 : Bool :=
    I64.beq (List.length (RtcData.bytes_of (RtcData.text "hi"))) 2i64

#[test]
def test_rtc_data_binary_payload_has_no_text : Bool :=
    String.beq (RtcData.text_of (RtcData.binary [1u8, 2u8, 3u8])) ""

#[test]
def test_rtc_data_binary_payload_bytes : Bool :=
    I64.beq (List.length (RtcData.bytes_of (RtcData.binary [1u8, 2u8, 3u8]))) 3i64

// ═══ Channel identity ═══

/// A channel is named by its label; that is what both peers agreed on and
/// what `Command.rtc_send` addresses.
#[test]
def test_channel_carries_its_label : Bool :=
    let ch : RtcChannel := { label := "chat", ordered := true, max_retransmits := 0i64 } in
    match ch {
        { label, ordered, .. } => String.beq label "chat" && ordered,
    }

// ═══ ICE server config ═══

/// A STUN server needs no credentials, so both are empty and still encode.
#[test]
def test_ice_servers_encode_a_stun_server : Bool :=
    let s : RtcIceServer := { url := "stun:stun.example.org", username := "",
        credential := "" } in
    String.beq (encode_ice_servers [s]) "21:stun:stun.example.org0:0:"

/// A TURN URL contains colons (`turn:host:3478?transport=udp`), so only the
/// length prefix can delimit it.
#[test]
def test_ice_servers_encode_a_turn_url_with_colons : Bool :=
    let url : String := "turn:host.example.org:3478?transport=udp" in
    let s : RtcIceServer := { url := url, username := "user", credential := "pass" } in
    String.beq (encode_ice_servers [s])
        (String.concat (I64.to_string (String.length url))
            (String.concat ":" (String.concat url "4:user4:pass")))

/// An empty list is "" -- the host then builds a peer with `iceServers: []`,
/// which still connects two peers on one host.
#[test]
def test_no_ice_servers_encodes_as_the_empty_string : Bool :=
    String.beq (encode_ice_servers List.empty) ""

#[test]
def test_ice_servers_encode_several_in_order : Bool :=
    let a : RtcIceServer := { url := "stun:a", username := "", credential := "" } in
    let b : RtcIceServer := { url := "turn:b", username := "u", credential := "p" } in
    let two : List RtcIceServer := [a, b] in
    String.beq (encode_ice_servers two) "6:stun:a0:0:6:turn:b1:u1:p"

// ═══ Message payload ═══

/// A queued message packs its channel label and its body into one buffer, so
/// a body of arbitrary bytes (NUL included) survives.
#[test]
def test_message_payload_splits_the_label_from_the_body : Bool :=
    match decode_message "4:chathello" {
        Option.none => false,
        Option.some p => match p {
            Pair.pair label body => String.beq label "chat" && String.beq body "hello",
        },
    }

/// An empty label is legal -- a data channel may be opened with `""`.
#[test]
def test_message_payload_allows_an_empty_label : Bool :=
    match decode_message "0:body" {
        Option.none => false,
        Option.some p => match p {
            Pair.pair label body => String.beq label "" && String.beq body "body",
        },
    }

/// An empty body is legal too: a peer may send a zero-byte frame.
#[test]
def test_message_payload_allows_an_empty_body : Bool :=
    match decode_message "4:chat" {
        Option.none => false,
        Option.some p => match p {
            Pair.pair label body => String.beq label "chat" && String.beq body "",
        },
    }

#[test]
def test_message_payload_rejects_a_missing_prefix : Bool :=
    match decode_message "no-prefix" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_message_payload_rejects_an_overlong_label : Bool :=
    match decode_message "99:x" {
        Option.none => true,
        Option.some _ => false,
    }
