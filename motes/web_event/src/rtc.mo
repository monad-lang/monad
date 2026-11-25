/// The WebRTC vocabulary shared by the browser boundary and the view layer:
/// what a peer connection reports and what it can carry.
///
/// `web_wasm` builds these from the JS `RTCPeerConnection` and `MediaStream`,
/// `oak` names `RtcEvent` in `Subscription.rtc`'s handler, and `oak_wasm`
/// hands them to it. Pure data -- no IO, no handles.
///
/// ## The signalling split
///
/// WebRTC itself has no signalling channel: two peers exchange a session
/// description and ICE candidates over some OTHER transport (a WebSocket, an
/// HTTP endpoint, a QR code). This module models exactly that seam. The host
/// reports what the browser produced -- `RtcEvent.local_description` and
/// `RtcEvent.local_candidate` -- and the app forwards it over whatever it
/// already has; the answer comes back in as `RtcSdp`/`RtcIce` and is handed
/// to `Rtc.set_remote`/`Rtc.add_ice`.
///
/// `RtcSdp.kind` and `RtcIce.sdp_mid` are kept as their own fields rather
/// than being folded into the description text, because a signalling server
/// has to route on them without parsing SDP.
///
/// ## Why the codecs below exist
///
/// A wasm export's ABI is plain i64 words, so a JS callback can never hand a
/// structured value to wasm. Every field the runtime needs therefore crosses
/// as a length-prefixed blob that the pure codecs here decode -- the same
/// shape `lib::fetch`'s header codec uses. Lengths (not separators) delimit
/// the pieces, so a candidate's `sdpMid` or SDP text may contain any
/// character at all; SDP and ICE never carry NUL, so nothing is escaped.
///
/// ## The match-binder alias
///
/// Several defs below re-bind a pattern variable through an annotated `let`
/// before mentioning it twice. The affine walk attributes a pattern binder to
/// its constructor's DECLARED field type (a type variable) rather than to the
/// concrete type the scrutinee gives it, so a bare double use reports a false
/// "used 2 times but is affine" even for `I64` and `U8`, which do have `Copy`
/// instances. `lib::fetch`'s `encode_header` carries the same aliasing for
/// the same reason.

/// One session description: the SDP's type line (`"offer"`, `"answer"`,
/// `"pranswer"`, `"rollback"`) and the description text itself.
///
/// `text` is the whole document, newlines included. A Monad `String` carries
/// it unchanged, so it can be forwarded verbatim to a signalling server.
pub struct RtcSdp {
    kind : String,
    text : String
}

/// One ICE candidate: every field of the browser's `RTCIceCandidateInit`.
///
/// `candidate` is the candidate line itself ("" is the end-of-candidates
/// marker a `null` candidate becomes). `sdp_mid` and `sdp_mline_index` say
/// which media section it belongs to, and `username_fragment` is the
/// `ufrag` the receiving peer validates it against.
pub struct RtcIce {
    candidate : String,
    sdp_mid : String,
    sdp_mline_index : I64,
    username_fragment : String
}

/// One ICE server for `Rtc.connect`: a STUN/TURN URL and, for TURN, the
/// credentials that authorize it. A STUN server needs none, so both are "".
///
/// A STUN server is enough to connect two peers on the open internet; a TURN
/// server is needed behind a symmetric NAT, and its credential is the one
/// secret in this whole API.
pub struct RtcIceServer {
    url : String,
    username : String,
    credential : String
}

/// `RTCDataChannel.readyState` and the peer connection's `connectionState`,
/// folded into one vocabulary both sides can name.
///
/// `ready` is the channel's `"open"` / the connection's `"connected"`. It is
/// not spelled `open`, which is a reserved keyword and so cannot name a
/// constructor.
pub type RtcState {
    /// `"connecting"` on a channel, `"new"` on a connection.
    connecting,
    /// `"open"` on a channel, `"connected"` on a connection.
    ready,
    /// `"closing"` on a channel (no connection equivalent).
    closing,
    /// `"closed"` on a channel; `"closed"` or `"disconnected"` on a
    /// connection.
    closed,
    /// `"failed"` on either.
    failed,
    /// Any state this vocabulary does not name: a future browser state reads
    /// as `unknown`, never as `ready`.
    unknown
}

/// One data-channel payload. `text` is the decoded string, `binary` the raw
/// bytes; the send flag decides which a frame becomes -- the same split
/// `WsData` uses.
pub type RtcData {
    text (s : String),
    binary (bytes : List U8)
}

/// One data channel as the app sees it, identified by its label.
///
/// A channel is addressed by `label` rather than by a host handle because a
/// label is what both peers agreed on, so an app can name the channel it
/// wants in a view or an update without carrying a handle into the model.
/// Two channels with the same label on one peer are a protocol the app owns;
/// the runtime addresses the FIRST, exactly as `Command.ws_send` addresses
/// the first socket for a URL.
pub struct RtcChannel {
    label : String,
    ordered : Bool,
    max_retransmits : I64
}

/// What a peer connection or one of its data channels reports.
///
/// The app sends nothing back through the event: an answer or a candidate
/// goes through `web_wasm::rtc`'s setters, and oak exposes the send path as
/// `Command.rtc_send`, so every update stays pure.
pub type RtcEvent {
    /// The browser produced a local description. Send it to the other peer
    /// (`RtcSdp.kind` is `"offer"` unless the app asked for an answer).
    local_description (sdp : RtcSdp),
    /// A local ICE candidate to forward. A `candidate` of "" is the
    /// end-of-candidates marker.
    local_candidate (ice : RtcIce),
    /// The connection's `connectionState` changed (also `"failed"`,
    /// `"disconnected"` and `"closed"`).
    connection (state : RtcState),
    /// The remote peer opened a data channel (`ondatachannel`).
    data_channel (channel : RtcChannel),
    /// A data channel opened, closed or failed; `label` names which.
    channel_state (label : String) (state : RtcState),
    /// A whole message arrived on the channel called `label`.
    message (label : String) (data : RtcData),
    /// The remote peer is sending a media stream; `stream` is the host's id
    /// for it, which `web_wasm::MediaStream` reads with
    /// `MediaStream.attach`. It arrives once per stream, before the track's
    /// frames, so a UI can bind it to a `<video>` when the event lands.
    ///
    /// The id is a bare `I64` on purpose: this module is pure vocabulary and
    /// must not name a `web_wasm` handle type, so the concrete handle is
    /// produced at the boundary (`web_wasm::Rtc.remote_stream`).
    track (stream : I64)
}

// ─── Accessors ───────────────────────────────────────────────────────

/// The description's type line.
pub def RtcSdp.kind_of (d : RtcSdp) : String := d.kind

/// The description text.
pub def RtcSdp.text_of (d : RtcSdp) : String := d.text

/// The payload's text (`""` for a binary message).
pub def RtcData.text_of (d : RtcData) : String :=
    match d {
        RtcData.text s => s,
        RtcData.binary _ => "",
    }

/// The payload's bytes (a text message's UTF-8).
pub def RtcData.bytes_of (d : RtcData) : List U8 :=
    match d {
        RtcData.text s => String.to_list s,
        RtcData.binary b => b,
    }

// ─── Description codec ───────────────────────────────────────────────
//
// Both directions live here because they must stay in step: the host writes
// `<klen>:<kind><text>`, and `decode_sdp` is its only reader. The type is
// length-prefixed rather than delimited by the first newline so that a
// malformed type cannot swallow the document.

/// Encode a description as `<klen>:<kind><text>`.
///
/// This is also what a signalling client puts on the wire: send `encode_sdp`
/// and receive `decode_sdp`, and the two peers agree on exactly one shape.
pub def encode_sdp (d : RtcSdp) : String :=
    match d {
        { kind, text } =>
            let k : String := kind in
            String.concat (I64.to_string (String.length k))
                (String.concat ":" (String.concat k text)),
    }

/// Read a decimal run starting at `i`; yields the value and the index of the
/// first non-digit (the `:` the caller expects). A non-digit at `i` yields
/// `0` with the index unchanged, which is how an empty prefix is detected.
#[terminating]
def parse_uint_from (s : String) (i : I64) (acc : I64) : Pair I64 I64 :=
    match String.get s i {
        Option.some b =>
            let byte : U8 := b in
            let d : I64 := U8.to_i64 byte - 48 in
            if d < 0 || I64.gt d 9
            then Pair.pair acc i
            else parse_uint_from s (I64.add i 1) (I64.add (I64.mul acc 10) d),
        Option.none => Pair.pair acc i,
    }

/// Decode `<klen>:<kind><text>`; `none` when the prefix is missing or the
/// declared type length runs past the end of the string.
///
/// A decoder that answered a default description instead would turn a
/// signalling bug into a peer connection that silently never connects.
pub def decode_sdp (s : String) : Option RtcSdp :=
    match parse_uint_from s 0 0 {
        Pair.pair klen colon =>
            let kl : I64 := klen in
            let co : I64 := colon in
            if I64.beq kl 0 && I64.beq co 0
            then Option.none
            else
                let start : I64 := I64.add co 1 in
                if I64.gt (I64.add start kl) (String.length s)
                then Option.none
                else
                    let kind : String := String.slice s start kl in
                    let d : RtcSdp := { kind := kind,
                        text := String.drop (I64.add start kl) s } in
                    Option.some d,
    }

// ─── Candidate codec ─────────────────────────────────────────────────
//
// A candidate has four independent parts and one of them (`candidate`) is
// free text that routinely contains spaces, so separators are out. Each part
// is length-prefixed instead:
//   `<clen>:<candidate><mlen>:<mid><ilen>:<mline><ulen>:<ufrag>`
// An empty part is a legal `0:` -- the end-of-candidates marker has no
// `sdpMid`, and a candidate that never belonged to a media section has `-1`
// for its index.

/// Encode a candidate as the length-prefixed blob described above.
pub def encode_ice (c : RtcIce) : String :=
    match c {
        { candidate, sdp_mid, sdp_mline_index, username_fragment } =>
            let mid : String := sdp_mid in
            let ufrag : String := username_fragment in
            let mstr : String := I64.to_string sdp_mline_index in
            String.concat (prefix candidate)
                (String.concat (prefix mid)
                    (String.concat (prefix mstr) (prefix ufrag))),
    }

/// One length-prefixed part on its own: `<len>:<text>`.
def prefix (text : String) : String :=
    String.concat (I64.to_string (String.length text))
        (String.concat ":" text)

/// One length-prefixed part, plus the rest of the string.
///
/// `none` means "malformed" -- the digit run is missing (`colon` stayed at 0,
/// which no valid prefix can produce, since `0:` still has a colon at index
/// 1) or the declared length runs past the end. A `0:` prefix with nothing
/// after the colon is the legal empty part, not an error.
def take_part (s : String) : Option (Pair String String) :=
    match parse_uint_from s 0 0 {
        Pair.pair klen colon =>
            let kl : I64 := klen in
            let co : I64 := colon in
            if I64.beq co 0
            then Option.none
            else
                let start : I64 := I64.add co 1 in
                if I64.gt (I64.add start kl) (String.length s)
                then Option.none
                else
                    Option.some (Pair.pair (String.slice s start kl)
                        (String.drop (I64.add start kl) s)),
    }

/// Decode a candidate blob; `none` on any malformed part.
///
/// Every part is required, in order, so a truncated blob is rejected rather
/// than arriving with an empty `candidate` -- which would read as the
/// end-of-candidates marker and end ICE gathering early.
///
/// One helper per remaining part rather than a four-deep nested `match`:
/// each stage is the same "take a part, carry the rest" step, and the
/// flattened shape is what both checkers (and a reader) handle best.
def decode_ice_part4 (candidate : String) (mid : String) (mline : String)
    (rest : String) : Option RtcIce :=
    match take_part rest {
        Option.none => Option.none,
        Option.some p4 => match p4 {
            Pair.pair ufrag _rest =>
                let c : RtcIce := { candidate := candidate, sdp_mid := mid,
                    sdp_mline_index := parse_maybe_int mline,
                    username_fragment := ufrag } in
                Option.some c,
        },
    }

def decode_ice_part3 (candidate : String) (mid : String) (rest : String) : Option RtcIce :=
    match take_part rest {
        Option.none => Option.none,
        Option.some p3 => match p3 {
            Pair.pair mline rest3 => decode_ice_part4 candidate mid mline rest3,
        },
    }

def decode_ice_part2 (candidate : String) (rest : String) : Option RtcIce :=
    match take_part rest {
        Option.none => Option.none,
        Option.some p2 => match p2 {
            Pair.pair mid rest2 => decode_ice_part3 candidate mid rest2,
        },
    }

pub def decode_ice (s : String) : Option RtcIce :=
    match take_part s {
        Option.none => Option.none,
        Option.some p1 => match p1 {
            Pair.pair candidate rest1 => decode_ice_part2 candidate rest1,
        },
    }

/// A decimal part as an `I64`; anything else (including the empty string)
/// reads as `-1`, which is `RTCIceCandidateInit`'s "no media section".
def parse_maybe_int (s : String) : I64 :=
    if I64.beq (String.length s) 0 then 0i64 - 1i64 else parse_int_body s 0 0i64 1i64

#[terminating]
def parse_int_body (s : String) (i : I64) (acc : I64) (sign : I64) : I64 :=
    match String.get s i {
        Option.some b =>
            let byte : U8 := b in
            if I64.beq i 0 && I64.beq (U8.to_i64 byte) 45i64
            then parse_int_body s 1 0i64 (0i64 - 1i64)
            else
                let d : I64 := U8.to_i64 byte - 48 in
                if d < 0 || I64.gt d 9
                then I64.mul acc sign
                else parse_int_body s (I64.add i 1) (I64.add (I64.mul acc 10) d) sign,
        Option.none => I64.mul acc sign,
    }

// ─── ICE server config codec ─────────────────────────────────────────
//
// The host receives the servers as one blob,
//   `<urllen>:<url><ulen>:<username><clen>:<credential>`
// repeated, so a URL may contain `:` (`turn:host:3478?transport=udp`) and a
// credential may contain anything at all. Same length-prefix discipline as
// the two codecs above; a STUN server simply leaves both credentials empty.

/// Encode `servers` as the concatenated blob described above.
///
/// An empty list encodes as "", and `Rtc.connect` then builds a peer
/// connection with `iceServers: []`: that still connects two peers on the
/// same host (`host` candidates), which is what a smoke test needs.
#[terminating]
pub def encode_ice_servers (servers : List RtcIceServer) : String :=
    match servers {
        List.empty => "",
        List.cons s rest =>
            match s {
                { url, username, credential } =>
                    String.concat (prefix url)
                        (String.concat (prefix username)
                            (String.concat (prefix credential) (encode_ice_servers rest))),
            },
    }

// ─── Message payload codec ───────────────────────────────────────────
//
// A queued `message` entry carries TWO things -- which channel it came from
// and the body -- but a queue entry has one payload buffer. The host packs
// them as `<label length>:<label><body>`, so the body can be arbitrary bytes
// (NUL included) while the label stays a string. Only the DECODER is public:
// the host writes this shape and Monad reads it, so there is exactly one
// writer of the format.

/// Split a message entry's payload into its label and its body.
///
/// `none` when the length prefix is missing or overruns. An EMPTY label is
/// legal -- a data channel may be opened with `""` -- so `""` is not an error
/// marker here.
pub def decode_message (s : String) : Option (Pair String String) :=
    match take_part s {
        Option.none => Option.none,
        Option.some p => match p {
            Pair.pair label body => Option.some (Pair.pair label body),
        },
    }

/// Split a message entry's payload into its label and its BODY BYTES.
///
/// `decode_message` answers a `String` body and is what an all-text protocol
/// wants, but a Monad `String` is NUL-terminated: decoding a binary frame
/// through it truncates at the first `0x00`, and any non-UTF-8 byte is
/// lossy. A binary channel carries arbitrary bytes, so the boundary uses
/// this one instead -- the label is text (the host wrote it), the body is
/// not necessarily.
///
/// Byte-level twin of `take_part`: the digit run is read from `List U8`, and
/// the label is decoded to a `String` only after its length is known to be
/// in range.
#[terminating]
def take_uint_bytes (bytes : List U8) (acc : I64) (digits : I64)
    : Option (Pair I64 (List U8)) :=
    match bytes {
        List.empty => Option.none,
        List.cons b rest =>
            let v : I64 := U8.to_i64 b in
            if I64.beq v 58i64
            then
                if I64.beq digits 0i64
                then Option.none
                else Option.some (Pair.pair acc rest)
            else
                if v < 48i64 || I64.gt v 57i64
                then Option.none
                else take_uint_bytes rest
                    (I64.add (I64.mul acc 10i64) (v - 48i64))
                    (I64.add digits 1i64),
    }

/// The first `n` bytes as a list, plus the rest; `none` when there are fewer.
#[terminating]
def take_n_bytes (bytes : List U8) (n : I64) (acc : List U8)
    : Option (Pair (List U8) (List U8)) :=
    if I64.beq n 0i64
    then Option.some (Pair.pair (List.reverse acc) bytes)
    else match bytes {
        List.empty => Option.none,
        List.cons b rest => take_n_bytes rest (I64.sub n 1i64) (List.cons b acc),
    }

pub def decode_message_bytes (bytes : List U8) : Option (Pair String (List U8)) :=
    match take_uint_bytes bytes 0i64 0i64 {
        Option.none => Option.none,
        Option.some p => match p {
            Pair.pair n rest => match take_n_bytes rest n List.empty {
                Option.none => Option.none,
                Option.some l => match l {
                    Pair.pair label body =>
                        Option.some (Pair.pair (String.from_list label) body),
                },
            },
        },
    }
// ─── State vocabulary ────────────────────────────────────────────────

/// The host's numeric state code: the data-channel mapping, shared with
/// `wasm/web/web_runtime.js`. `state_of_code` is the one reader, so a host
/// that renumbers a state fails the drift tests rather than silently
/// reporting `ready`.
///
/// 0 connecting, 1 ready, 2 closing, 3 closed, 4 failed, anything else
/// unknown.
pub def state_of_code (code : I64) : RtcState :=
    if I64.beq code 1i64
    then RtcState.ready
    else if I64.beq code 0i64
    then RtcState.connecting
    else if I64.beq code 2i64
    then RtcState.closing
    else if I64.beq code 3i64
    then RtcState.closed
    else if I64.beq code 4i64
    then RtcState.failed
    else RtcState.unknown

/// The data channel's spelling of a state, for a log line or a view.
pub def RtcState.channel_name (st : RtcState) : String :=
    match st {
        RtcState.connecting => "connecting",
        RtcState.ready => "open",
        RtcState.closing => "closing",
        RtcState.closed => "closed",
        RtcState.failed => "failed",
        RtcState.unknown => "unknown",
    }

/// The peer connection's spelling of the same state. A status line about the
/// link itself wants this one; `channel_name` is about a channel.
pub def RtcState.connection_name (st : RtcState) : String :=
    match st {
        RtcState.connecting => "new",
        RtcState.ready => "connected",
        RtcState.closing => "closing",
        RtcState.closed => "closed",
        RtcState.failed => "failed",
        RtcState.unknown => "unknown",
    }
