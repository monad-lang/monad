/// The browser `RTCPeerConnection`, imperative and per-frame friendly.
///
/// Two things shape this API.
///
/// **Nothing is awaited.** A JS promise callback must not re-enter wasm while
/// a Monad frame is on the stack, so no operation here returns a promise. The
/// browser's own asynchronous reports -- the description it produced once
/// `set_local`/`set_remote` ran, each ICE candidate it gathered, every
/// connection-state change, every data-channel event -- are APPENDED to the
/// peer's queue by the host, and this module drains it (`next`, `drain`, or
/// `watch`). That is why an SDP this peer produced arrives as
/// `RtcEvent.local_description` rather than as a return value: a description
/// is only final once the browser says so.
///
/// **Signalling is the app's job.** WebRTC has no signalling channel of its
/// own. The app forwards `RtcEvent.local_description`/`local_candidate` over
/// whatever transport it already has (a WebSocket, an HTTP endpoint), and
/// hands the peer's reply back through `set_remote`/`add_ice`.
/// `web_event::rtc`'s `encode_sdp`/`decode_sdp` and `encode_ice`/`decode_ice`
/// are the wire shape for that hop, so both ends agree on one encoding.
///
/// Data channels are addressed by LABEL, the name both peers agreed on, so an
/// app can name one from a pure update without carrying a handle into its
/// model.
///
/// For an oak app, `Subscription.rtc` owns the peer and drains it for you;
/// this imperative surface is for an app with its own loop.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.of_list, ByteBuf.to_list}
use std::list {}
use lib::ffi {
    rtc_open_raw, rtc_peek_raw, rtc_read_raw, rtc_info_raw,
    rtc_set_local_raw, rtc_set_remote_raw, rtc_add_ice_raw, rtc_open_channel_raw,
    rtc_send_raw, rtc_add_stream_raw, rtc_close_raw,
    rtc_watch_raw, rtc_unwatch_raw, rtc_free_raw,
}
use lib::types {RtcPeer, MediaStream}
use web_event::rtc {
    RtcSdp, RtcIce, RtcData, RtcState, RtcEvent, RtcIceServer, RtcChannel,
    encode_sdp, decode_sdp, encode_ice, decode_ice, encode_ice_servers,
    decode_message_bytes, state_of_code,
}

// ─── Selector numbers ────────────────────────────────────────────────
//
// These are the `which` words `rtc_peek` and `rtc_info` read on the host
// side, and the kind numbers `rtc_peek`/`rtc_read` answer with. They are
// written once, here; `wasm/web/web_runtime.js` uses the same numbers and
// `rtc_tests.mo` pins them, so a host that renumbers a kind fails the suite
// instead of silently reporting the wrong event.

/// `rtc_peek`: the head entry's kind (0 = the queue is empty).
def peek_kind : I64 := 0i64

/// `rtc_peek`: the peer's live connection-state code.
def peek_connection : I64 := 1i64

/// `rtc_peek`: the head entry's payload length in bytes.
def peek_len : I64 := 2i64

/// `rtc_info`: the head entry's state code.
def info_state : I64 := 0i64

/// `rtc_info`: the data channel's `ordered` flag (0/1).
def info_ordered : I64 := 1i64

/// `rtc_info`: the data channel's `max_retransmits`.
def info_retransmits : I64 := 2i64

/// `rtc_info`: whether a message payload is bytes (1) or text (0).
def info_binary : I64 := 3i64

/// The queue's kind numbers, matched against `peek_kind`/`rtc_read`.
def kind_sdp : I64 := 1i64
def kind_ice : I64 := 2i64
def kind_connection : I64 := 3i64
def kind_channel : I64 := 4i64
def kind_channel_state : I64 := 5i64
def kind_message : I64 := 6i64

// ─── Lifecycle ───────────────────────────────────────────────────────

/// Create a peer connection. `servers` is what the browser offers ICE:
/// `[{ url := "stun:stun.example.org", username := "", credential := "" }]` is
/// the usual
/// minimum, and an empty list still connects two peers on one host.
pub def Rtc.connect (servers : List RtcIceServer) : IO RtcPeer :=
    IO.mk (rtc_open_raw (encode_ice_servers servers))

/// The connection's live state, without draining the queue.
///
/// Reads the peer's current `connectionState` rather than the last report in
/// the queue, so it is right even before the first `RtcEvent.connection` has
/// been drained. `RtcState.connection_name` spells it.
pub def Rtc.state (p : RtcPeer) : IO RtcState := do {
    let code <- IO.mk (rtc_peek_raw p peek_connection);
    IO.pure (state_of_code code)
}

/// Forget the peer and release its queue, closing it first if needed.
pub def Rtc.free (p : RtcPeer) : IO Unit := do {
    let _ <- IO.mk (rtc_free_raw p);
    IO.pure unit
}

// ─── Signalling in ───────────────────────────────────────────────────
//
// Each of these answers at the CALL, because `setLocalDescription` et al.
// are asynchronous in the browser: the host kicks off the promise and the
// result -- the description this peer produced, or the answer it built --
// arrives in the queue. `Result.err` here therefore means only "the browser
// refused the CALL", not "the description was rejected"; the latter shows up
// as `RtcEvent.connection RtcState.failed`.

/// Set a local description (the OFFERER's `offer`, or `"rollback"`).
///
/// `Err` when the browser rejects the type (`NotSupportedError`) or the peer
/// is closed (`InvalidStateError`).
pub def Rtc.set_local (p : RtcPeer) (d : RtcSdp) : IO (Result String Unit) := do {
    let ok <- IO.mk (rtc_set_local_raw p (encode_sdp d));
    if I64.beq ok 0i64
    then IO.pure (Result.err "the peer refused its local description")
    else IO.pure (Result.ok unit)
}

/// Hand the browser the OTHER peer's description. After an offer this makes
/// the browser build an answer, which arrives as
/// `RtcEvent.local_description`.
pub def Rtc.set_remote (p : RtcPeer) (d : RtcSdp) : IO (Result String Unit) := do {
    let ok <- IO.mk (rtc_set_remote_raw p (encode_sdp d));
    if I64.beq ok 0i64
    then IO.pure (Result.err "the peer refused the remote description")
    else IO.pure (Result.ok unit)
}

/// Add one ICE candidate learned from the other peer. The end-of-candidates
/// marker (a `candidate` of "") is accepted and forwarded as a `null`
/// candidate.
pub def Rtc.add_ice (p : RtcPeer) (c : RtcIce) : IO (Result String Unit) := do {
    let ok <- IO.mk (rtc_add_ice_raw p (encode_ice c));
    if I64.beq ok 0i64
    then IO.pure (Result.err "the peer refused the ICE candidate")
    else IO.pure (Result.ok unit)
}

// ─── Data channels ───────────────────────────────────────────────────

/// Open a data channel called `label`. The channel is NOT usable at the call:
/// its progress arrives as `RtcEvent.channel_state label state`, and it can
/// carry a message once that state is `RtcState.ready`.
///
/// `max_retransmits` is -1 for a reliable channel and `>= 0` for a partially
/// reliable one (`0` is unreliable). `Err` when the peer is closed.
pub def Rtc.create_data_channel (p : RtcPeer) (label : String) (ordered : Bool)
    (max_retransmits : I64) : IO (Result String Unit) := do {
    let reliable := I64.lt max_retransmits 0i64;
    let retrans := if reliable then 0i64 - 1i64 else max_retransmits;
    let flag := if ordered then 1i64 else 0i64;
    // `num` is `ordered` in bit 0 plus `max_retransmits + 1` above it, so a
    // reliable channel (-1) encodes as 0 and a partially reliable one keeps
    // its count. The host reverses exactly this.
    let num := I64.add flag (I64.mul 2i64 (I64.add retrans 1i64));
    let ok <- IO.mk (rtc_open_channel_raw p label num);
    if I64.beq ok 0i64
    then IO.pure (Result.err "the peer is closed")
    else IO.pure (Result.ok unit)
}

/// Send one message on the channel called `label`; `Err` when no channel with
/// that label is open on this peer.
pub def Rtc.send (p : RtcPeer) (label : String) (d : RtcData) : IO (Result String Unit) :=
    match d {
        RtcData.text s => Rtc.send_bytes p label (String.to_list s) 0i64,
        RtcData.binary b => Rtc.send_bytes p label b 1i64,
    }

/// Send raw bytes (`is_binary` 0 sends them as the UTF-8 text they are).
pub def Rtc.send_bytes (p : RtcPeer) (label : String) (bytes : List U8)
    (is_binary : I64) : IO (Result String Unit) := do {
    let buf <- ByteBuf.of_list bytes;
    let sb := Shared.of buf;
    let ok <- IO.mk (rtc_send_raw p label (Shared.get sb) is_binary);
    let _ <- ByteBuf.free buf;
    if I64.beq ok 0i64
    then IO.pure (Result.err "no open data channel with that label")
    else IO.pure (Result.ok unit)
}

/// Close the whole peer connection, and with it every channel on it.
pub def Rtc.close (p : RtcPeer) : IO Unit := do {
    let _ <- IO.mk (rtc_close_raw p);
    IO.pure unit
}

// ─── Media ───────────────────────────────────────────────────────────

/// Send `stream`'s tracks over the connection.
///
/// Call it BEFORE the offer is created: the tracks present when the browser
/// builds the offer are the ones its SDP describes, and this API does not
/// model renegotiation. `Err` when the peer is closed or the stream has no
/// tracks.
pub def Rtc.add_stream (p : RtcPeer) (stream : MediaStream) : IO (Result String Unit) := do {
    let ok <- IO.mk (rtc_add_stream_raw p stream);
    if I64.beq ok 0i64
    then IO.pure (Result.err "the stream has no tracks, or the peer is closed")
    else IO.pure (Result.ok unit)
}
// ─── Draining the queue ──────────────────────────────────────────────
//
// `rtc_read` is the POP: it copies the head entry's payload into the buffer
// it is given and removes the entry. So a drain step reads the head's KIND
// through `rtc_peek` and its columns through `rtc_info` first, then calls
// `rtc_read` exactly once -- whatever the kind, payload or none. Calling it
// twice would silently eat the next event; never calling it would wedge the
// queue. `Rtc.take_bytes` and `Rtc.take` are the only two call sites.

/// The queue's next event, `none` when it is empty.
///
/// An entry whose payload does not decode is dropped rather than surfaced:
/// `none` here means "nothing more this frame", which is what every caller's
/// drain loop already stops on.
pub def Rtc.next (p : RtcPeer) : IO (Option RtcEvent) := do {
    let kind <- IO.mk (rtc_peek_raw p peek_kind);
    if I64.beq kind 0i64
    then IO.pure Option.none
    else if I64.beq kind kind_sdp
    then Rtc.next_sdp p
    else if I64.beq kind kind_ice
    then Rtc.next_ice p
    else if I64.beq kind kind_connection
    then do {
        let code <- IO.mk (rtc_info_raw p info_state);
        let _ <- Rtc.take p;
        IO.pure (Option.some (RtcEvent.connection (state_of_code code)))
    }
    else if I64.beq kind kind_channel
    then do {
        let ordered <- IO.mk (rtc_info_raw p info_ordered);
        let retransmits <- IO.mk (rtc_info_raw p info_retransmits);
        let label <- Rtc.take_text p;
        let ch : RtcChannel := { label := label,
            ordered := I64.beq ordered 1i64, max_retransmits := retransmits };
        IO.pure (Option.some (RtcEvent.data_channel ch))
    }
    else if I64.beq kind kind_channel_state
    then do {
        let code <- IO.mk (rtc_info_raw p info_state);
        let label <- Rtc.take_text p;
        IO.pure (Option.some (RtcEvent.channel_state label (state_of_code code)))
    }
    else if I64.beq kind kind_message
    then Rtc.next_message p
    else do {
        // A kind this build does not know. Pop it (payload and all, so a stale
        // entry cannot wedge the queue) and report nothing.
        let _ <- Rtc.take p;
        IO.pure Option.none
    }
}

def Rtc.next_sdp (p : RtcPeer) : IO (Option RtcEvent) := do {
    let text <- Rtc.take_text p;
    match decode_sdp text {
        Option.none => IO.pure Option.none,
        Option.some d => IO.pure (Option.some (RtcEvent.local_description d)),
    }
}

def Rtc.next_ice (p : RtcPeer) : IO (Option RtcEvent) := do {
    let text <- Rtc.take_text p;
    match decode_ice text {
        Option.none => IO.pure Option.none,
        Option.some c => IO.pure (Option.some (RtcEvent.local_candidate c)),
    }
}

/// The body of a message entry as an `RtcData`, chosen by the host's binary
/// flag. A separate def rather than a `let ... := if ...` inside the drain
/// arm: a `let` binding a conditional does not parse as a do-block or
/// match-arm statement.
def message_data (is_binary : I64) (body : List U8) : RtcData :=
    if I64.beq is_binary 1i64
    then RtcData.binary body
    else RtcData.text (String.from_list body)

/// A message entry's payload is `<label length>:<label><body>` (see
/// `decode_message_bytes`), so one buffer carries both halves.
///
/// The split happens on the BYTES, not on a `String` made from them: a Monad
/// `String` is NUL-terminated, so decoding the payload through one would
/// truncate every binary frame at its first `0x00` and lose any non-UTF-8
/// byte. The label is text (the host wrote it); the body is not.
def Rtc.next_message (p : RtcPeer) : IO (Option RtcEvent) := do {
    let is_binary <- IO.mk (rtc_info_raw p info_binary);
    let raw <- Rtc.take_bytes p;
    match decode_message_bytes raw {
        Option.none => IO.pure Option.none,
        Option.some parts => match parts {
            Pair.pair label body =>
                IO.pure (Option.some (RtcEvent.message label (message_data is_binary body))),
        },
    }
}

// ─── The pops ────────────────────────────────────────────────────────

/// Pop the head entry and return its payload (`""` when it has none). An SDP,
/// a candidate blob and a data channel's label all cross as text.
def Rtc.take_text (p : RtcPeer) : IO String := do {
    let bytes <- Rtc.take_bytes p;
    IO.pure (String.from_list bytes)
}

/// Pop the head entry and return its payload's bytes.
///
/// The buffer is sized from the head's reported length, so a message larger
/// than the 64 KiB scratch string arrives whole. `rtc_read` answers how many
/// bytes it actually wrote, and the list is clamped to that.
def Rtc.take_bytes (p : RtcPeer) : IO (List U8) := do {
    let n <- IO.mk (rtc_peek_raw p peek_len);
    if Bool.not (I64.gt n 0i64)
    then do {
        let _ <- Rtc.take p;
        IO.pure List.empty
    }
    else do {
        let buf <- ByteBuf.alloc n;
        let sb := Shared.of buf;
        // The buffer is EXACTLY the peeked length and `rtc_read` clamps its
        // copy to the buffer it is given, so `n` is the whole payload and
        // `to_list`'s own clamp makes an over-large read impossible -- the
        // same contract `WebSocket.read_bytes` relies on. The call's return
        // (the entry's kind) is not needed: the caller already read it.
        let _ <- IO.mk (rtc_read_raw p (Shared.get sb));
        let bytes <- ByteBuf.to_list (Shared.get sb) n;
        let _ <- ByteBuf.free buf;
        IO.pure bytes
    }
}

/// Pop the head entry, discarding its payload. `rtc_read` is the pop, so an
/// entry whose columns were already read still needs exactly one call.
def Rtc.take (p : RtcPeer) : IO Unit := do {
    let buf <- ByteBuf.alloc 1i64;
    let sb := Shared.of buf;
    let _ <- IO.mk (rtc_read_raw p (Shared.get sb));
    ByteBuf.free buf
}

/// Every queued event, oldest first -- the per-frame poll a game loop wants.
#[terminating]
pub def Rtc.drain (p : RtcPeer) : IO (List RtcEvent) := do {
    let e <- Rtc.next p;
    match e {
        Option.none => IO.pure List.empty,
        Option.some ev => do {
            // `p` is `Copy` (a host table id), so the recursive call reuses it.
            let rest <- Rtc.drain p;
            IO.pure (List.cons ev rest)
        },
    }
}

/// Have the host dispatch `handler` (an oak handler id) when the queue gains
/// entries. One dispatch drains everything queued.
pub def Rtc.watch (p : RtcPeer) (handler : U32) : IO Unit := do {
    let _ <- IO.mk (rtc_watch_raw p handler);
    IO.pure unit
}

/// Stop the wake-ups (the queue keeps filling).
pub def Rtc.unwatch (p : RtcPeer) : IO Unit := do {
    let _ <- IO.mk (rtc_unwatch_raw p);
    IO.pure unit
}
