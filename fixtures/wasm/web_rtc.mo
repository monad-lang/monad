// WebRTC fixture: the oak `Subscription.rtc` and the imperative `web_wasm`
// peer connection, in the same shape as `web_socket.mo`.
//
// `wasm/web/smoke/rtc_smoke.mjs` installs a fake `RTCPeerConnection` and a
// fake `navigator.mediaDevices`, then checks: the subscription created a peer
// and reached `update` for each queued event, a data channel opened and
// carried a message both ways, a description and a candidate round-tripped
// through the codecs, and the two-phase `getUserMedia` resolved to a stream
// that was displayed with `srcObject`.
//
// This file is CHECKED by `scripts/check-wasm-target.sh` and BUILT by the
// smoke harness; both matter, because the C/JS half of a native is only
// proven by a compiled binary actually calling it.
#![mote { name := "oak_rtc", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.id_, Html.span, Html.text}
use oak::app {Command, Host, Program}
use oak::events {Subscription}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::rtc {
    Rtc.connect, Rtc.state, Rtc.close, Rtc.free, Rtc.set_local, Rtc.set_remote,
    Rtc.add_ice, Rtc.create_data_channel, Rtc.send, Rtc.drain,
}
use web_wasm::media_stream {
    MediaStream.request_av, MediaStream.poll, MediaStream.result, MediaStream.attach,
    MediaStream.stop, MediaStream.release,
}
use web_wasm::dom {Dom.create, Dom.append}
use web_wasm::console {Console.log}
use web_event::rtc {
    RtcSdp, RtcIce, RtcData, RtcEvent, RtcIceServer,
    RtcState.connection_name, RtcState.channel_name, RtcState.ready,
}
use std::list {}

// ── the oak app ────────────────────────────────────────────────────────

type Msg {
    rtc (ev : RtcEvent),
}

/// The model is a running tally, so a wrong event count is visible.
def init : I64 := 0i64

def bump (ev : RtcEvent) : I64 :=
    match ev {
        RtcEvent.connection _st => 1i64,
        RtcEvent.data_channel _ch => 10i64,
        RtcEvent.channel_state _label _st => 100i64,
        RtcEvent.message _label _data => 1000i64,
        RtcEvent.local_description _d => 10000i64,
        RtcEvent.local_candidate _c => 100000i64,
        RtcEvent.track _stream => 1i64,
    }

/// The update is pure: it never touches the peer. On a ready channel it
/// answers through `Command.rtc_send`, which is the whole point of the
/// subscription -- the app reacts to events without owning the peer.
def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.rtc ev =>
            match ev {
                RtcEvent.channel_state label state =>
                    match state {
                        RtcState.ready =>
                            Pair.pair (m + bump ev)
                                (Command.rtc_send "chat" label (RtcData.text "ping")),
                        _ => Pair.pair (m + bump ev) Command.none,
                    },
                _ => Pair.pair (m + bump ev) Command.none,
            },
    }

/// One peer per app, named "chat"; signalling is the app's job, so nothing
/// here forwards anything -- the harness drives the setters directly.
def subs (_m : I64) : List (Subscription Msg) :=
    [Subscription.rtc "chat" [] (fn (ev : RtcEvent) => Msg.rtc ev)]

def view (m : I64) : Oak.Node Msg :=
    Html.div [Html.id_ "app"] [Html.span [Html.id_ "count"] [Html.text (I64.to_string m)]]

def app : Program I64 Msg Unit := Program.with_subs init update view subs

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

// ── the imperative API, driven directly by the smoke test ──────────────
//
// The harness calls these exports after installing its fakes, and asserts on
// the log lines they write.

/// How many events of each kind the peer produced. The harness compares the
/// totals against what its fake browser sent.
def count_kind (events : List RtcEvent) (desc : I64) (cand : I64) (state : I64)
    (msg : I64) : List I64 :=
    match events {
        List.empty => [desc, cand, state, msg],
        List.cons ev rest =>
            match ev {
                RtcEvent.local_description _d => count_kind rest (I64.add desc 1i64) cand state msg,
                RtcEvent.local_candidate _c => count_kind rest desc (I64.add cand 1i64) state msg,
                RtcEvent.connection _st => count_kind rest desc cand (I64.add state 1i64) msg,
                RtcEvent.message _label _data => count_kind rest desc cand state (I64.add msg 1i64),
                RtcEvent.data_channel _ch => count_kind rest desc cand state msg,
                RtcEvent.channel_state _label _st => count_kind rest desc cand state msg,
                RtcEvent.track _stream => count_kind rest desc cand state msg,
            },
    }

def sum (xs : List I64) : I64 :=
    match xs {
        List.empty => 0i64,
        List.cons x rest => I64.add x (sum rest),
    }

#[export "c"]
def imp_offer : IO Unit := do {
    let peer <- Rtc.connect [];
    let _ <- Rtc.create_data_channel peer "chat" true (0i64 - 1i64);
    let offer : RtcSdp := { kind := "offer",
        text := "v=0\r\no=- 1 2 IN IP4 127.0.0.1\r\n" };
    let _ <- Rtc.set_local peer offer;
    let events <- Rtc.drain peer;
    let counts := count_kind events 0i64 0i64 0i64 0i64;
    Console.log (String.concat "offer:events=" (I64.to_string (sum counts)));
    let _ <- Rtc.close peer;
    Rtc.free peer
}

/// The answerer's half: take an offer the harness supplies, set it remote,
/// set the answer local, add a candidate, then report the live state.
#[export "c"]
def imp_answer : IO Unit := do {
    let peer <- Rtc.connect [];
    let offer : RtcSdp := { kind := "offer", text := "v=0\r\n" };
    let _ <- Rtc.set_remote peer offer;
    let answer : RtcSdp := { kind := "answer", text := "v=0\r\n" };
    let _ <- Rtc.set_local peer answer;
    let candidate : RtcIce := { candidate := "candidate:1 1 udp 1 127.0.0.1 9 typ host",
        sdp_mid := "0", sdp_mline_index := 0i64, username_fragment := "abcd" };
    let _ <- Rtc.add_ice peer candidate;
    let end_marker : RtcIce := { candidate := "", sdp_mid := "",
        sdp_mline_index := 0i64 - 1i64, username_fragment := "" };
    let _ <- Rtc.add_ice peer end_marker;
    let events <- Rtc.drain peer;
    let counts := count_kind events 0i64 0i64 0i64 0i64;
    Console.log (String.concat "answer:events=" (I64.to_string (sum counts)));
    let state <- Rtc.state peer;
    Console.log (String.concat "answer:state=" (RtcState.connection_name state));
    Rtc.free peer
}

/// Send a text frame and a binary frame on an open channel, and report what
/// came back.
#[export "c"]
def imp_send : IO Unit := do {
    let peer <- Rtc.connect [];
    let _ <- Rtc.create_data_channel peer "chat" true (0i64 - 1i64);
    let sent_text <- Rtc.send peer "chat" (RtcData.text "hello");
    let sent_bytes <- Rtc.send peer "chat" (RtcData.binary [1u8, 2u8, 3u8]);
    let text_ok := match sent_text { Result.ok _ => 1i64, Result.err _ => 0i64 };
    let bytes_ok := match sent_bytes { Result.ok _ => 1i64, Result.err _ => 0i64 };
    Console.log (String.concat "send:text=" (I64.to_string text_ok));
    Console.log (String.concat "send:bytes=" (I64.to_string bytes_ok));
    Rtc.free peer
}

/// The camera half: begin a request, poll to completion, show the stream in a
/// `<video>`, then stop it.
#[export "c"]
def imp_camera : IO Unit := do {
    let op <- MediaStream.request_av;
    let state <- MediaStream.poll op;
    Console.log (String.concat "camera:poll=" (I64.to_string state));
    if I64.beq state 1i64
    then do {
        let stream <- MediaStream.result op;
        let video <- Dom.create "video";
        let shown <- MediaStream.attach stream video;
        let ok := match shown { Result.ok _ => 1i64, Result.err _ => 0i64 };
        Console.log (String.concat "camera:attach=" (I64.to_string ok));
        // Showing the stream and then stopping it are both reads of one host
        // id, which `MediaStream`'s Copy instance licenses.
        MediaStream.stop stream
    }
    else IO.pure unit
}

/// The null handle must be REFUSED. Index 0 of the host's stream table is
/// reserved so that "no stream yet" (`MediaStream.result` before `poll`
/// answers 1) is a handle nothing accepts -- otherwise it would name the
/// first live stream and `attach` would bind the wrong one.
///
/// Reported as two lines: `null:attach=<0|1>` for the pending op's handle
/// and `null:stop=1` for the call itself, which always returns unit.
#[export "c"]
def imp_null_handle : IO Unit := do {
    // Deliberately NOT polled: the op is still pending, so `result` answers
    // the null handle.
    let pending <- MediaStream.request_av;
    let unborn <- MediaStream.result pending;
    let video <- Dom.create "video";
    let shown <- MediaStream.attach unborn video;
    let ok := match shown { Result.ok _ => 1i64, Result.err _ => 0i64 };
    Console.log (String.concat "null:attach=" (I64.to_string ok));
    MediaStream.release pending
}

/// A channel that is not open must report a failure rather than throw.
#[export "c"]
def imp_closed_send : IO Unit := do {
    let peer <- Rtc.connect [];
    let outcome <- Rtc.send peer "nope" (RtcData.text "x");
    let ok := match outcome { Result.ok _ => 1i64, Result.err _ => 0i64 };
    Console.log (String.concat "closed:send=" (I64.to_string ok));
    Rtc.free peer
}
