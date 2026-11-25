/// Opaque browser handles. A `Node` is a JS node id; a `RequestId` names an
/// in-flight two-phase fetch. Neither is ever constructed, matched or
/// compared; they only cross the extern boundary.
///
/// `CryptoOp` is the two-phase WebCrypto operation (`Crypto.sha256_begin`,
/// `WebCrypto.generate_key_begin`, ...); `WebKey` is an ECDSA P-256 keypair
/// produced by one of them. The key is an id into the HOST's table, so the
/// private material never enters wasm memory at all -- stronger than the
/// native OpenSSL path, where the scalar lives in a zeroised `CryptoSecret`.
///
/// `RtcPeer` is a live `RTCPeerConnection` and `MediaStreamOp` a two-phase
/// `getUserMedia`; both are host table ids for the same reason. `MediaStream`
/// is the one handle here marked `#[opaque]`: it is handed to a `<video>`
/// element as well as polled, so unlike an id there is no useful default
/// value source could spell.

pub type Node { node }
pub type RequestId { request_id }
pub type ClipboardOp { clipboard_op }
pub type CryptoOp { crypto_op }
pub type WebKey { web_key }

/// The handles are host ids, so sharing one is a bit-copy, not a move:
/// sizing a canvas and asking for its context both read the same `Node`,
/// and polling an operation reads it once per poll.
pub instance Copy Node {
    def copy (n : Node) : Pair Node Node := Pair.pair n n
}

pub instance Copy ClipboardOp {
    def copy (op : ClipboardOp) : Pair ClipboardOp ClipboardOp := Pair.pair op op
}

pub instance Copy CryptoOp {
    def copy (op : CryptoOp) : Pair CryptoOp CryptoOp := Pair.pair op op
}

/// A live browser `WebSocket`, as the host's table id (0 means null).
pub type WebSocket {
    web_socket
}

/// The id is a plain word; duplicating it copies the number.
pub instance Copy WebSocket {
    def copy (w : WebSocket) : Pair WebSocket WebSocket := Pair.pair w w
}

/// A live `RTCPeerConnection`, as the host's table id (0 means null).
///
/// The peer connection, its data channels and its tracks all live in the
/// HOST's table, so nothing the browser owns enters wasm memory: the value
/// here is one opaque word. What the peer reports arrives through its queue
/// (`lib::rtc`'s `Rtc.drain`), never through a callback that re-enters wasm.
pub type RtcPeer {
    rtc_peer
}

/// Polling a peer reads the same word each time, so sharing it is a copy.
pub instance Copy RtcPeer {
    def copy (p : RtcPeer) : Pair RtcPeer RtcPeer := Pair.pair p p
}

/// A live `MediaStream` -- a camera, a microphone, a screen capture, or the
/// stream a remote peer is sending -- as the host's table id.
///
/// `#[opaque]`, unlike the id-only handles above: this one is handed to a
/// `<video>` element (`MediaStream.attach`) as well as polled, so there is
/// no useful default value and no reason for source to spell one.
#[opaque]
pub type MediaStream {
    media_stream_witness
}

/// A stream is a HOST table id, so using it twice is a bit-copy of one
/// word, not a move of a resource: showing it (`MediaStream.attach`) and
/// then releasing it (`MediaStream.stop`) both read the same id, and an id
/// copied twice is still one stream. `stop` is what ends the camera, and it
/// is idempotent on the host side, so a duplicated handle cannot stop
/// another stream.
pub instance Copy MediaStream {
    def copy (s : MediaStream) : Pair MediaStream MediaStream := Pair.pair s s
}

/// A two-phase `getUserMedia` operation: `MediaStream.get_user_media_begin`
/// starts the permission prompt, `poll` answers 0 pending / 1 done / 2
/// failed, and the stream is read with `MediaStream.result` once it is done.
///
/// Promise-based like every `Crypto`/`Fetch`/`Clipboard` operation, and for
/// the same reason: a JS promise callback must not re-enter wasm while a
/// Monad frame is on the stack.
pub type MediaStreamOp {
    media_stream_op
}

pub instance Copy MediaStreamOp {
    def copy (op : MediaStreamOp) : Pair MediaStreamOp MediaStreamOp := Pair.pair op op
}
