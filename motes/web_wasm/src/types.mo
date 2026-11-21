/// Opaque browser handles. A `Node` is a JS node id; a `RequestId` names an
/// in-flight two-phase fetch. Neither is ever constructed, matched or
/// compared; they only cross the extern boundary.
///
/// `CryptoOp` is the two-phase WebCrypto operation (`Crypto.sha256_begin`,
/// `WebCrypto.generate_key_begin`, ...); `WebKey` is an ECDSA P-256 keypair
/// produced by one of them. The key is an id into the HOST's table, so the
/// private material never enters wasm memory at all -- stronger than the
/// native OpenSSL path, where the scalar lives in a zeroised `CryptoSecret`.

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
