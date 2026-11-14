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
