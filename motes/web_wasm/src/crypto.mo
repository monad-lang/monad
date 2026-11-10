/// WebCrypto. Random bytes are synchronous (`crypto.getRandomValues`) and
/// fill a caller-owned `ByteBuf`; SHA-256 is two-phase, because a promise
/// callback must not re-enter wasm.
///
/// Hex is the string encoding of a digest: a Monad `String` is
/// NUL-terminated, so arbitrary bytes cannot travel in one. PKCE/atproto
/// callers base64url-encode the hex-decoded bytes (`std::base64`).

use lib::types {CryptoOp}
use lib::ffi {
    crypto_random_fill_raw, crypto_sha256_begin_raw, crypto_poll_raw,
    crypto_result_hex_raw,
}
use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.to_list}

/// `n` random bytes, or an error when the host has no
/// `crypto.getRandomValues` (an insecure context).
pub def Crypto.random_bytes (n : I64) : IO (Result String (List U8)) := do {
    if I64.lt n 1
    then IO.pure (Result.ok List.empty)
    else do {
        let buf <- ByteBuf.alloc n;
        let ok <- IO.mk (crypto_random_fill_raw buf);
        if I64.beq ok 0
        then do {
            let _ <- ByteBuf.free buf;
            IO.pure (Result.err "crypto.getRandomValues is unavailable")
        }
        else do {
            let xs <- ByteBuf.to_list buf n;
            let _ <- ByteBuf.free buf;
            IO.pure (Result.ok xs)
        }
    }
}

/// Start a SHA-256 digest over the buffer's bytes; poll it with `poll`.
pub def Crypto.sha256_begin (data : ByteBuf) : IO CryptoOp :=
    IO.mk (crypto_sha256_begin_raw data)

/// 0 = pending, 1 = done, 2 = failed (the fetch/clipboard convention).
pub def Crypto.poll (op : CryptoOp) : IO I64 := IO.mk (crypto_poll_raw op)

/// The lowercase hex digest, readable once `poll` answers 1.
pub def Crypto.result_hex (op : CryptoOp) : IO String :=
    IO.mk (crypto_result_hex_raw op)
