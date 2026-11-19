/// WebCrypto: a CSPRNG, SHA-256, and ECDSA P-256.
///
/// Random bytes are synchronous (`crypto.getRandomValues`) and fill a
/// caller-owned `ByteBuf`. Everything promise-based is TWO-PHASE, because a
/// JS promise callback must not re-enter wasm while a Monad frame is on the
/// stack: `*_begin` starts the operation and returns a `CryptoOp`, and the
/// caller drives `Crypto.poll` from its own frame loop. 0 = pending,
/// 1 = done, 2 = failed (the same convention `Fetch` uses).
///
/// `WebCrypto` is the ECDSA P-256 half an atproto / DPoP login needs: a
/// keypair, its public JSON Web Key (for the RFC 7638 `jkt` thumbprint and the
/// client-metadata document), its raw 65-byte public point (for a multikey /
/// DID document), and a signature. The private key is an id into the HOST's
/// table -- it never enters wasm memory, so there is nothing here to leak.
///
/// WebCrypto's ECDSA output is already IEEE P1363 `r‖s`, which IS the JWS
/// form, so no DER conversion is needed on this path (`motes/crypto`'s
/// `Der.ecdsa_raw_to_der` is a NATIVE-only need). WebCrypto does not
/// guarantee low-S; JWS ES256 does not require it and DPoP servers accept
/// either form, so this is recorded rather than normalised.
///
/// Hex is the string encoding of every byte result: a Monad `String` is
/// NUL-terminated, so arbitrary bytes cannot travel in one. `std::hex` and
/// `std::base64` decode them at the call site.

use lib::types {CryptoOp, WebKey}
use lib::ffi {
    crypto_random_fill_raw, crypto_sha256_begin_raw, crypto_poll_raw,
    crypto_result_hex_raw, crypto_error_raw, crypto_op_key_raw,
    ecdsa_generate_begin_raw, ecdsa_export_jwk_begin_raw,
    ecdsa_export_raw_begin_raw, ecdsa_sign_begin_raw,
}
use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.to_list}

/// `n` random bytes, or an error when the host has no
/// `crypto.getRandomValues` (an insecure context).
pub def Crypto.random_bytes (n : I64) : IO (Result String (List U8)) := do {
    if I64.lt n 1
    then IO.pure (Result.ok List.empty)
    else do {
        let buf <- ByteBuf.alloc n;
        let bs := Shared.of buf;
        let ok <- IO.mk (crypto_random_fill_raw (Shared.get bs));
        if I64.beq ok 0
        then do {
            let _ <- ByteBuf.free buf;
            IO.pure (Result.err "crypto.getRandomValues is unavailable")
        }
        else do {
            let xs <- ByteBuf.to_list (Shared.get bs) n;
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

/// The host's error name (`NotSupportedError`, `InvalidAccessError`, ...),
/// or `""` when the operation has not failed. The WebCrypto DOMException
/// name is the useful half: "generateKey returned a rejected promise" is
/// not a diagnosable message.
pub def Crypto.error (op : CryptoOp) : IO String :=
    IO.mk (crypto_error_raw op)

/// The ECDSA keypair a `WebCrypto.generate_key_begin` (or
/// `KeyStore.get_begin`) produced, readable once `poll` answers 1.
///
/// A separate step because `generateKey` is asynchronous: the handle does
/// not exist until the promise resolves, so a caller polls first and reads
/// the key second.
pub def Crypto.op_key (op : CryptoOp) : IO WebKey :=
    IO.mk (crypto_op_key_raw op)

/// Poll until the operation is no longer pending, up to `max_ticks` yields.
///
/// A convenience for a caller with no frame loop of its own (a test driver,
/// or a one-shot command). The answers are `Crypto.poll`'s own states,
/// unchanged: 1 when it completed, 2 when it failed, and 0 when the budget ran
/// out with the op STILL PENDING.
///
/// A budget that runs out answering `1` is the mistake this shape exists to
/// avoid: `1` is what every caller tests for completion, so a timeout would
/// read as a finished operation whose result is not there yet -- and
/// `KeyStore.get`, which reads a key handle once the state is 1, would answer
/// `some` for the null handle. `0` cannot be misread that way, because every
/// caller already handles it: it is what the first poll of any operation
/// answers.
///
/// A UI MUST drive `Crypto.poll` from its own frame loop instead. This spins
/// inside ONE export, and a promise cannot settle while an export is on the
/// stack, so in a browser every call here can only time out; the spin is for
/// an op that settled between two exports.
#[terminating]
pub def Crypto.await_op (op : CryptoOp) (max_ticks : I64) : IO I64 :=
    Crypto.await_op_go op max_ticks 0

#[terminating]
def Crypto.await_op_go (op : CryptoOp) (max_ticks : I64) (tick : I64) : IO I64 := do {
    let state <- Crypto.poll op;
    if I64.beq state 0
    then
        if I64.gt tick max_ticks
        then IO.pure state
        else Crypto.await_op_go op max_ticks (I64.add tick 1)
    else IO.pure state
}

// ─── ECDSA P-256 ─────────────────────────────────────────────────────

/// Start generating an ECDSA P-256 keypair. It is NON-EXTRACTABLE and
/// signing-only: the host can sign with it and export its PUBLIC half, and
/// nothing can export the private scalar. Read the handle with `op_key`
/// once `poll` answers 1.
pub def WebCrypto.generate_key_begin : IO CryptoOp :=
    IO.mk ecdsa_generate_begin_raw

/// Export the keypair's public half as a JSON Web Key (`{"kty":"EC",
/// "crv":"P-256","x":...,"y":...}`). The result is JSON TEXT, so it is read
/// with `Crypto.result_hex` like every other string result -- the name is
/// the existing reader's, not a claim that a JWK is hex.
pub def WebCrypto.export_public_jwk_begin (k : WebKey) : IO CryptoOp :=
    IO.mk (ecdsa_export_jwk_begin_raw k)

/// Export the public half as the raw 65-byte SEC1 point
/// (`0x04 ‖ X ‖ Y`), hex-encoded. This is what a `did:key`/multikey needs.
pub def WebCrypto.export_public_raw_begin (k : WebKey) : IO CryptoOp :=
    IO.mk (ecdsa_export_raw_begin_raw k)

/// Sign `data` with the keypair: ES256 (ECDSA over SHA-256), returning the
/// 64-byte IEEE P1363 `r ‖ s` signature, hex-encoded -- already the JWS form.
pub def WebCrypto.sign_begin (k : WebKey) (data : ByteBuf) : IO CryptoOp :=
    IO.mk (ecdsa_sign_begin_raw k data)
