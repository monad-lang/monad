/// IndexedDB-backed storage for a non-extractable `WebKey`.
///
/// This is the piece that makes a browser atproto login possible at all: the
/// page UNLOADS between the PAR request and the callback, so the DPoP key that
/// signs the token exchange (`ath`) must survive a full page reload. A
/// `CryptoKey` generated non-extractable cannot be serialised by anything
/// Monad-side, but IndexedDB stores it by STRUCTURED CLONE -- the browser
/// keeps the key material in its own (non-readable) form and hands back a
/// live handle on the next page. That is the pattern
/// `@atproto/oauth-client-browser` uses, and it is strictly safer than the
/// `localStorage` JWK fallback Phase 4 of the web-wasm-crypto plan records as
/// a risk: an XSS that reads `localStorage` steals a key; an XSS that reads
/// IndexedDB steals a handle the browser will not export.
///
/// Every operation is TWO-PHASE for the same reason `Fetch` is: an IndexedDB
/// request resolves in a promise callback, and re-entering wasm from one while
/// a Monad frame is on the stack is what the begin/poll shape exists to avoid.
/// `Crypto.poll` answers 0 = pending, 1 = done, 2 = failed, and for `get` one
/// more: 3 = done and the slot is EMPTY. That fourth state is why a miss is
/// not an error -- "this browser has no DPoP key for this DID" is the ordinary
/// answer on a first visit, and a caller must be able to tell it from a
/// rejected `get`.
///
/// The store is one object store named `keys`, one database named
/// `monad_keys`. A slot is the caller's opaque string -- an atproto driver
/// keys it by the DID, so one browser can hold several accounts' DPoP keys.

use lib::types {CryptoOp, WebKey}
use lib::crypto {Crypto.await_op, Crypto.op_key}
use lib::ffi {
    keystore_put_begin_raw, keystore_get_begin_raw, keystore_delete_begin_raw,
}

/// `get`'s "done, and the slot holds nothing" state.
pub def KeyStore.empty_state : I64 := 3

/// Store `k` under `slot`, replacing whatever was there.
///
/// Poll the result with `Crypto.poll`; there is nothing to read back. A
/// failed put is a real failure -- the key would not survive the redirect --
/// so a login flow must treat it as fatal rather than proceed and fail later
/// at the token exchange with an opaque `invalid_dpop_proof`.
pub def KeyStore.put_begin (slot : String) (k : WebKey) : IO CryptoOp :=
    IO.mk (keystore_put_begin_raw slot k)

/// Load the key stored under `slot`. Read it with `Crypto.op_key` once
/// `Crypto.poll` answers 1; `1` is the only state in which a key is there.
pub def KeyStore.get_begin (slot : String) : IO CryptoOp :=
    IO.mk (keystore_get_begin_raw slot)

/// Delete `slot`. Succeeds even when the slot was empty, so a logout does not
/// have to check first.
pub def KeyStore.delete_begin (slot : String) : IO CryptoOp :=
    IO.mk (keystore_delete_begin_raw slot)

/// `get_begin` with the present/absent question answered: `none` when the
/// slot is empty, `some key` when it holds one.
///
/// Drives the poll itself (`Crypto.await_op`), so it is for a caller that has
/// no frame loop of its own -- a callback's first frame, or a test. A UI
/// should use `get_begin` plus its own `Crypto.poll`; see `Crypto.await_op`
/// on why spinning starves a browser event loop.
///
/// Only state 1 reads a key. An empty slot (state 3) is `none`, and so is an
/// op that failed or was still pending when the budget ran out: in both of
/// those the host has produced no handle, so `Crypto.op_key` would answer the
/// null one rather than a key.
pub def KeyStore.get (slot : String) : IO (Option WebKey) := do {
    let op <- KeyStore.get_begin slot;
    let state <- Crypto.await_op op 64;
    if I64.beq state 1
    then do {
        let k <- Crypto.op_key op;
        IO.pure (Option.some k)
    }
    else IO.pure Option.none
}
