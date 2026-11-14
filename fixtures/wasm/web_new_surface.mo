// The Phase-1 web surface, end to end: presence-aware storage, monotonic
// clock, media queries, hit testing + attribute reads, random bytes,
// request headers, memory introspection, a two-phase SHA-256 that the harness
// finishes from a second export, and the atproto login surface -- ECDSA
// P-256 (generate / public JWK / raw point / sign), the `location` reads a
// redirect delivers its result in, and the IndexedDB key store that carries a
// DPoP key across the redirect.
//
// `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/new_surface_smoke.mjs` drives the real `web_runtime.js` over a
// stub DOM/globals with Node's real `crypto.subtle`, so the signature this
// produces is VERIFIED by an independent implementation.

#![mote { name := "web_new_surface", deps := [web_wasm] }]

use web_wasm::storage {Storage.set, Storage.has, Storage.get_raw, Storage.remove}
use web_wasm::clock {Clock.monotonic_ms}
use web_wasm::media {Media.matches}
use web_wasm::dom {
    Dom.root, Dom.create, Dom.set_attr, Dom.text_node, Dom.append,
    Dom.element_at, Dom.attr,
}
use web_wasm::crypto {
    Crypto.random_bytes, Crypto.sha256_begin, Crypto.poll, Crypto.result_hex,
    Crypto.op_key, Crypto.error,
    WebCrypto.generate_key_begin, WebCrypto.export_public_jwk_begin,
    WebCrypto.export_public_raw_begin, WebCrypto.sign_begin,
}
use web_wasm::keystore {
    KeyStore.put_begin, KeyStore.get_begin, KeyStore.delete_begin,
}
use web_wasm::fetch {Fetch.begin_with}
use web_wasm::memory {Memory.heap_bytes, Memory.heap_used}
use web_wasm::window {
    Window.navigate, Window.reload, Window.replace, Window.origin,
    Window.pathname, Window.search, Window.search_param,
}
use web_wasm::keep {Keep.save, Keep.load}
use web_wasm::types {CryptoOp, WebKey}
use std::bytebuf {ByteBuf, ByteBuf.of_string, ByteBuf.free}
use std::ref {Ref, Ref.new, Ref.get}
use std::list {}

def report (label : String) (ok : Bool) : String :=
    if ok then String.concat label "=ok " else String.concat label "=FAIL "

/// One exported step that starts a SHA-256 over "abc" and stashes the op.
#[export "c"]
def sha_begin : IO Unit := do {
    let buf <- ByteBuf.of_string "abc";
    let op <- Crypto.sha256_begin buf;
    let _ <- ByteBuf.free buf;
    let r <- Ref.new op;
    let _ <- Keep.save r;
    return unit
}

/// The second half: poll the stashed op and, once done, append the hex.
#[export "c"]
def sha_finish : IO Unit := do {
    let r : Ref CryptoOp <- Keep.load;
    let op <- Ref.get r;
    let state <- Crypto.poll op;
    if I64.beq state 1
    then do {
        let hex <- Crypto.result_hex op;
        let n <- Dom.create "span";
        let _ <- Dom.set_attr n "id" "sha";
        let t <- Dom.text_node hex;
        let _ <- Dom.append n t;
        let root <- Dom.root;
        let _ <- Dom.append root n;
        return unit
    }
    else IO.pure unit
}

// ─── ECDSA P-256, driven a step at a time ───
//
// Every WebCrypto call is two-phase, so the harness advances them: a `*_start`
// export begins one op, a `*_ready` export polls it and appends the result to a
// span. Splitting them (rather than looping inside one export) is what keeps a
// promise callback from re-entering wasm while a Monad frame is on the stack --
// an in-wasm spin would deadlock, because JS cannot settle the promise until
// the export returns.
//
// `Keep` holds exactly ONE word, so the state is a `Ref` to a pair: the op in
// flight and the keypair handle. Both are opaque extern handles, which is why
// the pair has to be built from their (unreferenceable) witness constructors --
// this fixture is the one place that is legitimate, since it is standing in for
// the host's own bookkeeping.

struct EcdsaState {
    op : CryptoOp,
    key : WebKey,
}

def dummy_state : EcdsaState :=
    { op := CryptoOp.crypto_op, key := WebKey.web_key }

/// Create the state cell. Called once, before any key operation.
#[export "c"]
def ecdsa_init : IO Unit := do {
    let cell <- Ref.new dummy_state;
    let _ <- Keep.save cell;
    return unit
}

def get_state : IO EcdsaState := do {
    let cell : Ref EcdsaState <- Keep.load;
    Ref.get cell
}

def put_state (st : EcdsaState) : IO Unit := do {
    let cell : Ref EcdsaState <- Keep.load;
    Ref.set cell st
}

def store_op (op : CryptoOp) : IO Unit := do {
    let st <- get_state;
    let next : EcdsaState := { st with op := op };
    put_state next
}

def store_key (k : WebKey) : IO Unit := do {
    let st <- get_state;
    let next : EcdsaState := { st with key := k };
    put_state next
}

def stored_op : IO CryptoOp := do {
    let st <- get_state;
    IO.pure st.op
}

def stored_key : IO WebKey := do {
    let st <- get_state;
    IO.pure st.key
}

/// Append `span#<id>` with `text` once the op is done, or nothing while it
/// is still pending.
def emit_if_done (op : CryptoOp) (id : String) : IO Unit := do {
    let state <- Crypto.poll op;
    if I64.beq state 1
    then do {
        let text <- Crypto.result_hex op;
        let _ <- append_span id text;
        return unit
    }
    else IO.pure unit
}

/// Start a P-256 keypair.
#[export "c"]
def ecdsa_generate : IO Unit := do {
    let op <- WebCrypto.generate_key_begin;
    store_op op
}

/// Poll the generated key: on success stash the HANDLE in the state cell.
#[export "c"]
def ecdsa_key_ready : IO Unit := do {
    let op <- stored_op;
    let state <- Crypto.poll op;
    if I64.beq state 1
    then do {
        let k <- Crypto.op_key op;
        store_key k;
        append_span "key" "ready"
    }
    else do {
        let e <- Crypto.error op;
        append_span "key" (if String.is_empty e then "pending" else e)
    }
}

#[export "c"]
def ecdsa_export_jwk : IO Unit := do {
    let k <- stored_key;
    let op <- WebCrypto.export_public_jwk_begin k;
    store_op op
}

#[export "c"]
def ecdsa_jwk_ready : IO Unit := do {
    let op <- stored_op;
    emit_if_done op "jwk"
}

#[export "c"]
def ecdsa_export_raw : IO Unit := do {
    let k <- stored_key;
    let op <- WebCrypto.export_public_raw_begin k;
    store_op op
}

#[export "c"]
def ecdsa_raw_ready : IO Unit := do {
    let op <- stored_op;
    emit_if_done op "raw"
}

/// Sign "dpop-test-message" with ES256.
#[export "c"]
def ecdsa_sign : IO Unit := do {
    let k <- stored_key;
    let buf <- ByteBuf.of_string "dpop-test-message";
    let op <- WebCrypto.sign_begin k buf;
    let _ <- ByteBuf.free buf;
    store_op op
}

#[export "c"]
def ecdsa_sig_ready : IO Unit := do {
    let op <- stored_op;
    emit_if_done op "sig"
}

// ─── IndexedDB: a DPoP key surviving the redirect ───

#[export "c"]
def keystore_put : IO Unit := do {
    let k <- stored_key;
    let op <- KeyStore.put_begin "did:plc:test" k;
    store_op op
}

#[export "c"]
def keystore_put_ready : IO Unit := do {
    let op <- stored_op;
    let state <- Crypto.poll op;
    append_span "put" (I64.to_string state)
}

#[export "c"]
def keystore_get : IO Unit := do {
    let op <- KeyStore.get_begin "did:plc:test";
    store_op op
}

/// Poll the load; when it found the key, sign with the RESTORED handle -- the
/// real test is that a key round-tripped through IndexedDB still signs.
#[export "c"]
def keystore_get_ready : IO Unit := do {
    let op <- stored_op;
    let state <- Crypto.poll op;
    let _ <- append_span "get" (I64.to_string state);
    if I64.beq state 1
    then do {
        let k <- Crypto.op_key op;
        let buf <- ByteBuf.of_string "dpop-test-message";
        let sop <- WebCrypto.sign_begin k buf;
        let _ <- ByteBuf.free buf;
        store_op sop;
        return unit
    }
    else IO.pure unit
}

#[export "c"]
def keystore_sig_ready : IO Unit := do {
    let op <- stored_op;
    emit_if_done op "restored_sig"
}

/// A slot that was never written: state 3 (empty), not an error.
#[export "c"]
def keystore_get_missing : IO Unit := do {
    let op <- KeyStore.get_begin "did:plc:absent";
    store_op op
}

#[export "c"]
def keystore_missing_ready : IO Unit := do {
    let op <- stored_op;
    let state <- Crypto.poll op;
    append_span "missing" (I64.to_string state)
}

// ─── A timed-out await must not read as "done" ───
//
// A promise cannot settle while an export is on the stack, so `Crypto.await_op`
// started and finished INSIDE one export always exhausts its budget. That makes
// the timeout path deterministic to reach from here -- and the answer must stay
// 0 (pending), NOT 1 (done): 1 is what every caller tests for completion, so a
// timeout reported as 1 makes `KeyStore.get` answer `some` for the null handle
// and a caller sign with key 0.

/// Begin a `get` for a slot that is empty and await it in the SAME export: the
/// budget runs out, so the state must still read as pending.
#[export "c"]
def keystore_await_timeout : IO Unit := do {
    let op <- KeyStore.get_begin "did:plc:await";
    let state <- Crypto.await_op op 8i64;
    append_span "await_timeout" (I64.to_string state)
}

/// Append a `span#<id>` holding `text` to the root, so the harness can read it.
def append_span (id : String) (text : String) : IO Unit := do {
    let root <- Dom.root;
    let n <- Dom.create "span";
    let _ <- Dom.set_attr n "id" id;
    let t <- Dom.text_node text;
    let _ <- Dom.append n t;
    let _ <- Dom.append root n;
    return unit
}

def main : IO Unit := do {
    let root <- Dom.root;

    let _ <- Storage.set "probe-key" "probe-value";
    let has_key <- Storage.has "probe-key";
    let got <- Storage.get_raw "probe-key";
    let _ <- Storage.set "empty-key" "";
    let empty <- Storage.get_raw "empty-key";
    let _ <- Storage.remove "probe-key";
    let gone <- Storage.has "probe-key";

    let storage_ok : Bool :=
        has_key && Bool.not gone
            && (match got { Option.some v => String.beq v "probe-value", Option.none => false })
            && (match empty { Option.some v => String.is_empty v, Option.none => false });

    let mono <- Clock.monotonic_ms;
    let dark <- Media.matches "dark";
    let light <- Media.matches "light";

    let hit <- Dom.element_at 10.0 20.0;
    let cell <- Dom.attr hit "data-cell";
    let heap <- Memory.heap_bytes;
    let used <- Memory.heap_used;

    let rand <- Crypto.random_bytes 16;
    let random_ok : Bool :=
        match rand { Result.ok bs => I64.beq (List.length bs) 16, Result.err _ => false };

    let _req <- Fetch.begin_with "https://example.test/echo" 1i64 "body"
        [Pair.pair "Authorization" "Bearer token", Pair.pair "Content-Type" "application/json"];

    // Navigation/reload are the escape hatch for a heap-pressure reload; the
    // stub records both instead of unloading.
    let _ <- Window.navigate "https://example.test/next";
    let _ <- Window.reload;

    // A browser OAuth redirect delivers `code`/`state`/`iss` in the URL, so
    // these are the reads an atproto login starts with. `search_param` must
    // percent-decode: the stub serves `state=a%20b` and `code` unpadded.
    let origin <- Window.origin;
    let pathname <- Window.pathname;
    let search <- Window.search;
    let state <- Window.search_param "state";
    let code <- Window.search_param "code";
    let absent <- Window.search_param "nope";
    let location_ok : Bool :=
        String.beq origin "https://app.test"
            && String.beq pathname "/callback"
            && String.contains search "state="
            && (match state { Option.some v => String.beq v "a b", Option.none => false })
            && (match code { Option.some v => String.beq v "abc-def_ghi", Option.none => false })
            && (match absent { Option.none => true, Option.some _ => false });

    let _ <- Window.replace "https://app.test/done";

    let line : String := String.concat_list [
        report "storage" storage_ok,
        report "clock" (I64.beq mono 1234i64),
        report "media" (dark && Bool.not light),
        report "hit" (String.beq cell "7"),
        report "memory" (I64.gt heap 0i64 && I64.gt used 0i64),
        report "random" random_ok,
        report "location" location_ok,
    ];

    let report_node <- Dom.create "span";
    let _ <- Dom.set_attr report_node "id" "report";
    let summary <- Dom.text_node line;
    let _ <- Dom.append report_node summary;
    let _ <- Dom.append root report_node;
    return unit
}
