// The Phase-1 web surface, end to end: presence-aware storage, monotonic
// clock, media queries, hit testing + attribute reads, random bytes,
// request headers, memory introspection, and a two-phase SHA-256 that the
// harness finishes from a second export.
//
// `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/new_surface_smoke.mjs` drives the real `web_runtime.js` over a
// stub DOM/globals.

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
}
use web_wasm::fetch {Fetch.begin_with}
use web_wasm::memory {Memory.heap_bytes, Memory.heap_used}
use web_wasm::window {Window.navigate, Window.reload}
use web_wasm::keep {Keep.save, Keep.load}
use web_wasm::types {CryptoOp}
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

    let line : String := String.concat_list [
        report "storage" storage_ok,
        report "clock" (I64.beq mono 1234i64),
        report "media" (dark && Bool.not light),
        report "hit" (String.beq cell "7"),
        report "memory" (I64.gt heap 0i64 && I64.gt used 0i64),
        report "random" random_ok,
    ];

    let report_node <- Dom.create "span";
    let _ <- Dom.set_attr report_node "id" "report";
    let summary <- Dom.text_node line;
    let _ <- Dom.append report_node summary;
    let _ <- Dom.append root report_node;
    return unit
}
