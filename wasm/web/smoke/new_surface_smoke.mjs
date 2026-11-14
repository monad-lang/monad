#!/usr/bin/env node
// Node smoke test for the web surface. Usage:
//   node wasm/web/smoke/new_surface_smoke.mjs <web_new_surface.wasm>
//
// Drives the REAL `wasm/web/web_runtime.js` and generated `web.js` over the
// stub DOM/globals: storage presence/removal, monotonic clock, media query,
// hit test + attribute read, random bytes, request headers, memory probes,
// a two-phase SHA-256 completed through a second export, and the atproto
// login surface -- ECDSA P-256 (generate, public JWK, raw point, sign), the
// `location` reads a redirect delivers its result in, and the IndexedDB key
// store that carries a DPoP key across that redirect.
//
// Node's `crypto.subtle` is the REAL WebCrypto, so the signature this file
// checks is verified by an independent implementation rather than by the
// code that produced it.

import { readFile } from 'node:fs/promises';
import { webcrypto } from 'node:crypto';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { FakeNode, body, installDocument, fail, stub } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/smoke/new_surface_smoke.mjs <web_new_surface.wasm>');
  process.exit(2);
}

installDocument();

const cell = new FakeNode(1, 'DIV');
cell.setAttribute('data-cell', '7');
body.appendChild(cell);
stub.elementAt = cell;
stub.mediaMatches = { dark: true };
stub.performanceNow = 1234;

let fetchInit = null;
globalThis.fetch = (_url, init) => {
  fetchInit = init;
  return new Promise(() => {}); // pending forever; the fixture only starts it
};

// `location` with a query string, the shape an OAuth callback lands on:
// `state` is percent-encoded (the space must survive), `code` is the
// base64url form atproto sends (no padding, and `-`/`_` in the alphabet).
const CALLBACK_SEARCH =
  '?code=abc-def_ghi&state=a%20b&iss=https%3A%2F%2Fauth.test';
Object.assign(globalThis.location, {
  origin: 'https://app.test',
  pathname: '/callback',
  search: CALLBACK_SEARCH,
  href: 'https://app.test/callback' + CALLBACK_SEARCH,
  replaced: null,
  replace(url) { this.replaced = String(url); },
});

// A minimal in-memory IndexedDB, enough for the `monad_keys`/`keys` shape the
// runtime uses: `open` -> onupgradeneeded/onsuccess, then a transaction with
// one `get`/`put`/`delete` request. Values are kept by reference, which is
// exactly what structured clone does for a CryptoKey.
//
// `db.close()` is tracked, and every `open` must be answered by exactly one
// close: a real `IDBDatabase` lives until the page unloads, so a runtime that
// opens one per keystore call leaks a connection per call AND blocks any later
// schema upgrade. `assertConnectionsClosed` below is what makes that a test
// failure rather than a slow leak nobody notices.
const idbData = new Map();
const idbConnections = { opened: 0, closed: 0 };
function installIndexedDB() {
  globalThis.indexedDB = {
    open() {
      const req = { result: null, error: null, onsuccess: null, onerror: null, onupgradeneeded: null };
      idbConnections.opened += 1;
      const db = {
        objectStoreNames: { contains: () => true },
        createObjectStore: () => {},
        close() {
          idbConnections.closed += 1;
        },
        transaction() {
          const tx = { error: null, oncomplete: null, onerror: null, onabort: null };
          tx.objectStore = () => ({
            get(key) {
              const r = { result: idbData.get(key), error: null, onsuccess: null };
              queueMicrotask(() => { if (r.onsuccess) r.onsuccess(); });
              return r;
            },
            put(value, key) {
              idbData.set(key, value);
              queueMicrotask(() => { if (tx.oncomplete) tx.oncomplete(); });
              return {};
            },
            delete(key) {
              idbData.delete(key);
              queueMicrotask(() => { if (tx.oncomplete) tx.oncomplete(); });
              return {};
            },
          });
          return tx;
        },
      };
      req.result = db;
      queueMicrotask(() => {
        if (req.onupgradeneeded) req.onupgradeneeded();
        if (req.onsuccess) req.onsuccess();
      });
      return req;
    },
  };
}
installIndexedDB();

// Every `open` must be matched by a `close`. Called after the last keystore
// operation, so the count covers put + get + the absent-slot get.
function assertConnectionsClosed() {
  if (idbConnections.opened === 0) fail('the keystore never opened a connection');
  if (idbConnections.closed !== idbConnections.opened) {
    fail(
      `the keystore closed ${idbConnections.closed} of ${idbConnections.opened} IndexedDB ` +
        'connections: an unclosed one leaks until the page unloads and blocks a schema upgrade',
    );
  }
}

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.monad_main(0n);

const report = body.childNodes.find((n) => n.attrs && n.attrs.id === 'report');
if (!report) fail('no span#report was appended');
const want = 'storage=ok clock=ok media=ok hit=ok memory=ok random=ok location=ok ';
if (report.textContent !== want) {
  fail(`report mismatch: ${JSON.stringify(report.textContent)} (want ${JSON.stringify(want)})`);
}

if (!fetchInit || !fetchInit.headers) fail('fetch_begin_with did not pass request headers');
if (String(fetchInit.headers.Authorization) !== 'Bearer token') {
  fail(`missing/incorrect Authorization header: ${JSON.stringify(fetchInit.headers)}`);
}
if (String(fetchInit.headers['Content-Type']) !== 'application/json') {
  fail(`missing/incorrect Content-Type header: ${JSON.stringify(fetchInit.headers)}`);
}

if (stub.navigated !== 'https://example.test/next') {
  fail(`Window.navigate did not reach location.assign: ${JSON.stringify(stub.navigated)}`);
}
if (stub.reloaded !== 1) {
  fail(`Window.reload did not reach location.reload: ${stub.reloaded}`);
}

instance.exports.sha_begin();
await new Promise((resolve) => setTimeout(resolve, 100));
instance.exports.sha_finish();

const sha = body.childNodes.find((n) => n.attrs && n.attrs.id === 'sha');
const wantSha = 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';
if (!sha) fail('SHA-256 did not complete (no span#sha)');
if (sha.textContent !== wantSha) {
  fail(`SHA-256 of "abc" was ${JSON.stringify(sha.textContent)}, want ${wantSha}`);
}

if (globalThis.location.replaced !== 'https://app.test/done') {
  fail(`Window.replace did not reach location.replace: ${JSON.stringify(globalThis.location.replaced)}`);
}

// ─── ECDSA P-256 ───
//
// Every step is a separate export because each WebCrypto call is two-phase:
// start the op, let the promise settle on the microtask queue, then poll.

const span = (id) => body.childNodes.find((n) => n.attrs && n.attrs.id === id);
const settle = () => new Promise((resolve) => setTimeout(resolve, 20));

instance.exports.ecdsa_init();
await settle();
instance.exports.ecdsa_generate();
await settle();
instance.exports.ecdsa_key_ready();
await settle();
const key = span('key');
if (!key || key.textContent !== 'ready') {
  fail(`ECDSA key generation did not complete: ${key ? JSON.stringify(key.textContent) : 'no span#key'}`);
}

instance.exports.ecdsa_export_jwk();
await settle();
instance.exports.ecdsa_jwk_ready();
await settle();
const jwkSpan = span('jwk');
if (!jwkSpan) fail('the public JWK was never exported');
let jwk;
try {
  jwk = JSON.parse(jwkSpan.textContent);
} catch (e) {
  fail(`the exported JWK is not JSON: ${jwkSpan.textContent}`);
}
if (jwk.kty !== 'EC') fail(`JWK kty is ${JSON.stringify(jwk.kty)}, want "EC"`);
if (jwk.crv !== 'P-256') fail(`JWK crv is ${JSON.stringify(jwk.crv)}, want "P-256"`);
if (!jwk.x || !jwk.y) fail(`JWK is missing its coordinates: ${jwkSpan.textContent}`);
// A JWK of a NON-EXTRACTABLE key must not carry private material.
if (jwk.d) fail('the exported JWK leaked the private scalar (d)');

instance.exports.ecdsa_export_raw();
await settle();
instance.exports.ecdsa_raw_ready();
await settle();
const raw = span('raw');
if (!raw) fail('the raw public point was never exported');
// A SEC1 uncompressed P-256 point is 0x04 followed by 32-byte X and Y.
const rawHex = raw.textContent;
if (rawHex.length !== 130) fail(`raw public point is ${rawHex.length} hex chars, want 130`);
if (!rawHex.startsWith('04')) fail(`raw public point does not start with 04: ${rawHex.slice(0, 4)}`);

instance.exports.ecdsa_sign();
await settle();
instance.exports.ecdsa_sig_ready();
await settle();
const sigSpan = span('sig');
if (!sigSpan) fail('the ES256 signature was never produced');
const sigHex = sigSpan.textContent;
// ES256 is 64 bytes: IEEE P1363 r||s, which is already the JWS form.
if (sigHex.length !== 128) fail(`ES256 signature is ${sigHex.length} hex chars, want 128 (64 bytes)`);

// Verify the signature with NODE's WebCrypto -- an independent
// implementation -- against the JWK the module exported. This is the check
// that would catch a plausible-looking but wrong encoding.
const publicKey = await webcrypto.subtle.importKey(
  'jwk',
  { kty: jwk.kty, crv: jwk.crv, x: jwk.x, y: jwk.y },
  { name: 'ECDSA', namedCurve: 'P-256' },
  false,
  ['verify'],
);
const verified = await webcrypto.subtle.verify(
  { name: 'ECDSA', hash: 'SHA-256' },
  publicKey,
  Buffer.from(sigHex, 'hex'),
  new TextEncoder().encode('dpop-test-message'),
);
if (!verified) {
  fail('the ES256 signature did not verify against the exported public JWK in Node');
}

// ─── IndexedDB: the DPoP key surviving a reload ───

instance.exports.keystore_put();
await settle();
instance.exports.keystore_put_ready();
await settle();
const put = span('put');
if (!put || put.textContent !== '1') {
  fail(`KeyStore.put did not complete: ${put ? put.textContent : 'no span#put'}`);
}

instance.exports.keystore_get();
await settle();
instance.exports.keystore_get_ready();
await settle();
const got = span('get');
if (!got || got.textContent !== '1') {
  fail(`KeyStore.get did not find the stored key: ${got ? got.textContent : 'no span#get'}`);
}

// The restored handle must still sign -- a CryptoKey round-tripped through
// indexedDB is the whole point of the store.
instance.exports.keystore_sig_ready();
await settle();
const restored = span('restored_sig');
if (!restored) fail('a key restored from IndexedDB could not sign');
if (restored.textContent.length !== 128) {
  fail(`the restored-key signature is ${restored.textContent.length} hex chars, want 128`);
}
const restoredOk = await webcrypto.subtle.verify(
  { name: 'ECDSA', hash: 'SHA-256' },
  publicKey,
  Buffer.from(restored.textContent, 'hex'),
  new TextEncoder().encode('dpop-test-message'),
);
if (!restoredOk) fail('the signature made with the RESTORED key did not verify');

// An unwritten slot is state 3 (empty), not an error.
instance.exports.keystore_get_missing();
await settle();
instance.exports.keystore_missing_ready();
await settle();
const missing = span('missing');
if (!missing || missing.textContent !== '3') {
  fail(`an empty slot answered ${missing ? missing.textContent : 'nothing'}, want 3 (empty)`);
}

// A timed-out `Crypto.await_op` must still read as PENDING (0). A promise
// cannot settle while an export is on the stack, so awaiting inside one export
// always exhausts the budget -- deterministic to reach, and the one answer that
// matters is that it is not 1 ("done"), which would let `KeyStore.get` hand a
// caller the null key handle.
instance.exports.keystore_await_timeout();
await settle();
const timeoutState = span('await_timeout');
if (!timeoutState) fail('the timed-out await produced no span#await_timeout');
if (timeoutState.textContent === '1') {
  fail('a timed-out Crypto.await_op answered 1 (done): a caller reading a key handle would get the null one');
}
if (timeoutState.textContent !== '0') {
  fail(`a timed-out Crypto.await_op answered ${timeoutState.textContent}, want 0 (still pending)`);
}

// The connection bookkeeping, now that every keystore op has run: put, get,
// the absent-slot get and the timed-out get are four connections, and all four
// must be closed.
assertConnectionsClosed();

console.log(`ok: ${path} -> web surface, SHA-256 ok, ES256 verified, key survived IndexedDB`);
