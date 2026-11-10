#!/usr/bin/env node
// Node smoke test for the Phase-1 web surface. Usage:
//   node wasm/web/new_surface_smoke.mjs <web_new_surface.wasm>
//
// Drives the REAL `wasm/web/web_runtime.js` and generated `web.js` over the
// stub DOM/globals: storage presence/removal, monotonic clock, media query,
// hit test + attribute read, random bytes, request headers, memory probes,
// and a two-phase SHA-256 completed through a second export.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { FakeNode, body, installDocument, fail, stub } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/new_surface_smoke.mjs <web_new_surface.wasm>');
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

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.monad_main(0n);

const report = body.childNodes.find((n) => n.attrs && n.attrs.id === 'report');
if (!report) fail('no span#report was appended');
const want = 'storage=ok clock=ok media=ok hit=ok memory=ok random=ok ';
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

console.log(`ok: ${path} -> phase-1 web surface, SHA-256 ok`);
