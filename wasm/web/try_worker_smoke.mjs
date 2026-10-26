#!/usr/bin/env node
// Node smoke test for the REAL `worker.js` protocol. Usage:
//   node wasm/web/try_worker_smoke.mjs <dir>
//
// `<dir>` is a built /try directory (the output of `scripts/build-try.sh`):
// it must contain worker.js, sources.js, web.js, web_runtime.js,
// float_format.js, try_engine.wasm, sources.json and the sources/ tree. The
// worker's own relative imports are used, so this exercises the EXACT
// pairing a browser gets -- which is what the stale host/new worker mismatch
// broke: the UI harness fakes the worker, and the engine harness bypasses
// it, so nothing pinned the protocol before. It is also the only test that
// takes the served source files through the REAL worker (index fetch, files
// fetch, `sources.js` framing, `try_run(sources, source)`).
//
// Shims: `fetch` serves the engine bytes and the served source files from
// `<dir>` (compileStreaming fails in Node, so the worker's arrayBuffer
// fallback runs), and `postMessage` collects the messages the worker would
// send to the page.

import { readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

const dir = process.argv[2];
if (!dir) {
  console.error('usage: node wasm/web/try_worker_smoke.mjs <dir>');
  process.exit(2);
}

function fail(message) {
  console.error(message);
  process.exit(1);
}

const engine = await readFile(join(dir, 'try_engine.wasm'));

let messages = [];
let notify = null;
globalThis.postMessage = (msg) => {
  messages.push(msg);
  // Re-arm on every message: a waiter outlives the messages that do not
  // match it (a `started` arriving before its `result`, a second run).
  if (notify) notify();
};

function served(body, status = 200) {
  return {
    ok: status === 200,
    status,
    arrayBuffer: async () => body,
    text: async () => Buffer.from(body).toString('utf8'),
    json: async () => JSON.parse(Buffer.from(body).toString('utf8')),
  };
}

// The worker resolves its URLs relative to itself, so the shim keys off the
// path suffix and reads the same files the site would serve.
globalThis.fetch = async (url) => {
  const href = String(url).split('?')[0];
  if (href.endsWith('try_engine.wasm')) {
    return served(engine.buffer.slice(engine.byteOffset, engine.byteOffset + engine.byteLength));
  }
  if (href.endsWith('sources.json')) {
    return served(await readFile(join(dir, 'sources.json')));
  }
  const marker = href.indexOf('sources/');
  if (marker !== -1) {
    return served(await readFile(join(dir, 'sources', href.slice(marker + 'sources/'.length))));
  }
  throw new Error(`unexpected fetch ${href}`);
};

function waitFor(predicate, what, timeoutMs = 180000) {
  return new Promise((resolve, reject) => {
    const check = () => {
      const found = messages.find(predicate);
      if (found) {
        notify = null;
        clearTimeout(timer);
        resolve(found);
      }
    };
    notify = check;
    const timer = setTimeout(() => {
      reject(new Error(`timed out waiting for ${what}; saw ${JSON.stringify(messages)}`));
    }, timeoutMs);
    check();
  });
}

// A Web Worker has `onmessage` as a global binding; Node modules are
// strict, so the property must exist before `worker.js` assigns it.
globalThis.onmessage = null;

await import(`${pathToFileURL(join(dir, 'worker.js')).href}?v=${Date.now()}`);
if (typeof globalThis.onmessage !== 'function') {
  fail('worker.js did not install globalThis.onmessage');
}

globalThis.onmessage({ data: { type: 'run', seq: 7, source: 'def main : I64 := 2 + 3\n' } });

const started = await waitFor((m) => m.type === 'started', 'the started message');
if (started.seq !== 7) fail(`started carried seq ${started.seq}, expected 7`);

const result = await waitFor(
  (m) => m.type === 'result' || m.type === 'failure',
  'a result',
);
if (result.type === 'failure') fail(`the worker failed: ${result.error}`);
if (result.seq !== 7) fail(`result carried seq ${result.seq}, expected 7`);
if (result.status !== 'ok') fail(`status ${JSON.stringify(result.status)}, expected ok (${result.error})`);
if (result.value !== '5') fail(`value ${JSON.stringify(result.value)}, expected "5"`);
if (result.typeText !== 'I64') fail(`type ${JSON.stringify(result.typeText)}, expected "I64"`);

// The served files really are the prelude: a module outside the old
// embedded nine resolves through the same fetch path.
messages = [];
notify = null;
globalThis.onmessage({ data: { type: 'run', seq: 8, source: 'use init::foldable {}\n\ndef main : I64 := 7\n' } });
const second = await waitFor(
  (m) => (m.type === 'result' || m.type === 'failure') && m.seq === 8,
  'the second result',
);
if (second.type === 'failure') fail(`the second run failed: ${second.error}`);
if (second.status !== 'ok' || second.value !== '7') {
  fail(`use init::foldable gave ${second.status}/${JSON.stringify(second.value)} (${second.error})`);
}

console.log(`ok: ${dir} -> worker.js speaks the host protocol (started, then 5 : I64)`);
console.log(`ok: ${dir} -> the served sources are the prelude (use init::foldable resolves)`);
