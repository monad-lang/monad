#!/usr/bin/env node
// Async clipboard: pending, resolved, rejected, and write.
// Usage:
//   node wasm/web/clipboard_smoke.mjs <web_events.wasm>

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail, stub } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/clipboard_smoke.mjs <web_events.wasm>');
  process.exit(2);
}

installDocument();

function byId(id) {
  const walk = (n) => {
    if (n.attrs && n.attrs.id === id) return n;
    for (const c of n.childNodes) {
      const found = walk(c);
      if (found) return found;
    }
    return null;
  };
  return walk(body);
}

const flush = () => new Promise((resolve) => setTimeout(resolve, 0));

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.setup();

const report = byId('report');
const text = () => report.textContent;

// ── pending, then resolved ──
instance.exports.clipboard_read_begin_test();
if (text() !== 'pending') fail(`read should start pending, saw ${JSON.stringify(text())}`);
await flush();
instance.exports.clipboard_read_finish_test();
if (text() !== 'ok:from-clipboard') {
  fail(`read result is ${JSON.stringify(text())}`);
}

// ── a rejected promise is an Err with the DOMException name ──
globalThis.navigator.clipboard.readText = () => Promise.reject({ name: 'NotAllowedError' });
instance.exports.clipboard_read_begin_test();
await flush();
instance.exports.clipboard_read_finish_test();
if (text() !== 'err:NotAllowedError') {
  fail(`rejected read is ${JSON.stringify(text())}`);
}

// ── write ──
stub.clipboardWritten = null;
instance.exports.clipboard_write_begin_test();
await flush();
instance.exports.clipboard_write_finish_test();
if (text() !== 'ok') fail(`write result is ${JSON.stringify(text())}`);
if (stub.clipboardWritten !== 'written') {
  fail(`writeText saw ${JSON.stringify(stub.clipboardWritten)}`);
}

console.log(`ok: ${path} -> async clipboard pending/resolved/rejected/write`);
