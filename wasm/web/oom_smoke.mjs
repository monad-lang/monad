#!/usr/bin/env node
// Heap exhaustion is a diagnostic trap, not a silent 0 or a negative-offset
// RangeError. Usage: node wasm/web/oom_smoke.mjs <any web .wasm>
//
// `try_alloc` is the C-only staging export present in every web module; a
// request no `memory.grow` can satisfy calls `oom` and then `unreachable`.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/oom_smoke.mjs <module.wasm>');
  process.exit(2);
}

installDocument();
const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);

if (typeof instance.exports.try_alloc !== 'function') {
  fail('module does not export try_alloc');
}

let logged = '';
const original = console.error;
console.error = (message) => { logged = String(message); };
let trapped = false;
try {
  instance.exports.try_alloc(1n << 40n); // 1 TiB
} catch (e) {
  trapped = e instanceof WebAssembly.RuntimeError;
  if (!trapped) logged = `unexpected error: ${e && e.message}`;
} finally {
  console.error = original;
}

if (!trapped) {
  fail(`allocation did not trap: ${logged}`);
}
if (!logged.includes('heap exhausted')) {
  fail(`no heap-exhausted diagnostic: ${JSON.stringify(logged)}`);
}

console.log(`ok: ${path} -> OOM trap with a heap-exhausted diagnostic`);
