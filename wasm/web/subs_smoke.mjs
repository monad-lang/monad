#!/usr/bin/env node
// Subscriptions: window/document listeners and the animation-frame hook.
// Usage:
//   node wasm/web/subs_smoke.mjs <oak_subs.wasm>

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/subs_smoke.mjs <oak_subs.wasm>');
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

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();

const count = () => byId('count').textContent;

// ── the model declared one listener per subscription ──
if ((globalThis.window.listeners.resize || []).length !== 1) {
  fail('the resize subscription did not register on window');
}
if ((globalThis.document.listeners.visibilitychange || []).length !== 1) {
  fail('the visibilitychange subscription did not register on document');
}

// ── each fires into update, one tick per event ──
globalThis.window.fire('resize');
instance.exports.oak_tick();
if (count() !== '1') fail(`after resize the count is ${count()}`);

globalThis.document.fire('visibilitychange');
instance.exports.oak_tick();
if (count() !== '11') fail(`after visibilitychange the count is ${count()}`);

// ── the frame subscription is dispatched by the loader's rAF loop ──
let pending = null;
globalThis.requestAnimationFrame = (cb) => { pending = cb; };
host.start_ticks(instance);
if (typeof pending !== 'function') fail('start_ticks did not schedule a frame');
pending();
if (count() !== '111') fail(`after one frame the count is ${count()}`);

console.log(`ok: ${path} -> window/document subscriptions and the frame loop`);
