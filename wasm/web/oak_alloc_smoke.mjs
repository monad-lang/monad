#!/usr/bin/env node
// Render allocation guard: a 256-button view with two handlers per cell.
// Usage:
//   node wasm/web/oak_alloc_smoke.mjs <oak_spa_alloc.wasm> [max-delta-bytes]
//
// Mounts, then fires one click and ticks, and asserts committed linear
// memory grew by less than the ceiling (default 2 MiB). The pre-fix path
// allocated ~3 MB for this view; the number is printed so a regression is
// visible even below the threshold.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
const ceiling = Number(process.argv[3] ?? 2097152);
if (!path) {
  console.error('usage: node wasm/web/oak_alloc_smoke.mjs <oak_spa_alloc.wasm> [max-delta-bytes]');
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

const committed = () => instance.exports.memory.buffer.byteLength;
const board = byId('board');
if (!board) fail('no #board in the view');
const buttons = board.childNodes.filter((n) => n.nodeType === 1);
if (buttons.length !== 256) fail(`board has ${buttons.length} buttons, want 256`);

const before = committed();
buttons[7].fire('click');
instance.exports.oak_tick();
const after = committed();
const delta = after - before;

console.log(`committed delta for one 256-node render: ${delta} bytes`);
if (delta > ceiling) {
  fail(`render allocated ${delta} bytes, over the ${ceiling}-byte ceiling`);
}
const count = byId('app');
if (!count || !count.textContent.startsWith('1')) {
  fail('the click did not reach update');
}

console.log(`ok: ${path} -> one 256-node render in ${delta} bytes`);
