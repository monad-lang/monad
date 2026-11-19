#!/usr/bin/env node
// The web collector under a frame loop. Usage:
//   node wasm/web/smoke/gc_smoke.mjs <gc_tick.wasm> [ticks] [max-heap-bytes]
//
// Drives fixtures/wasm/gc_tick.mo: mount once, then `ticks` calls to
// `gc_tick`, each allocating ~3 MB of garbage and replacing the kept
// 2000-element list. Asserts the logged state sum is exact on every tick
// (a freed live cell corrupts it), that the collector ran, and that
// committed linear memory stays under the ceiling (default 96 MiB; the old
// bump allocator passed 1 GiB within ~300 ticks).

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
const ticks = Number(process.argv[3] ?? 1000);
const ceiling = Number(process.argv[4] ?? 96 * 1024 * 1024);
if (!path) {
  console.error('usage: node wasm/web/smoke/gc_smoke.mjs <gc_tick.wasm> [ticks] [max-heap-bytes]');
  process.exit(2);
}

installDocument();
const bytes = await readFile(path);
let memory = null;
const logs = [];
const importObject = {
  monad: {
    ...imports.monad,
    console_log(ptr, len) {
      logs.push(Buffer.from(memory.buffer, Number(ptr), Number(len)).toString('utf8'));
      return 0n;
    },
  },
};
const { instance } = await WebAssembly.instantiate(bytes, importObject);
host.bind(instance);
memory = instance.exports.memory;
const ex = instance.exports;
for (const name of ['gc_mount', 'gc_tick', 'web_gc_collections', 'web_gc_live_bytes']) {
  if (typeof ex[name] !== 'function') fail(`missing export ${name}`);
}

const N = 2000;
const base = (N * (N - 1)) / 2;
let waste = null;
ex.gc_mount();
let peak = 0;
for (let t = 1; t <= ticks; t++) {
  ex.gc_tick();
  const line = logs.pop();
  if (line === undefined) fail(`tick ${t}: no log`);
  const [sum, w] = line.split(' ').map(Number);
  const want = base + N * t;
  if (sum !== want) fail(`tick ${t}: state sum ${sum}, want ${want} (a live cell was freed)`);
  if (waste === null) waste = w;
  else if (w !== waste) fail(`tick ${t}: garbage length ${w}, want ${waste}`);
  peak = Math.max(peak, memory.buffer.byteLength);
  if (peak > ceiling) fail(`tick ${t}: linear memory ${peak} exceeds ${ceiling} (nothing is freed)`);
}

const collections = Number(ex.web_gc_collections());
if (collections === 0) fail('the collector never ran');
const mib = (n) => (n / 1048576).toFixed(1);
console.log(`ok: ${path} -> ${ticks} ticks, ${collections} collections, ` +
  `peak ${mib(peak)} MiB, live ${mib(Number(ex.web_gc_live_bytes()))} MiB`);
