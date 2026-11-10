#!/usr/bin/env node
// `Command.batch` + `Command.after` + `Command.focus`. Usage:
//   node wasm/web/timer_smoke.mjs <oak_timer.wasm>
//
// One click must: fold `now` in this batch (count 0 -> 1), focus #target
// after the patch, and, once the host timer fires, fold `later` on the next
// tick (1 -> 11). No animation-frame subscription is involved.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/timer_smoke.mjs <oak_timer.wasm>');
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
if (count() !== '0') fail(`initial count is ${count()}`);

const go = byId('go');
if (!go) fail('no #go button in the view');
go.fire('click');
instance.exports.oak_tick();

if (count() !== '1') fail(`after the batch's immediate dispatch the count is ${count()}`);
const active = globalThis.document.activeElement;
if (!active || active.attrs.id !== 'target') {
  fail(`focus after patch went to ${active && active.attrs && active.attrs.id}`);
}

// The timer callback re-enters wasm through oak_dispatch_event; the message
// waits in the state slot until the next tick.
await new Promise((resolve) => setTimeout(resolve, 80));
instance.exports.oak_tick();
if (count() !== '11') fail(`after the delayed message the count is ${count()}`);

console.log(`ok: ${path} -> batch folded now, focused #target, delivered the 10 ms timer`);
