#!/usr/bin/env node
// Low-level event transport: the synchronous slot, the selector getters, the
// spec flags, and the declarative drag/clipboard effects.
// Usage:
//   node wasm/web/event_smoke.mjs <web_events.wasm>
//
// `fixtures/wasm/web_events.mo` mounts a probe with one listener per event
// family and writes the snapshot into `#report` as
//   kind|clientX|clientY|modifiers|key|code|value|data|types|files|repeat|effectAllowed|dropEffect|handler

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { FakeDataTransfer, installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/event_smoke.mjs <web_events.wasm>');
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
instance.exports.setup();

const probe = byId('probe');
const report = byId('report');
if (!probe || !report) fail('setup did not mount the probe/report nodes');
const text = () => report.textContent;
const fields = () => text().split('|');

// ── pointer: coordinates, modifiers, button, pointerId ──
probe.fire('pointerdown', {
  clientX: 12.5, clientY: 3, shiftKey: true, button: 2, buttons: 3, detail: 2,
  pointerId: 7, pointerType: 'pen', pressure: 0.5, isPrimary: true, timeStamp: 1234.5,
});
{
  const f = fields();
  if (f[0] !== 'pointerdown') fail(`kind is ${JSON.stringify(f[0])}`);
  if (f[1] !== '12.5' || f[2] !== '3') fail(`coordinates are ${f[1]},${f[2]}`);
  if (f[3] !== '1') fail(`shift modifier is ${f[3]}`);
  if (f[13] !== '2') fail(`detail is ${f[13]}`);
  if (f[14] !== '7') fail(`pointerId is ${f[14]}`);
  if (f[15] !== '0.5') fail(`pressure is ${f[15]}`);
  if (f[19] !== '1234.5') fail(`timeStamp is ${f[19]}`);
  if (f[22] !== '1') fail(`isPrimary is ${f[22]}`);
  if (f[23] !== '1') fail(`handled id is ${f[23]}`);
}

// ── keyboard: key/code/repeat ──
probe.fire('keydown', { key: 'a', code: 'KeyA', repeat: true, location: 1 });
{
  const f = fields();
  if (f[0] !== 'keydown' || f[4] !== 'a' || f[5] !== 'KeyA') {
    fail(`keydown snapshot is ${JSON.stringify(text())}`);
  }
  if (f[10] !== '1') fail(`repeat flag is ${f[10]}`);
  if (f[21] !== '1') fail(`location is ${f[21]}`);
}

// ── form: the live target value ──
probe.value = 'typed';
probe.checked = true;
probe.fire('input');
{
  const f = fields();
  if (f[0] !== 'input' || f[6] !== 'typed') {
    fail(`input value snapshot is ${JSON.stringify(text())}`);
  }
  if (f[20] !== '1') fail(`checked is ${f[20]}`);
}

// ── wheel: deltas and deltaMode ──
probe.fire('wheel', { deltaX: 1.5, deltaY: 2.5, deltaMode: 1 });
{
  const f = fields();
  if (f[0] !== 'wheel' || f[16] !== '1.5' || f[17] !== '2.5' || f[18] !== '1') {
    fail(`wheel snapshot is ${JSON.stringify(text())}`);
  }
}

// ── dragstart: declarative payload + effectAllowed ──
probe.setAttribute('data-oak-drag', '10:text/plaindragdata');
probe.setAttribute('data-oak-drag-effect', 'move');
const drag = new FakeDataTransfer();
const startEvt = probe.fire('dragstart', { dataTransfer: drag });
if (drag.getData('text/plain') !== 'dragdata') {
  fail(`dragstart setData produced ${JSON.stringify(drag.getData('text/plain'))}`);
}
if (drag.effectAllowed !== 'move') fail(`dragstart effectAllowed is ${drag.effectAllowed}`);
if (startEvt.defaultPrevented) fail('dragstart prevented default without a flag');

// ── dragover: the `d` flag prevents default; the drop effect is declarative ──
probe.setAttribute('data-oak-drop-effect', 'copy');
drag.dropEffect = 'none';
const overEvt = probe.fire('dragover', { dataTransfer: drag });
if (!overEvt.defaultPrevented) fail('dragover did not preventDefault');
if (drag.dropEffect !== 'copy') fail(`dragover dropEffect is ${drag.dropEffect}`);

// ── drop: payload + types reach the snapshot ──
drag.setData('text/plain', 'dropped');
const dropEvt = probe.fire('drop', { dataTransfer: drag });
if (!dropEvt.defaultPrevented) fail('drop did not preventDefault');
{
  const f = fields();
  if (f[7] !== 'dropped') fail(`drop data is ${JSON.stringify(f[7])}`);
  if (f[8] !== '1') fail(`drop type count is ${f[8]}`);
}

// ── paste: clipboardData text ──
const clip = new FakeDataTransfer();
clip.setData('text/plain', 'pasted');
probe.fire('paste', { clipboardData: clip });
{
  const f = fields();
  if (f[7] !== 'pasted') fail(`paste data is ${JSON.stringify(f[7])}`);
}

// ── flags are stored on the listener (c/p/o) ──
{
  const entries = probe.listeners.custom || [];
  if (entries.length !== 1) fail(`custom has ${entries.length} listeners`);
  const opts = entries[0].options || {};
  if (!opts.capture || !opts.passive || !opts.once) {
    fail(`custom options are ${JSON.stringify(opts)}`);
  }
}

// ── the slot is empty outside a dispatch ──
instance.exports.oak_dispatch_event(0n);
if (!text().startsWith('|')) {
  fail(`a getter outside dispatch saw a live event: ${JSON.stringify(text())}`);
}

console.log(`ok: ${path} -> event snapshot, flags, drag payload and clipboard text`);
