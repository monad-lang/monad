#!/usr/bin/env node
// Oak-level events: lowered handler attributes, drag-and-drop payloads,
// drag/drop effects, and the sync clipboard path.
// Usage:
//   node wasm/web/oak_event_smoke.mjs <oak_events.wasm>

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { FakeDataTransfer, installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/oak_event_smoke.mjs <oak_events.wasm>');
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

const source = byId('source');
const target = byId('target');
const field = byId('field');
const copier = byId('copier');
const paster = byId('paster');
const state = byId('state');
if (!source || !target || !field || !copier || !paster || !state) {
  fail('the view did not mount every probe node');
}

// ── lowering: handler attrs carry a hex id, flags ride after ':' ──
const startSpec = source.attrs['data-oak-on-dragstart'];
if (!/^0x[0-9a-f]{8}$/.test(startSpec || '')) {
  fail(`dragstart spec is ${JSON.stringify(startSpec)}`);
}
if (source.attrs.draggable !== 'true') fail('source is not draggable');
if (!/^10:text\/plain/.test(source.attrs['data-oak-drag'] || '')) {
  fail(`drag payload is ${JSON.stringify(source.attrs['data-oak-drag'])}`);
}
if (!/:d$/.test(target.attrs['data-oak-on-dragover'] || '')) {
  fail(`dragover spec is ${JSON.stringify(target.attrs['data-oak-on-dragover'])}`);
}
if (target.attrs['data-oak-drop-effect'] !== 'copy') {
  fail('drop effect attribute is missing');
}
if ((target.listeners.drop || []).length !== 1) fail('drop listener was not registered');
if ((target.listeners.dragover || []).length !== 1) fail('dragover listener was not registered');

// ── dragstart: the host fills dataTransfer from the view attributes ──
const drag = new FakeDataTransfer();
source.fire('dragstart', { dataTransfer: drag });
if (drag.getData('text/plain') !== 'payload') {
  fail(`drag payload is ${JSON.stringify(drag.getData('text/plain'))}`);
}
if (drag.effectAllowed !== 'copy') fail(`effectAllowed is ${drag.effectAllowed}`);

// ── dragover: the `d` flag prevents default; dropEffect is declarative ──
drag.dropEffect = 'none';
const overEvt = target.fire('dragover', { dataTransfer: drag });
if (!overEvt.defaultPrevented) fail('dragover did not preventDefault');
if (drag.dropEffect !== 'copy') fail(`dropEffect is ${drag.dropEffect}`);

// ── drop: the payload reaches update, then the tick patches the view ──
drag.setData('text/plain', 'dropped');
const dropEvt = target.fire('drop', { dataTransfer: drag });
if (!dropEvt.defaultPrevented) fail('drop did not preventDefault');
instance.exports.oak_tick();
if (!state.textContent.startsWith('dropped/hello/')) {
  fail(`after drop the state is ${JSON.stringify(state.textContent)}`);
}

// ── input: e.value reaches a String -> Msg handler ──
field.value = 'typed';
field.fire('input');
instance.exports.oak_tick();
if (!state.textContent.includes('/typed/')) {
  fail(`after input the state is ${JSON.stringify(state.textContent)}`);
}

// ── copy: copy_text fills clipboardData and prevents the default ──
const clip = new FakeDataTransfer();
const copyEvt = copier.fire('copy', { clipboardData: clip });
if (clip.getData('text/plain') !== 'typed') {
  fail(`copy text is ${JSON.stringify(clip.getData('text/plain'))}`);
}
if (!copyEvt.defaultPrevented) fail('copy did not preventDefault');

// ── paste: clipboardData reaches the pure handler ──
const pasteData = new FakeDataTransfer();
pasteData.setData('text/plain', 'pasted');
paster.fire('paste', { clipboardData: pasteData });
instance.exports.oak_tick();
if (!state.textContent.endsWith('/pasted')) {
  fail(`after paste the state is ${JSON.stringify(state.textContent)}`);
}

console.log(`ok: ${path} -> lowered handlers, drag/drop payloads, sync clipboard`);
