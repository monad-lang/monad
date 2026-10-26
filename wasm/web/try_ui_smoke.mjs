#!/usr/bin/env node
// Node smoke test for the /try Oak UI. Usage:
//   node wasm/web/try_ui_smoke.mjs <try_ui.wasm>
//
// Drives the real Oak runtime over `stub_dom.mjs` with a FAKE Worker: the
// UI's worker channel is a JS host contract, so the test asserts what the
// UI posts (`{type:'run', source}`), how it polls, and what it renders
// when a result arrives -- the engine itself is covered by
// `try_engine_smoke.mjs`.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { FakeNode, body, installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/try_ui_smoke.mjs <try_ui.wasm>');
  process.exit(2);
}

const workers = [];
class FakeWorker {
  constructor(url) {
    this.url = url;
    this.posted = [];
    this.terminated = false;
    this.onmessage = null;
    this.onerror = null;
    workers.push(this);
  }
  postMessage(message) {
    this.posted.push(message);
  }
  terminate() {
    this.terminated = true;
  }
  deliver(data) {
    if (this.onmessage) this.onmessage({ data });
  }
}
globalThis.Worker = FakeWorker;

let pendingFrame = null;
globalThis.requestAnimationFrame = (cb) => {
  pendingFrame = cb;
  return 1;
};
globalThis.cancelAnimationFrame = () => {};
function frame() {
  const cb = pendingFrame;
  pendingFrame = null;
  if (cb) cb(performance.now());
}

installDocument();
const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();
host.start_ticks(instance);

function findAll(node, pred, acc = []) {
  for (const child of node.childNodes) {
    if (child.nodeType === 1) {
      if (pred(child)) acc.push(child);
      findAll(child, pred, acc);
    }
  }
  return acc;
}
const byTag = (tag) => findAll(body, (n) => n.tagName === tag);
const textarea = byTag('TEXTAREA')[0];
if (!textarea) fail('no textarea rendered');
const buttons = byTag('BUTTON');
const runButton = buttons.find((b) => b.textContent === 'Run');
if (!runButton) fail(`no Run button; buttons are ${buttons.map((b) => b.textContent).join(', ')}`);

// Type a program (the uncontrolled editor: value changes, source updates).
textarea.value = 'def main : I64 := 2 + 3';
textarea.fire('input');
instance.exports.oak_tick();

runButton.fire('click');
instance.exports.oak_tick();

if (workers.length !== 1) fail(`expected one worker, got ${workers.length}`);
const worker = workers[0];
const posted = worker.posted[0];
if (!posted || posted.type !== 'run') fail(`worker was not asked to run: ${JSON.stringify(posted)}`);
if (posted.source !== 'def main : I64 := 2 + 3') {
  fail(`worker received ${JSON.stringify(posted.source)}`);
}

// Result arrives; the animation-frame subscription polls and renders it.
worker.deliver({ type: 'result', seq: posted.seq, status: 'ok', value: '5', typeText: 'I64', error: '', notes: '' });
frame();
instance.exports.oak_tick();

const output = findAll(body, (n) => n.attrs && n.attrs.id === 'try-result')[0];
if (!output) fail('no result pane');
const text = output.textContent;
if (!text.includes('5')) fail(`result pane does not show 5: ${JSON.stringify(text)}`);
if (!text.includes(': I64')) fail(`result pane does not show the type: ${JSON.stringify(text)}`);
if (!worker.terminated) fail('the worker was not terminated after its result');

// Cancel path: start again, then cancel; the worker must be terminated.
instance.exports.oak_tick();
const runAgain = findAll(body, (n) => n.tagName === 'BUTTON' && n.textContent === 'Run')[0];
if (!runAgain) fail('no Run button after a result');
runAgain.fire('click');
instance.exports.oak_tick();
const second = workers[workers.length - 1];
const cancel = findAll(body, (n) => n.tagName === 'BUTTON' && n.textContent === 'Cancel')[0];
if (!cancel) fail('no Cancel button while running');
cancel.fire('click');
instance.exports.oak_tick();
if (!second.terminated) fail('Cancel did not terminate the worker');

console.log(`ok: ${path} -> /try UI runs, polls, renders and cancels`);
