#!/usr/bin/env node
// Node smoke test for the Oak SPA loop. Usage:
//   node wasm/web/spa_smoke.mjs <oak_spa.wasm>
//
// Built from fixtures/wasm/oak_spa.mo: a two-message counter. The test drives the
// REAL `wasm/web/web_runtime.js` and the generated `wasm/web/web.js` import
// object over a minimal stub DOM, so the whole path is exercised --
// export thunks -> `oak_wasm` runtime -> `web_wasm` externs -> C wrappers ->
// JS host -> DOM -- and the patch path is checked by watching the live text
// node change after `oak_tick`.
//
// Sequence: mount, assert "0"; fire two clicks (queued messages), one tick
// folds both into "2"; fire reset, one tick patches back to "0". Two ticks
// and two messages also prove the batch fold and the queue drain.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/spa_smoke.mjs <oak_spa.wasm>');
  process.exit(2);
}

class FakeNode {
  constructor(nodeType, tagName) {
    this.nodeType = nodeType;
    this.tagName = tagName;
    this.childNodes = [];
    this.attrs = {};
    this.listeners = {};
    this.parentNode = null;
    this._text = '';
  }

  appendChild(child) {
    child.parentNode = this;
    this.childNodes.push(child);
    return child;
  }

  insertBefore(child, before) {
    const at = before ? this.childNodes.indexOf(before) : -1;
    child.parentNode = this;
    if (at < 0) this.childNodes.push(child);
    else this.childNodes.splice(at, 0, child);
    return child;
  }

  removeChild(child) {
    const at = this.childNodes.indexOf(child);
    if (at >= 0) this.childNodes.splice(at, 1);
    child.parentNode = null;
    return child;
  }

  replaceChild(next, old) {
    const at = this.childNodes.indexOf(old);
    if (at >= 0) this.childNodes[at] = next;
    next.parentNode = this;
    old.parentNode = null;
    return old;
  }

  setAttribute(name, value) {
    this.attrs[name] = value;
  }

  removeAttribute(name) {
    delete this.attrs[name];
  }

  addEventListener(event, handler) {
    (this.listeners[event] ||= []).push(handler);
  }

  removeEventListener(event, handler) {
    const handlers = this.listeners[event] || [];
    this.listeners[event] = handlers.filter((h) => h !== handler);
  }

  fire(event) {
    for (const handler of this.listeners[event] || []) handler();
  }

  get textContent() {
    if (this.nodeType === 3) return this._text;
    return this.childNodes.map((c) => c.textContent).join('');
  }

  set textContent(value) {
    this.childNodes = [];
    this._text = value;
  }

  get nodeValue() {
    return this._text;
  }

  set nodeValue(value) {
    this._text = value;
  }
}

// `createElement` records the last node it made, so the direct-runtime
// section below can fire a listener on the node its id names.
let lastCreated = null;

const body = new FakeNode(1, 'BODY');
// A stand-in for a server-rendered page: `oak_mount` must clear the
// container before mounting (v1 hydration replaces, it does not adopt).
const stale = new FakeNode(1, 'DIV');
stale.setAttribute('id', 'server-rendered');
body.appendChild(stale);
globalThis.document = {
  body,
  querySelector(selector) {
    return selector === 'body' || selector === '#app' ? body : null;
  },
  createElement(tag) {
    lastCreated = new FakeNode(1, tag.toUpperCase());
    return lastCreated;
  },
  createTextNode(text) {
    lastCreated = new FakeNode(3, '#text');
    lastCreated.nodeValue = text;
    return lastCreated;
  },
  createComment(text) {
    lastCreated = new FakeNode(8, '#comment');
    lastCreated.nodeValue = text;
    return lastCreated;
  },
};

function fail(message) {
  console.error(message);
  process.exit(1);
}

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.oak_mount();

if (body.childNodes.some((n) => n.attrs.id === 'server-rendered')) {
  fail('oak_mount did not clear the server-rendered content under the root');
}
const root = body.childNodes.find((n) => n.tagName === 'DIV');
if (!root) fail('oak_mount did not append the view under the root');
const counter = () => root.childNodes.find((n) => n.tagName === 'SPAN');
const addButton = root.childNodes.find((n) => n.tagName === 'BUTTON' && n.textContent === 'add');
const resetButton = root.childNodes.find((n) => n.tagName === 'BUTTON' && n.textContent === 'reset');
if (!counter() || !addButton || !resetButton) {
  fail(`mounted tree is not the counter view: ${JSON.stringify(root.childNodes.map((n) => n.tagName))}`);
}
if (counter().textContent !== '0') fail(`initial count is ${counter().textContent}`);
if (!addButton.listeners.click || addButton.listeners.click.length !== 1) {
  fail('the add button has no click listener (data-oak-on-click was not registered)');
}

// Two messages, one tick: the batch fold must apply both, IN ARRIVAL
// ORDER. add-then-reset is the pair that distinguishes FIFO (0) from LIFO
// (1), which the old cons-based enqueue produced.
addButton.fire('click');
resetButton.fire('click');
instance.exports.oak_tick();
if (counter().textContent !== '0') fail(`add-then-reset in one frame gave ${counter().textContent}, expected 0 (FIFO)`);

addButton.fire('click');
addButton.fire('click');
instance.exports.oak_tick();
if (counter().textContent !== '2') fail(`after two clicks the count is ${counter().textContent}`);

// A second tick with a reset patches the same text node back to 0.
resetButton.fire('click');
instance.exports.oak_tick();
if (counter().textContent !== '0') fail(`after reset the count is ${counter().textContent}`);

// A tick with an empty queue must not disturb anything.
instance.exports.oak_tick();
if (counter().textContent !== '0') fail(`an idle tick changed the count to ${counter().textContent}`);

// ── the JS host directly: listener replacement, comments, bad selectors ──
//
// The SPA's handler ids are constant, so the attribute-change path is
// exercised here: setting `data-oak-on-click` again must REPLACE the
// listener, and removing the attribute must unregister it.
const calls = [];
const fakeMemory = { buffer: new ArrayBuffer(4096) };
host.bind({
  exports: {
    memory: fakeMemory,
    oak_dispatch_event(id) {
      calls.push(Number(id));
    },
  },
});

const encoder = new TextEncoder();
function write(text, at) {
  const bytes = encoder.encode(text);
  new Uint8Array(fakeMemory.buffer, at, bytes.length).set(bytes);
  return [BigInt(at), BigInt(bytes.length)];
}

// Create through the host so the node gets an id, then fire on the node it
// made (`lastCreated` is recorded by the stub `createElement`).
const buttonId = host.dom_create('button');
const hostButton = lastCreated;
const [kp, kl] = write('data-oak-on-click', 0);
const [v7p, v7l] = write('7', 256);
const [v8p, v8l] = write('8', 288);

host.dom_set_attr(buttonId, kp, kl, v7p, v7l);
hostButton.fire('click');
host.dom_set_attr(buttonId, kp, kl, v8p, v8l);
hostButton.fire('click');
if (calls.join(',') !== '7,8') {
  fail(`listener replacement failed: dispatched ${JSON.stringify(calls)} (expected 7 then 8 exactly once each)`);
}
host.dom_remove_attr(buttonId, kp, kl);
hostButton.fire('click');
if (calls.join(',') !== '7,8') {
  fail(`removing data-oak-on-click left a live listener: dispatched ${JSON.stringify(calls)}`);
}

const commentId = host.dom_create_comment(...write('note', 384));
if (commentId === 0n || !lastCreated || lastCreated.nodeType !== 8) {
  fail('dom_create_comment did not create a comment node');
}

host.set_root('#missing');
let threw = false;
try {
  host.dom_root();
} catch {
  threw = true;
}
if (!threw) fail('dom_root fell back silently for a selector that matches nothing');

console.log(`ok: ${path} -> mount 0, FIFO batch, patch to 2 then 0, listeners replaced/removed`);
