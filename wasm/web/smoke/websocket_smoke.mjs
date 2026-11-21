#!/usr/bin/env node
// WebSocket: the oak subscription that owns a socket, and the imperative
// `web_wasm` socket. Usage:
//   node wasm/web/smoke/websocket_smoke.mjs <oak_socket.wasm>
//
// The fake `WebSocket` records what was opened and what was sent, and lets
// the test fire open/message/close in a controlled order. Every callback is
// asynchronous in the browser; the harness calls them directly, then the
// wake-up the host scheduled with `setTimeout` dispatches the oak handler.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/smoke/websocket_smoke.mjs <oak_socket.wasm>');
  process.exit(2);
}

installDocument();

// ── the fake browser WebSocket ──────────────────────────────────────────
const opened = [];
class FakeWebSocket {
  static CONNECTING = 0;
  static OPEN = 1;
  static CLOSING = 2;
  static CLOSED = 3;
  constructor(url, protocols) {
    this.url = url;
    this.protocols = Array.isArray(protocols) ? protocols : protocols ? [protocols] : [];
    this.protocol = this.protocols[0] || '';
    this.readyState = 0;
    this.sent = [];
    this.closedWith = null;
    this._onopen = null;
    this._onmessage = null;
    this._onclose = null;
    // A socket for /raw delivers one text frame as soon as the code
    // attaches the handlers, so the imperative fixture (which drains in the
    // same export) sees a message. The game socket stays under the test's
    // control (`fireOpen`/`fireText`/`fireClose`).
    this.autoMessage = url.endsWith('/raw') ? 'hello' : undefined;
    opened.push(this);
  }
  set onopen(fn) {
    this._onopen = fn;
    this.readyState = 1;
    if (fn) fn({});
  }
  set onmessage(fn) {
    this._onmessage = fn;
    if (fn && this.autoMessage !== undefined) fn({ data: this.autoMessage });
  }
  set onclose(fn) {
    this._onclose = fn;
  }
  get onopen() { return this._onopen; }
  get onmessage() { return this._onmessage; }
  get onclose() { return this._onclose; }
  send(data) {
    if (this.readyState !== 1) throw new Error('not open');
    this.sent.push(data);
  }
  close(code, reason) {
    this.closedWith = { code, reason };
    this.readyState = 3;
    if (this._onclose) this._onclose({ code, reason, wasClean: true });
  }
  // Test-only transitions.
  fireText(text) {
    if (this._onmessage) this._onmessage({ data: text });
  }
  fireClose(code, reason) {
    this.readyState = 3;
    if (this._onclose) this._onclose({ code, reason, wasClean: true });
  }
}
globalThis.WebSocket = FakeWebSocket;

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();

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
const count = () => byId('count').textContent;

const settle = () => new Promise((r) => setTimeout(r, 0));

// ── the subscription opened exactly one socket, with its protocols ──
if (opened.length !== 1) fail(`expected one socket, the subscription opened ${opened.length}`);
const sock = opened[0];
if (sock.url !== 'ws://example.test/game') fail(`opened ${sock.url}`);
if (sock.protocols.join(',') !== 'v1') fail(`protocols were ${sock.protocols.join(',')}`);

// ── open (delivered when the host attached the handlers): the wake-up
// dispatches and update sends through ws_send ──
await settle();
instance.exports.oak_tick();
if (count() !== '1') fail(`after open the count is ${count()}`);
if (sock.sent.length !== 1) fail(`expected one sent message, got ${sock.sent.length}`);
if (sock.sent[0] !== 'hello v1') fail(`sent ${JSON.stringify(sock.sent[0])}`);

// ── a message bumps the model by ten ──
sock.fireText('tick');
await settle();
instance.exports.oak_tick();
if (count() !== '11') fail(`after a message the count is ${count()}`);

// ── close bumps by a hundred ──
sock.fireClose(1000, 'bye');
await settle();
instance.exports.oak_tick();
if (count() !== '111') fail(`after close the count is ${count()}`);

// ── the imperative socket: drain a text frame, send a binary reply, close ──
opened.length = 0;
// The export ABI returns no value, so the fixture reports through
// `console.log`; capture it.
const logs = [];
const realConsoleLog = console.log.bind(console);
console.log = (...args) => { logs.push(args.join(' ')); };
instance.exports.imp_probe();
console.log = realConsoleLog;
if (!logs.some((l) => l === 'imp:len=5')) fail(`imperative drain saw ${JSON.stringify(logs)}`);
if (opened.length !== 1) fail(`the imperative socket opened ${opened.length} sockets`);
const raw = opened[0];
if (raw.url !== 'ws://example.test/raw') fail(`the imperative socket opened ${raw.url}`);

if (raw.sent.length !== 1) fail(`the imperative socket sent ${raw.sent.length} messages`);
if (!(raw.sent[0] instanceof ArrayBuffer)) fail('the binary reply was not an ArrayBuffer');
if (new Uint8Array(raw.sent[0]).join(',') !== '1,2,3') fail('the binary reply bytes changed');
if (!raw.closedWith || raw.closedWith.code !== 1000) fail('the imperative socket was not closed');

console.log(`ok: ${path} -> oak Subscription.websocket and the imperative web_wasm socket`);
