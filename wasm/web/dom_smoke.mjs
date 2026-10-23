#!/usr/bin/env node
// Node smoke test for the `web_wasm` DOM surface. Usage:
//   node wasm/web/dom_smoke.mjs <web_dom.wasm>
//
// Built from fixtures/wasm/web_dom.mo: it appends a div#probe containing a
// text node under the mount root. This test drives the REAL
// `wasm/web/web_runtime.js` and the generated `wasm/web/web.js` import
// object over a minimal stub DOM, so the externs, the C wrappers and the JS
// host are checked against each other -- not against hand-written mocks of
// each side.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/dom_smoke.mjs <web_dom.wasm>');
  process.exit(2);
}

class FakeNode {
  constructor(nodeType, tagName) {
    this.nodeType = nodeType;
    this.tagName = tagName;
    this.childNodes = [];
    this.attrs = {};
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

  addEventListener() {}

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

const body = new FakeNode(1, 'BODY');
globalThis.document = {
  body,
  querySelector(selector) {
    return selector === 'body' || selector === '#app' ? body : null;
  },
  createElement(tag) {
    return new FakeNode(1, tag.toUpperCase());
  },
  createTextNode(text) {
    const n = new FakeNode(3, '#text');
    n.nodeValue = text;
    return n;
  },
};

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.monad_main(0n);

const div = body.childNodes.find((n) => n.tagName === 'DIV');
if (!div) {
  console.error('no <div> was appended to the root');
  process.exit(1);
}
if (div.attrs.id !== 'probe') {
  console.error(`div has no id="probe": ${JSON.stringify(div.attrs)}`);
  process.exit(1);
}
if (div.textContent !== 'hello from wasm') {
  console.error(`unexpected text: ${JSON.stringify(div.textContent)}`);
  process.exit(1);
}

console.log(`ok: ${path} -> <div id="probe">hello from wasm</div> under #app`);
