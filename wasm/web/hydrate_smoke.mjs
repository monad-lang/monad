#!/usr/bin/env node
// SSR hydration: `Runtime.mount` adopts a matching server-rendered tree.
// Usage:
//   node wasm/web/hydrate_smoke.mjs <oak_spa_nested.wasm>
//
// The fixture's initial view is
//   div.app > [div > [p "nested", ul#items], footer > [button add, button clear]]
// This harness pre-seeds EXACTLY that markup (plus a stale attribute, a
// `data-oak` annotation, an extra child, and an extra root sibling), then
// mounts and asserts:
//   * every seeded node is still in the tree BY IDENTITY, and nothing was
//     created (`createElement` count 0);
//   * the stale class was corrected and the annotation removed;
//   * the extra child and sibling were trimmed;
//   * hydration registered the click handlers the SSR markup lacks;
//   * a later dispatch + tick still patches through the adopted nodes.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { FakeNode, body, installDocument, fail, stub } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/hydrate_smoke.mjs <oak_spa_nested.wasm>');
  process.exit(2);
}

installDocument();

// ── seed the server-rendered tree, capturing every node ──
function el(tag, attrs, children) {
  const n = new FakeNode(1, tag.toUpperCase());
  for (const [k, v] of Object.entries(attrs || {})) n.setAttribute(k, v);
  for (const c of children || []) n.appendChild(c);
  return n;
}
function tx(text) {
  const n = new FakeNode(3, '#text');
  n.nodeValue = text;
  return n;
}

const ssrText = tx('nested');
const ssrP = el('p', {}, [ssrText]);
const ssrList = el('ul', { id: 'items' }, []);
const ssrExtra = el('span', { id: 'extra' }, [tx('stale child')]);
const ssrWrapper = el('div', {}, [ssrP, ssrList, ssrExtra]);
const ssrAdd = el('button', {}, [tx('add')]);
const ssrClear = el('button', {}, [tx('clear')]);
const ssrFooter = el('footer', {}, [ssrAdd, ssrClear]);
// A stale class and an SSR annotation on the root: the class comes from the
// view, so hydration must correct it; `data-oak` is cleaned unconditionally.
const ssrRoot = el('div', { class: 'old', 'data-oak': '0' }, [ssrWrapper, ssrFooter]);
body.appendChild(ssrRoot);
const ssrSibling = el('nav', { id: 'stray' }, []);
body.appendChild(ssrSibling);

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

const createdBefore = stub.createdCount;
instance.exports.oak_mount();

// ── identity: nothing was created and every seeded node survived ──
if (stub.createdCount !== createdBefore) {
  fail(`hydration created ${stub.createdCount - createdBefore} elements, expected 0`);
}
if (body.childNodes.length !== 1 || body.childNodes[0] !== ssrRoot) {
  fail('the mount container was not trimmed to the adopted root');
}
if (ssrSibling.parentNode !== null) fail('the extra root sibling was not trimmed');
if (ssrWrapper.parentNode !== ssrRoot || ssrFooter.parentNode !== ssrRoot) {
  fail('the root children were remounted instead of adopted');
}
if (ssrP.parentNode !== ssrWrapper || ssrList.parentNode !== ssrWrapper) {
  fail('the wrapper children were remounted instead of adopted');
}
if (ssrText.parentNode !== ssrP || ssrText.textContent !== 'nested') {
  fail('the adopted text node was replaced');
}
if (ssrAdd.parentNode !== ssrFooter || ssrClear.parentNode !== ssrFooter) {
  fail('the footer buttons were remounted instead of adopted');
}
if (ssrExtra.parentNode !== null) fail('the extra SSR child was not trimmed');

// ── attribute correction and annotation cleanup ──
if (ssrRoot.attrs.class !== 'app') {
  fail(`the stale class was not corrected: ${JSON.stringify(ssrRoot.attrs)}`);
}
if ('data-oak' in ssrRoot.attrs) fail('the data-oak annotation survived hydration');

// ── hydration registered the handlers the SSR markup did not carry ──
if (!(ssrAdd.listeners.click || []).length) {
  fail('hydration did not register the add button listener');
}
if (!(ssrClear.listeners.click || []).length) {
  fail('hydration did not register the clear button listener');
}

// ── the adopted tree still patches: add two items, then clear ──
function findList() {
  const wrapper = ssrRoot.childNodes.find((n) => n.tagName === 'DIV');
  const list = wrapper.childNodes.find((n) => n.tagName === 'UL');
  if (!list) fail('the adopted ul disappeared');
  return list;
}

ssrAdd.fire('click');
instance.exports.oak_tick();
if (findList().childNodes.length !== 1) {
  fail(`after one add the adopted list has ${findList().childNodes.length} items`);
}
if (ssrFooter.parentNode !== ssrRoot) {
  fail('the patch after hydration replaced the footer');
}
ssrClear.fire('click');
instance.exports.oak_tick();
if (findList().childNodes.length !== 0) {
  fail(`after clear the adopted list has ${findList().childNodes.length} items`);
}

console.log(`ok: ${path} -> adopted the SSR tree (0 creates), corrected attrs, patch still works`);
