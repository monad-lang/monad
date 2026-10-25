#!/usr/bin/env node
// Node smoke test for a nested dynamic list: the regression for
// `Patch.drop_last`. Usage:
//   node wasm/web/nested_spa_smoke.mjs <oak_spa_nested.wasm>
//
// Built from fixtures/wasm/oak_spa_nested.mo. The view is
// `div.app > [div > [p, ul#items], footer]`, so the list sits at patch path
// [0, 0, 1]. Adding an item changes the ul's child count, which emits a
// wholesale `Patch.replace` at that path; with the two-at-a-time
// `drop_last` the parent resolves to the root div and its child 1 -- the
// footer -- so the list never updates and the footer vanishes. The
// assertions below pin both.
//
// It drives the REAL `wasm/web/web_runtime.js` and the generated
// `wasm/web/web.js` over the shared stub DOM.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { body, installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/nested_spa_smoke.mjs <oak_spa_nested.wasm>');
  process.exit(2);
}

installDocument();

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.oak_mount();

function byTag(parent, tag) {
  return parent.childNodes.find((n) => n.tagName === tag);
}

const root = body.childNodes[0];
if (!root || root.tagName !== 'DIV') {
  fail(`mount did not put a div at the root: ${JSON.stringify(body.childNodes.map((n) => n.tagName))}`);
}

function findList() {
  const wrapper = byTag(root, 'DIV');
  if (!wrapper) fail('the wrapper div is missing');
  const list = byTag(wrapper, 'UL');
  if (!list) fail('the items ul is missing from the wrapper');
  return list;
}

function findFooter() {
  const footer = byTag(root, 'FOOTER');
  if (!footer) {
    fail(`the footer disappeared (root children: ${JSON.stringify(root.childNodes.map((n) => n.tagName))})`);
  }
  return footer;
}

function button(footer, label) {
  const b = footer.childNodes.find((n) => n.tagName === 'BUTTON' && n.textContent === label);
  if (!b) fail(`no "${label}" button in the footer`);
  return b;
}

if (findList().childNodes.length !== 0) fail('the list did not start empty');
findFooter();

const footer = findFooter();
button(footer, 'add').fire('click');
instance.exports.oak_tick();
if (findList().childNodes.length !== 1) {
  fail(`after one add the list has ${findList().childNodes.length} items, expected 1`);
}
if (findList().childNodes[0].textContent !== 'item') {
  fail(`the item text is ${JSON.stringify(findList().childNodes[0].textContent)}`);
}
findFooter();

button(footer, 'add').fire('click');
instance.exports.oak_tick();
if (findList().childNodes.length !== 2) {
  fail(`after two adds the list has ${findList().childNodes.length} items, expected 2`);
}
findFooter();

button(footer, 'clear').fire('click');
instance.exports.oak_tick();
if (findList().childNodes.length !== 0) {
  fail(`after clear the list has ${findList().childNodes.length} items, expected 0`);
}
findFooter();

console.log(`ok: ${path} -> nested list 0 -> 1 -> 2 -> 0 with the footer intact`);
