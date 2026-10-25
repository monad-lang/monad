#!/usr/bin/env node
// Node smoke test for keyed list reconciliation. Usage:
//   node wasm/web/keyed_spa_smoke.mjs <oak_spa_keyed.wasm>
//
// Built from fixtures/wasm/oak_spa_keyed.mo, whose initial list is
// `a, b, c` of keyed, clickable `<li>`s. The assertions are about NODE
// IDENTITY, which is the whole point of a keyed diff:
//   * reverse keeps the same three objects, reordered, and creates none;
//   * a moved item keeps its click listener;
//   * add mounts exactly one new element and leaves the others alone;
//   * drop detaches the first item and leaves the survivors in order.
//
// It drives the REAL `wasm/web/web_runtime.js` and the generated
// `wasm/web/web.js` over the shared stub DOM.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { body, installDocument, fail, stub } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/keyed_spa_smoke.mjs <oak_spa_keyed.wasm>');
  process.exit(2);
}

installDocument();

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

instance.exports.oak_mount();

const root = body.childNodes[0];
if (!root || root.tagName !== 'DIV') fail('mount did not put a div at the root');
const list = root.childNodes.find((n) => n.tagName === 'UL');
if (!list) fail('the items ul is missing');

const [a, b, c] = list.childNodes;
if (list.childNodes.length !== 3) fail(`expected 3 items, got ${list.childNodes.length}`);
if (a.textContent !== 'a' || b.textContent !== 'b' || c.textContent !== 'c') {
  fail(`unexpected initial items: ${JSON.stringify(list.childNodes.map((n) => n.textContent))}`);
}

function expectOrder(want, why) {
  const got = list.childNodes.map((n) => n.textContent);
  if (got.join(',') !== want.join(',')) {
    fail(`${why}: got ${JSON.stringify(got)}, expected ${JSON.stringify(want)}`);
  }
}

// ── reverse: same objects, reversed; zero creates ──
const createdBefore = stub.createdCount;
a.fire('click');
instance.exports.oak_tick();
expectOrder(['c', 'b', 'a'], 'reverse');
if (list.childNodes[0] !== c || list.childNodes[1] !== b || list.childNodes[2] !== a) {
  fail('reverse reordered by remounting instead of moving the existing nodes');
}
if (stub.createdCount !== createdBefore) {
  fail(`reverse created ${stub.createdCount - createdBefore} elements, expected 0`);
}
if (!(c.listeners.click || []).length) {
  fail('the moved item lost its click listener');
}

// ── the moved item still dispatches: click c (now first), tick, reverse ──
c.fire('click');
instance.exports.oak_tick();
expectOrder(['a', 'b', 'c'], 'reverse via a moved listener');

// ── add: one fresh element, the rest untouched ──
const createdBeforeAdd = stub.createdCount;
const [a2, b2, c2] = list.childNodes;
const addButton = root.childNodes
  .find((n) => n.tagName === 'DIV')
  .childNodes.find((n) => n.tagName === 'BUTTON' && n.textContent === 'add');
if (!addButton) fail('no add button');
addButton.fire('click');
instance.exports.oak_tick();
expectOrder(['a', 'b', 'c', 'item3'], 'add');
if (list.childNodes[0] !== a2 || list.childNodes[1] !== b2 || list.childNodes[2] !== c2) {
  fail('add remounted existing items');
}
if (stub.createdCount - createdBeforeAdd !== 1) {
  fail(`add created ${stub.createdCount - createdBeforeAdd} elements, expected 1`);
}

// ── drop: the first item is detached, survivors keep identity ──
const dropButton = root.childNodes
  .find((n) => n.tagName === 'DIV')
  .childNodes.find((n) => n.tagName === 'BUTTON' && n.textContent === 'drop');
if (!dropButton) fail('no drop button');
const removed = list.childNodes[0];
dropButton.fire('click');
instance.exports.oak_tick();
expectOrder(['b', 'c', 'item3'], 'drop');
if (removed.parentNode !== null) fail('the dropped item is still attached');
if (list.childNodes[0] !== b2 || list.childNodes[1] !== c2) {
  fail('drop remounted the survivors');
}

console.log(`ok: ${path} -> keyed reverse/add/drop preserved node identity`);
