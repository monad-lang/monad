#!/usr/bin/env node
// Node smoke test for trellis's browser UI. Usage:
//   node wasm/web/smoke/trellis_ui_smoke.mjs <trellis_ui.wasm>
//
// Built from `motes/trellis_ui` (`--bin trellis_ui`). Drives the REAL
// `web_runtime.js` and generated `web.js` over `stub_dom.mjs`, with a stub
// `fetch` serving a small `trellis 1` graph, and checks end to end:
//   * the first frame starts the fetch, the poll timer delivers the body,
//     and the module-level graph draws;
//   * the drawing is SVG: `<svg>` and everything below it is created in the
//     SVG namespace (the oak_wasm patch's namespace rule), HTML around it is
//     not;
//   * typing in the search box ranks a declaration, Enter picks it, and the
//     view switches to declarations with the pick selected;
//   * a re-render that swaps nodes inside the drawing keeps them in the SVG
//     namespace (`dom_in_svg` on the parent).

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { body, installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/smoke/trellis_ui_smoke.mjs <trellis_ui.wasm>');
  process.exit(2);
}

const SVG = 'http://www.w3.org/2000/svg';
const graph = [
  'trellis\t1',
  'R\tdemo',
  'M\tdemo::infer\tdemo\tdemo/src/infer.mo\t0',
  'M\tdemo::unify\tdemo\tdemo/src/unify.mo\t0',
  'D\t0\tcheck\tdef\tpub\t3\t\t\t',
  'D\t0\tinfer\tdef\tpub\t9\t\t\t',
  'D\t1\tunify\tdef\tpub\t4\t\t\t',
  'D\t1\twhnf\tdef\tpub\t20\t\t\t',
  'E\t0\t1\tb',
  'E\t1\t2\tb',
  'E\t2\t3\tb',
  'S\t3\t3\t0',
].join('\n');

let fetched = null;
globalThis.fetch = (url) => {
  fetched = url;
  const bytes = new TextEncoder().encode(graph);
  return Promise.resolve({
    status: 200,
    headers: { forEach() {} },
    arrayBuffer: () => Promise.resolve(bytes.buffer),
  });
};

let pendingFrame = null;
globalThis.requestAnimationFrame = (cb) => { pendingFrame = cb; return 1; };
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
const tick = () => instance.exports.oak_tick();
const settle = async () => {
  for (let i = 0; i < 20; i += 1) {
    await new Promise((r) => setTimeout(r, 40));
    tick();
  }
};

function findAll(node, pred, acc = []) {
  for (const child of node.childNodes) {
    if (child.nodeType === 1) {
      if (pred(child)) acc.push(child);
      findAll(child, pred, acc);
    }
  }
  return acc;
}
const all = (pred) => findAll(body, pred);
const one = (pred, what) => {
  const found = all(pred)[0];
  if (!found) fail(`not found: ${what}`);
  return found;
};
const hasClass = (n, c) => (n.attrs.class || '').split(' ').includes(c);
const nodes = () => all((n) => hasClass(n, 'oak-graph__node'));
const text = (n) => n.textContent;

// 1. Load: the first frame starts the fetch; polling delivers the graph.
frame();
tick();
await settle();
if (fetched !== 'graph.tsv') fail(`fetched ${JSON.stringify(fetched)}, expected graph.tsv`);
const svg = one((n) => n.localName === 'svg' || n.tagName === 'svg', 'the graph <svg>');
if (nodes().length !== 2) fail(`module level should draw 2 modules, drew ${nodes().length}`);

// 2. Namespaces: the svg subtree is SVG, the page around it is not.
if (svg.namespaceURI !== SVG) fail(`<svg> created in namespace ${svg.namespaceURI}`);
const inside = findAll(svg, () => true);
const strays = inside.filter((n) => n.namespaceURI !== SVG);
if (inside.length < 6 || strays.length > 0) {
  fail(`svg subtree: ${inside.length} elements, ${strays.length} outside the SVG namespace (${strays.map((n) => n.tagName).join(', ')})`);
}
const html = one((n) => n.tagName === 'INPUT', 'the search input');
if (html.namespaceURI === SVG) fail('an HTML element was created in the SVG namespace');

// 3. Search, then Enter picks the best hit.
html.value = 'whnf';
html.fire('input');
tick();
const hits = all((n) => hasClass(n, 'trellis-hit'));
if (hits.length === 0) fail('typing "whnf" produced no hits');
const enter = html.fire('keydown', { key: 'Enter' });
if (!enter.defaultPrevented) fail('Enter in the search box was not default-prevented');
tick();
const labels = nodes().map(text);
if (!labels.some((l) => l.includes('whnf')) || !labels.some((l) => l.includes('unify'))) {
  fail(`after picking whnf the drawing shows ${JSON.stringify(labels)}`);
}
one((n) => hasClass(n, 'oak-graph__node--selected'), 'the selected whnf node');

// 4. The re-render replaced nodes inside the drawing: still all SVG.
const after = findAll(one((n) => n.localName === 'svg' || n.tagName === 'svg', 'the redrawn <svg>'), () => true);
const strays2 = after.filter((n) => n.namespaceURI !== SVG);
if (strays2.length > 0) fail(`after re-render ${strays2.length} svg-subtree elements left the SVG namespace`);

console.log(`ok: ${path} -> loads graph.tsv, draws SVG in its namespace, fuzzy-picks a declaration and redraws`);
