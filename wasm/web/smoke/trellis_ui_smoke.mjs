#!/usr/bin/env node
// Node smoke test for trellis's browser UI. Usage:
//   node wasm/web/smoke/trellis_ui_smoke.mjs <trellis_ui.wasm>
//
// Built from `motes/trellis_ui` (`--bin trellis_ui`). Drives the REAL
// `web_runtime.js` and generated `web.js` over `stub_dom.mjs`, with a stub
// `fetch` serving a small `trellis 2` graph, and checks end to end:
//   * the first frame starts the fetch, the poll timer delivers the body,
//     and the module-level graph draws;
//   * the drawing is SVG: `<svg>` and everything below it is created in the
//     SVG namespace (the oak_wasm patch's namespace rule), HTML around it is
//     not;
//   * typing in the search box ranks a declaration, Enter picks it, and the
//     view switches to declarations with the pick selected;
//   * a re-render that swaps nodes inside the drawing keeps them in the SVG
//     namespace (`dom_in_svg` on the parent);
//   * the picked declaration's doc comment (markdown in the graph file) is
//     rendered as real elements in the detail panel;
//   * the drawing is fitted (a nested `<svg viewBox>`);
//   * a view over the node cap shows the section browser, and opening a
//     section draws just that section.

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
// 130 declarations in demo::big: at the declaration level with a cap of
// 100 the view (134 nodes) is split into sections.
const big = Array.from({ length: 130 }, (_, i) => `D\t2\tbig_${i}\tdef\tpub\t${i + 1}\t\t\t\t`);
const graph = [
  'trellis\t2',
  'R\tdemo',
  'M\tdemo::infer\tdemo\tdemo/src/infer.mo\t0\tThe checker.',
  'M\tdemo::unify\tdemo\tdemo/src/unify.mo\t0\t',
  'M\tdemo::big\tdemo\tdemo/src/big.mo\t0\t',
  'D\t0\tcheck\tdef\tpub\t3\t\t\t\t',
  'D\t0\tinfer\tdef\tpub\t9\t\t\t\t',
  'D\t1\tunify\tdef\tpub\t4\t\t\t\t',
  'D\t1\twhnf\tdef\tpub\t20\t\t\t\tWeak head normal form of `t`.\\n\\nNever *unfolds* a let.',
  ...big,
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
if (nodes().length !== 3) fail(`module level should draw 3 modules, drew ${nodes().length}`);
one((n) => hasClass(n, 'oak-graph__fit') && n.attrs.viewBox, 'the fitted drawing (nested <svg viewBox>)');

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

// 5. The pick's doc comment, rendered from markdown into elements.
const doc = one((n) => hasClass(n, 'trellis-doc'), 'the rendered doc comment');
const code = findAll(doc, (n) => n.tagName === 'CODE');
const em = findAll(doc, (n) => n.tagName === 'EM');
const paras = findAll(doc, (n) => n.tagName === 'P');
if (code.length !== 1 || text(code[0]) !== 't' || em.length !== 1 || paras.length !== 2) {
  fail(`doc comment rendered as ${JSON.stringify(text(doc))} (${paras.length} p, ${code.length} code, ${em.length} em)`);
}

// 6. Over the cap: declarations, no focus, cap 100 -> the section browser.
const clear = all((n) => n.tagName === 'BUTTON' && text(n) === 'Clear focus')[0];
if (!clear) fail('no Clear focus button after the pick');
clear.fire('click');
tick();
const cap = one((n) => n.tagName === 'SELECT' && n.attrs.id === 'trellis-cap', 'the Max nodes select');
cap.value = '100';
cap.fire('change');
tick();
const cards = all((n) => hasClass(n, 'trellis-section'));
const bigCards = cards.filter((n) => text(n).includes('demo::big'));
if (cards.length !== 4 || bigCards.length !== 2 || nodes().length !== 0) {
  fail(`section browser: ${cards.length} sections (${bigCards.length} for demo::big), ${nodes().length} nodes drawn`);
}
bigCards[1].fire('click');
tick();
if (nodes().length !== 30) fail(`opening demo::big (2/2) should draw 30 nodes, drew ${nodes().length}`);
one((n) => hasClass(n, 'trellis-sectionbar'), 'the section bar');

console.log(`ok: ${path} -> loads graph.tsv, draws fitted SVG in its namespace, fuzzy-picks a declaration, `
  + 'renders its docs, and browses an oversized view by section');
