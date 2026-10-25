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
import { body, installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/dom_smoke.mjs <web_dom.wasm>');
  process.exit(2);
}

installDocument();

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
