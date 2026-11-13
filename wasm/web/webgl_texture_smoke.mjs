#!/usr/bin/env node
// Texture state and two-phase image loading over the stub GL.
// Usage:
//   node wasm/web/webgl_texture_smoke.mjs <webgl_texture.wasm>
//
// Built from fixtures/wasm/webgl_texture.mo: `main` starts two loads, the
// harness finishes them (one fails), and the `probe` export polls and
// uploads. Checks the poll states, the upload gate and the GL stream.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';
import { installGl, glStub, finishImages } from './stub_gl.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/webgl_texture_smoke.mjs <webgl_texture.wasm>');
  process.exit(2);
}

installDocument();
installGl();

const reports = () => body.childNodes
  .filter((n) => n.attrs && n.attrs.id === 'report')
  .map((n) => n.textContent);

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.monad_main(0n);

if (glStub.contexts.length !== 1) fail(`expected one context, got ${glStub.contexts.length}`);
const gl = glStub.contexts[0];
const first = reports();
if (first.length !== 1 || first[0] !== 'polls=0,0 early=no') {
  fail(`before loading: ${JSON.stringify(first)}`);
}

finishImages();
instance.exports.probe();
const second = reports();
const want = 'polls=1,2 size=64x32 uploaded=yes failed_upload=no';
if (second[1] !== want) fail(`after loading: ${JSON.stringify(second[1])}\n want ${JSON.stringify(want)}`);

const golden = [
  ['createTexture', 'texture#1'],
  ['activeTexture', 0x84c0],
  ['bindTexture', 0x0de1, 'texture#1'],
  ['texParameteri', 0x0de1, 0x2801, 0x2703],
  ['texParameteri', 0x0de1, 0x2800, 0x2601],
  ['texParameteri', 0x0de1, 0x2802, 0x812f],
  ['texParameteri', 0x0de1, 0x2803, 0x2901],
  ['pixelStorei', 0x9240, 1],
  ['texImage2D', 0x0de1, 0, 0x1908, 0x1908, 0x1401, 'image:board.png'],
  ['generateMipmap', 0x0de1],
];
const got = JSON.stringify(gl.calls);
if (got !== JSON.stringify(golden)) fail(`GL stream differs\n got:  ${got}\n want: ${JSON.stringify(golden)}`);

console.log(`ok: ${path} -> image begin/poll, upload gate, texture state stream`);
