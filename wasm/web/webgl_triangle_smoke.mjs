#!/usr/bin/env node
// Buffered drawing through `std::buf` over the stub GL.
// Usage:
//   node wasm/web/webgl_triangle_smoke.mjs <webgl_triangle.wasm> [webgl2|webgl1-nouint]
//
// Built from fixtures/wasm/webgl_triangle.mo. Checks that `Buf F32`/`I32`/
// `U8` uploads reach the host as their decoded values (F32 rounding
// included), that a short matrix or pixel buffer is refused before the
// host, and the exact GL call stream. `webgl1-nouint` is a WebGL1 context
// without OES_element_index_uint: `Gl.has_uint_indices` must say no.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';
import { installGl, glStub } from './stub_gl.mjs';

const path = process.argv[2];
const mode = process.argv[3] || 'webgl2';
if (!path) {
  console.error('usage: node wasm/web/webgl_triangle_smoke.mjs <webgl_triangle.wasm> [webgl2|webgl1-nouint]');
  process.exit(2);
}

installDocument();
installGl();
if (mode === 'webgl1-nouint') {
  glStub.mode = 'webgl1';
  glStub.noUintIndices = true;
}

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.monad_main(0n);

const reports = body.childNodes
  .filter((n) => n.attrs && n.attrs.id === 'report')
  .map((n) => n.textContent);
const uint = mode === 'webgl2' ? 'yes' : 'no';
const want = `uint=${uint} vertices=yes sub=yes indices=yes mat4=yes short_mat4=no texture=yes short_texture=no`;
if (reports.length !== 1 || reports[0] !== want) {
  fail(`report: ${JSON.stringify(reports)}\n want ${JSON.stringify(want)}`);
}

if (glStub.contexts.length !== 1) fail(`expected one context, got ${glStub.contexts.length}`);
const gl = glStub.contexts[0];
const identity = [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1];
const golden = [
  ...(mode === 'webgl2'
    ? []
    : [['getExtension', 'OES_vertex_array_object'], ['getExtension', 'OES_element_index_uint']]),
  ['createShader', 0x8b31, 'shader#1'],
  ['shaderSource', 'shader#1'],
  ['compileShader', 'shader#1'],
  ['createShader', 0x8b30, 'shader#2'],
  ['shaderSource', 'shader#2'],
  ['compileShader', 'shader#2'],
  ['createProgram', 'program#1'],
  ['attachShader', 'program#1', 'shader#1'],
  ['attachShader', 'program#1', 'shader#2'],
  ['linkProgram', 'program#1'],
  ['deleteShader', 'shader#1'],
  ['deleteShader', 'shader#2'],
  ['createBuffer', 'buffer#1'],
  ['bindBuffer', 0x8892, 'buffer#1'],
  ['bufferData', 0x8892, [0, 0.5, -0.5, -0.5, 0.5, -0.5], 0x88e4],
  ['bufferSubData', 0x8892, 0, [0.25, 0.75]],
  ['createBuffer', 'buffer#2'],
  ['bindBuffer', 0x8893, 'buffer#2'],
  ['bufferData', 0x8893, [0, 1, 2], 0x88e4],
  ['useProgram', 'program#1'],
  ['getAttribLocation', 'program#1', 'a_position'],
  ['vertexAttribPointer', 0, 2, 0x1406, false, 0, 0],
  ['enableVertexAttribArray', 0],
  ['getUniformLocation', 'program#1', 'u_mvp'],
  ['uniformMatrix4fv', 'uniform:u_mvp', false, identity],
  ['createTexture', 'texture#1'],
  ['bindTexture', 0x0de1, 'texture#1'],
  ['texImage2D', 0x0de1, 0, 0x1908, 2, 1, 0, 0x1908, 0x1401, [255, 0, 0, 255, 0, 44, 0, 255]],
  ['drawElements', 4, 3, 0x1405, 0],
];
const got = JSON.stringify(gl.calls);
if (got !== JSON.stringify(golden)) {
  fail(`GL stream differs\n got:  ${got}\n want: ${JSON.stringify(golden)}`);
}

console.log(`ok: ${path} [${mode}] -> Buf F32/I32/U8 uploads, refusals, golden GL stream`);
