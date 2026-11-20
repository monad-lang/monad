#!/usr/bin/env node
// Render targets (framebuffer + depth texture) over the stub GL.
// Usage:
//   node wasm/web/smoke/webgl_shadow_smoke.mjs <webgl_shadow.wasm> [webgl2|webgl1|webgl1-nodepth|incomplete|none]
//
// Built from fixtures/wasm/webgl_shadow.mo. Checks the report and the
// render-target part of the GL stream: depth allocation per context kind,
// the attach/complete check, a colour-masked and polygon-offset depth pass,
// then the quad pass on the default framebuffer. `webgl1-nodepth` is WebGL1
// without WEBGL_depth_texture: the depth pass must be skipped cleanly.
// `incomplete` is WebGL2 whose framebuffer check fails: nothing is drawn.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';
import { installGl, glStub } from './stub_gl.mjs';

const path = process.argv[2];
const mode = process.argv[3] || 'webgl2';
if (!path) {
  console.error('usage: node wasm/web/smoke/webgl_shadow_smoke.mjs <webgl_shadow.wasm> [webgl2|webgl1|webgl1-nodepth|incomplete|none]');
  process.exit(2);
}

installDocument();
installGl();
if (mode === 'webgl1-nodepth') {
  glStub.mode = 'webgl1';
  glStub.noDepthTexture = true;
} else if (mode === 'incomplete') {
  glStub.incompleteFramebuffer = true;
} else {
  glStub.mode = mode;
}

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.monad_main(0n);

const reports = body.childNodes
  .filter((n) => n.attrs && n.attrs.id === 'report')
  .map((n) => n.textContent);

const wantReport = {
  webgl2: 'has_depth=yes quad=yes zero_size=no depth=yes complete=yes',
  webgl1: 'has_depth=yes quad=yes zero_size=no depth=yes complete=yes',
  'webgl1-nodepth': 'has_depth=no quad=yes zero_size=no depth=no skipped',
  incomplete: 'has_depth=yes quad=yes zero_size=no depth=yes complete=no',
  none: 'no webgl',
}[mode];
if (wantReport === undefined) fail(`unknown mode ${mode}`);
if (reports.length !== 1 || reports[0] !== wantReport) {
  fail(`report: ${JSON.stringify(reports)}\n want ${JSON.stringify(wantReport)}`);
}

if (mode === 'none') {
  console.log(`ok: ${path} [none] -> no context, no trap`);
  process.exit(0);
}

const gl = glStub.contexts[0];
// Only the calls this fixture is about; shader compiles and attribute
// setup are covered by the other WebGL smokes.
const keep = new Set([
  'getExtension', 'createFramebuffer', 'bindFramebuffer', 'deleteFramebuffer',
  'framebufferTexture2D', 'checkFramebufferStatus', 'texImage2D', 'colorMask',
  'polygonOffset', 'enable', 'disable', 'clear', 'viewport', 'drawArrays', 'bindTexture',
]);
const got = gl.calls.filter((c) => keep.has(c[0]));

const TEX = 0x0de1;
const FB = 0x8d40;
const DEPTH_ATTACHMENT = 0x8d00;
const depthAlloc = mode === 'webgl2' || mode === 'incomplete'
  ? ['texImage2D', TEX, 0, 0x81a6, 512, 512, 0, 0x1902, 0x1405, null]
  : ['texImage2D', TEX, 0, 0x1902, 512, 512, 0, 0x1902, 0x1403, null];
const webgl1Probes = [
  ['getExtension', 'OES_vertex_array_object'],
  ['getExtension', 'OES_element_index_uint'],
  ['getExtension', 'WEBGL_depth_texture'],
];

let golden;
if (mode === 'webgl1-nodepth') {
  golden = [...webgl1Probes, ['bindTexture', TEX, 'texture#1']];
} else if (mode === 'incomplete') {
  golden = [
    ['bindTexture', TEX, 'texture#1'],
    depthAlloc,
    ['createFramebuffer', 'framebuffer#1'],
    ['bindFramebuffer', FB, 'framebuffer#1'],
    ['framebufferTexture2D', FB, DEPTH_ATTACHMENT, TEX, 'texture#1', 0],
    ['checkFramebufferStatus', FB],
    ['bindFramebuffer', FB, null],
    ['deleteFramebuffer', 'framebuffer#1'],
  ];
} else {
  golden = [
    ...(mode === 'webgl1' ? webgl1Probes : []),
    ['bindTexture', TEX, 'texture#1'],
    depthAlloc,
    ['createFramebuffer', 'framebuffer#1'],
    ['bindFramebuffer', FB, 'framebuffer#1'],
    ['framebufferTexture2D', FB, DEPTH_ATTACHMENT, TEX, 'texture#1', 0],
    ['checkFramebufferStatus', FB],
    ['viewport', 0, 0, 512, 512],
    ['colorMask', false, false, false, false],
    ['enable', 0x0b71],
    ['enable', 0x8037],
    ['polygonOffset', 2, 4],
    ['clear', 0x100],
    ['drawArrays', 4, 0, 3],
    ['disable', 0x8037],
    ['colorMask', true, true, true, true],
    ['bindFramebuffer', FB, null],
    ['viewport', 0, 0, 640, 400],
    ['bindTexture', TEX, 'texture#1'],
    ['drawArrays', 5, 0, 4],
    ['deleteFramebuffer', 'framebuffer#1'],
  ];
}
if (JSON.stringify(got) !== JSON.stringify(golden)) {
  fail(`GL stream differs\n got:  ${JSON.stringify(got)}\n want: ${JSON.stringify(golden)}`);
}

const what = {
  'webgl1-nodepth': 'no depth texture, passes skipped',
  incomplete: 'incomplete framebuffer, passes skipped',
}[mode] || 'depth texture, framebuffer, depth pass, quad pass';
console.log(`ok: ${path} [${mode}] -> ${what}`);
