#!/usr/bin/env node
// WebGL from an Oak program, over the stub DOM and the recording stub GL.
// Usage:
//   node wasm/web/webgl_smoke.mjs <oak_webgl.wasm> [webgl2|webgl1|none]
//
// Built from fixtures/wasm/oak_webgl.mo. Drives the real
// `wasm/web/web_runtime.js` and the generated `web.js`, so the gl.mo
// externs, the platform_web.c wrappers and the JS host are checked against
// each other. Checks: `Command.after_render` runs after the patch (the
// canvas exists when setup queries it), canvas fit at the stub's DPR, the
// WebGL2 -> WebGL1 fallback, a compile error's info log, and the exact GL
// call stream of one setup and one drawn frame.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';
import { installGl, glStub } from './stub_gl.mjs';

const path = process.argv[2];
const mode = process.argv[3] || 'webgl2';
if (!path) {
  console.error('usage: node wasm/web/webgl_smoke.mjs <oak_webgl.wasm> [webgl2|webgl1|none]');
  process.exit(2);
}

installDocument();
installGl({ dpr: 2, clientWidth: 320, clientHeight: 200 });
glStub.mode = mode;

function byId(id) {
  const walk = (n) => {
    if (n.attrs && n.attrs.id === id) return n;
    for (const c of n.childNodes) {
      const found = walk(c);
      if (found) return found;
    }
    return null;
  };
  return walk(body);
}

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();

const status = () => byId('status').textContent;
if (!byId('board') || byId('board').tagName !== 'CANVAS') fail('the view did not mount a <canvas id="board">');
if (status() !== 'init frames=0') fail(`initial status: ${JSON.stringify(status())}`);

// Drive frames through the loader's rAF loop, with fixed timestamps.
let pending = null;
globalThis.requestAnimationFrame = (cb) => { pending = cb; };
host.start_ticks(instance);
const frame = (ts) => {
  if (typeof pending !== 'function') fail('the frame loop is not scheduled');
  const cb = pending;
  pending = null;
  cb(ts);
};

// Frame 1: update asks for setup; after the patch the effect runs, and its
// `ready` message lands in frame 2's batch.
frame(16);
if (mode === 'none') {
  frame(32);
  if (status() !== 'failed: no webgl frames=0') fail(`no-WebGL status: ${JSON.stringify(status())}`);
  console.log(`ok: ${path} [none] -> setup reports no webgl`);
  process.exit(0);
}
if (glStub.contexts.length !== 1) fail(`expected one context, got ${glStub.contexts.length}`);
const gl = glStub.contexts[0];
const want = mode === 'webgl2' ? 'webgl2' : 'webgl';
if (gl.kind !== want) fail(`context kind ${gl.kind}, want ${want}`);

const canvas = byId('board');
if (canvas.width !== 640 || canvas.height !== 400) {
  fail(`canvas_fit gave ${canvas.width}x${canvas.height}, want 640x400 (320x200 at DPR 2)`);
}

const setupCalls = gl.calls.splice(0);
gl.drawingBufferWidth = 640;
gl.drawingBufferHeight = 400;
// Frame 2's batch is [ready, frame]: `ready` stores the scene, then the frame
// message asks for a draw, which runs after this frame's patch.
frame(32);
const drawCalls = gl.calls.splice(0);
const version = mode === 'webgl2' ? 2 : 1;
const wantStatus =
  `webgl${version} fit=yes dpr=2 vao=yes badlog=ERROR: 0:1: stub compile error frames=1`;
if (status() !== wantStatus) fail(`status after setup: ${JSON.stringify(status())}\n want ${JSON.stringify(wantStatus)}`);
frame(48);
if (!status().endsWith('frames=2')) fail(`status after two draws: ${JSON.stringify(status())}`);

const setupGolden = [
  ...(mode === 'webgl1'
    ? [['getExtension', 'OES_vertex_array_object'], ['getExtension', 'OES_element_index_uint']]
    : []),
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
  ['createShader', 0x8b30, 'shader#3'],
  ['shaderSource', 'shader#3'],
  ['compileShader', 'shader#3'],
  ['deleteShader', 'shader#3'],
  ['getUniformLocation', 'program#1', 'u_time'],
];
const drawGolden = [
  ['viewport', 0, 0, 640, 400],
  ['clearColor', 0, 0, 0, 1],
  ['clear', 0x4000 | 0x100],
  ['enable', 0x0b71],
  ['useProgram', 'program#1'],
  ['uniform1f', 'uniform:u_time', 32],
  ['drawArrays', 4, 0, 3],
];

function same(got, golden, label) {
  const a = JSON.stringify(got);
  const b = JSON.stringify(golden);
  if (a !== b) {
    fail(`${label} call stream differs\n got:  ${a}\n want: ${b}`);
  }
}
same(setupCalls, setupGolden, 'setup');
same(drawCalls, drawGolden, 'draw');

// The context is lost: the host marks it, and the runtime's listener
// prevented the default so the browser may restore it.
const lostEvt = canvas.fire('webglcontextlost');
if (!lostEvt.defaultPrevented) fail('webglcontextlost was not preventDefault-ed');

console.log(`ok: ${path} [${mode}] -> after_render setup + draw, fit 640x400, golden GL stream`);
