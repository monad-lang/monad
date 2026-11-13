// A recording stub of WebGL for the Node harnesses (CI has no browser).
//
// `installGl()` gives every stub `<canvas>` (`FakeNode` with tagName CANVAS)
// a `getContext` that returns a `FakeGL`. The fake implements exactly the
// calls `wasm/web/web_runtime.js` makes and records each one as
// `[name, ...args]` in `gl.calls`, with GL objects replaced by stable labels
// (`buffer#1`, `program#1`, ...) so a harness can compare a call stream to a
// golden. Typed-array uploads (Part B of plans/implementations/web-webgl.md)
// will record their decoded values.
//
// Modes (`glStub.mode`): 'webgl2' (default), 'webgl1' (no `webgl2` context;
// VAOs come from `OES_vertex_array_object`), or 'none' (no WebGL at all).
// A shader whose source contains `#error` fails to compile with a fixed log;
// a program linked from a shader containing `#nolink` fails to link.

import { FakeNode } from './stub_dom.mjs';

export const glStub = {
  mode: 'webgl2',
  contexts: [], // every FakeGL handed out, in order
  lost: false,
};

const CONSTANTS = {
  COMPILE_STATUS: 0x8b81,
  LINK_STATUS: 0x8b82,
  TEXTURE0: 0x84c0,
  RGBA: 0x1908,
  UNSIGNED_BYTE: 0x1401,
  UNSIGNED_INT: 0x1405,
};

class GlObject {
  constructor(kind, n) {
    this.label = `${kind}#${n}`;
  }
}

export class FakeGL {
  constructor(canvas, kind, attrs) {
    Object.assign(this, CONSTANTS);
    this.canvas = canvas;
    this.kind = kind;
    this.attrs = attrs || {};
    this.calls = [];
    this.counts = {};
    this.drawingBufferWidth = canvas.width || 300;
    this.drawingBufferHeight = canvas.height || 150;
  }

  _new(kind) {
    this.counts[kind] = (this.counts[kind] || 0) + 1;
    const obj = new GlObject(kind, this.counts[kind]);
    if (kind === 'shader') obj.source = '';
    if (kind === 'program') obj.shaders = [];
    return obj;
  }

  _rec(name, ...args) {
    this.calls.push([name, ...args.map((a) => (a instanceof GlObject ? a.label : a))]);
  }

  // ── queries ──
  isContextLost() { return glStub.lost; }
  getError() { return 0; }

  getExtension(name) {
    this._rec('getExtension', name);
    if (this.kind === 'webgl' && name === 'OES_vertex_array_object') {
      return {
        createVertexArrayOES: () => { const v = this._new('vao'); this._rec('createVertexArrayOES', v); return v; },
        bindVertexArrayOES: (v) => this._rec('bindVertexArrayOES', v),
        deleteVertexArrayOES: (v) => this._rec('deleteVertexArrayOES', v),
      };
    }
    if (name === 'OES_element_index_uint') return {};
    return null;
  }

  // ── objects ──
  createBuffer() { const o = this._new('buffer'); this._rec('createBuffer', o); return o; }
  createTexture() { const o = this._new('texture'); this._rec('createTexture', o); return o; }
  createProgram() { const o = this._new('program'); this._rec('createProgram', o); return o; }
  createShader(stage) { const o = this._new('shader'); o.stage = stage; this._rec('createShader', stage, o); return o; }

  createVertexArray() {
    if (this.kind !== 'webgl2') throw new Error('createVertexArray on a WebGL1 context');
    const o = this._new('vao');
    this._rec('createVertexArray', o);
    return o;
  }

  deleteBuffer(o) { this._rec('deleteBuffer', o); }
  deleteTexture(o) { this._rec('deleteTexture', o); }
  deleteProgram(o) { this._rec('deleteProgram', o); }
  deleteShader(o) { this._rec('deleteShader', o); }
  deleteVertexArray(o) { this._rec('deleteVertexArray', o); }

  bindBuffer(t, o) { this._rec('bindBuffer', t, o); }
  bindTexture(t, o) { this._rec('bindTexture', t, o); }
  bindVertexArray(o) { this._rec('bindVertexArray', o); }
  useProgram(o) { this._rec('useProgram', o); }

  // ── shaders and programs ──
  shaderSource(sh, src) { sh.source = src; this._rec('shaderSource', sh); }
  compileShader(sh) { this._rec('compileShader', sh); }

  getShaderParameter(sh, p) {
    if (p === CONSTANTS.COMPILE_STATUS) return !sh.source.includes('#error');
    return null;
  }

  getShaderInfoLog(sh) {
    return sh.source.includes('#error') ? 'ERROR: 0:1: stub compile error' : '';
  }

  attachShader(p, sh) { p.shaders.push(sh); this._rec('attachShader', p, sh); }
  linkProgram(p) { this._rec('linkProgram', p); }

  getProgramParameter(p, pname) {
    if (pname === CONSTANTS.LINK_STATUS) return !p.shaders.some((s) => s.source.includes('#nolink'));
    return null;
  }

  getProgramInfoLog(p) {
    return this.getProgramParameter(p, CONSTANTS.LINK_STATUS) ? '' : 'stub link error';
  }

  getAttribLocation(p, name) {
    this._rec('getAttribLocation', p, name);
    return name === 'a_position' ? 0 : name === 'a_uv' ? 1 : -1;
  }

  getUniformLocation(p, name) {
    this._rec('getUniformLocation', p, name);
    if (name.startsWith('u_')) {
      const o = this._new('uniform');
      o.label = `uniform:${name}`;
      return o;
    }
    return null;
  }

  // ── attributes and uniforms ──
  vertexAttribPointer(...a) { this._rec('vertexAttribPointer', ...a); }
  enableVertexAttribArray(i) { this._rec('enableVertexAttribArray', i); }
  disableVertexAttribArray(i) { this._rec('disableVertexAttribArray', i); }
  uniform1f(l, x) { this._rec('uniform1f', l, x); }
  uniform2f(l, x, y) { this._rec('uniform2f', l, x, y); }
  uniform3f(l, x, y, z) { this._rec('uniform3f', l, x, y, z); }
  uniform4f(l, x, y, z, w) { this._rec('uniform4f', l, x, y, z, w); }
  uniform1i(l, x) { this._rec('uniform1i', l, x); }

  // ── state and drawing ──
  clearColor(r, g, b, a) { this._rec('clearColor', r, g, b, a); }
  clear(mask) { this._rec('clear', mask); }
  viewport(x, y, w, h) { this._rec('viewport', x, y, w, h); }
  enable(c) { this._rec('enable', c); }
  disable(c) { this._rec('disable', c); }
  blendFunc(s, d) { this._rec('blendFunc', s, d); }
  depthFunc(f) { this._rec('depthFunc', f); }
  depthMask(m) { this._rec('depthMask', m); }
  cullFace(f) { this._rec('cullFace', f); }
  frontFace(w) { this._rec('frontFace', w); }
  activeTexture(u) { this._rec('activeTexture', u); }
  generateMipmap(t) { this._rec('generateMipmap', t); }
  texParameteri(t, p, v) { this._rec('texParameteri', t, p, v); }
  pixelStorei(p, v) { this._rec('pixelStorei', p, v); }
  drawArrays(m, f, c) { this._rec('drawArrays', m, f, c); }
  drawElements(m, c, t, o) { this._rec('drawElements', m, c, t, o); }

  texImage2D(target, level, internal, format, type, source) {
    const what = source && source.src !== undefined ? `image:${source.src}` : 'pixels';
    this._rec('texImage2D', target, level, internal, format, type, what);
  }
}

/// A stub `Image`: loading resolves when the harness calls
/// `finishImages()`; a src containing `missing` fails.
export class FakeImage {
  constructor() {
    this.onload = null;
    this.onerror = null;
    this.naturalWidth = 0;
    this.naturalHeight = 0;
    this._src = '';
    FakeImage.pending.push(this);
  }

  set src(v) { this._src = v; }
  get src() { return this._src; }
}
FakeImage.pending = [];

export function finishImages() {
  const all = FakeImage.pending.splice(0);
  for (const img of all) {
    if (img._src.includes('missing')) {
      if (img.onerror) img.onerror(new Error('404'));
    } else {
      img.naturalWidth = 64;
      img.naturalHeight = 32;
      if (img.onload) img.onload();
    }
  }
}

/// Give stub canvases a WebGL `getContext`, a CSS size, and the window a
/// `devicePixelRatio`. Call after `installDocument()`.
export function installGl({ dpr = 2, clientWidth = 320, clientHeight = 200 } = {}) {
  globalThis.devicePixelRatio = dpr;
  globalThis.Image = FakeImage;
  const cache = new WeakMap(); // canvas -> FakeGL: getContext is idempotent
  FakeNode.prototype.getContext = function getContext(kind, attrs) {
    if (this.tagName !== 'CANVAS') return null;
    if (glStub.mode === 'none') return null;
    if (kind === 'webgl2' && glStub.mode !== 'webgl2') return null;
    if (kind !== 'webgl' && kind !== 'webgl2') return null;
    const known = cache.get(this);
    if (known) return known;
    const gl = new FakeGL(this, kind, attrs);
    cache.set(this, gl);
    glStub.contexts.push(gl);
    return gl;
  };
  Object.defineProperty(FakeNode.prototype, 'clientWidth', {
    configurable: true,
    get() { return this.tagName === 'CANVAS' ? clientWidth : 0; },
  });
  Object.defineProperty(FakeNode.prototype, 'clientHeight', {
    configurable: true,
    get() { return this.tagName === 'CANVAS' ? clientHeight : 0; },
  });
}
