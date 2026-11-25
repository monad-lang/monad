// The browser host behind the generated loader (`web.js`).
//
// This file is the ONLY hand-written JavaScript at the web boundary: the
// import object `web.js` passes to `WebAssembly.instantiateStreaming` maps
// every `WebAbi` import name onto `host.<name>`, and `runtime/src/platform_web.c`
// declares the matching `web_*` externs. Edit the names here only together
// with `motes/web_wasm/src/web_abi.mo` and the C wrappers.
//
// Conventions:
//   * a Monad String crosses as (pointer, byte length) into the wasm memory;
//     it is decoded as UTF-8;
//   * a string RESULT is written into a caller-supplied wasm buffer and its
//     byte length returned (the C wrapper copies it into a Monad string);
//   * a Node/RequestId is an opaque integer id; JS owns the table. Id 0 is
//     the null handle.
//
// `set_root` / `bind` / `start_ticks` are the loader's half of the contract:
// the selector never crosses the wasm ABI (it is a JS string), DOM listeners
// call the exported `oak_dispatch_event` through the bound instance, and
// `oak_tick` is driven from requestAnimationFrame.

import { f64ToRustString } from './float_format.js';

let instance = null;
let memory = null;
let rootSelector = 'body';
let tryResult = null; // the last /try engine result (see `try_result`)
// The /try worker channel (main thread only; the engine worker never
// calls these). A fresh Worker per run bounds the engine's heap (nothing
// is collected while `try_run` is running, and linear memory never
// shrinks), and terminating it is what Cancel does.
let tryWorker = null;
let workerState = 0; // 0 idle, 1 running, 2 done, 3 timeout, 4 failed
let workerResult = null;
let workerSeq = 0;
let workerTimer = null;
// The timer covers two phases with different budgets: loading the engine
// (fetch + compile, which dominates on a slow link) and then evaluation.
// `worker.js` posts `started` when the instance is up, which switches to
// the evaluation backstop. Fuel is the primary bound; this is the wall
// clock for the front end, which has no fuel.
const WORKER_LOAD_TIMEOUT_MS = 30000;
const WORKER_EVAL_TIMEOUT_MS = 30000;

const nodes = [null]; // id -> DOM node; 0 is the null handle
const nodeIds = new WeakMap(); // node -> id, so a re-read keeps its handle
const listenerTables = new WeakMap(); // node -> Map(event -> { id, wrapper })
const globalTables = new Map(); // "target:event" -> { flags, wrapper }
let frameHandler = null; // the animation-frame subscription's handler id
const fetches = []; // id -> { state, status, bytes, offset, headers }
const clips = []; // id -> { state, text, error }
// Live sockets: id -> { ws, queue, handler, state, code, reason, clean }.
// `queue` holds decoded entries { kind, bytes }: kind 1 open, 2 text,
// 3 binary, 4 close, 5 error. A socket's callbacks only append; the wasm
// side drains them (`ws_read`) and, when watched, a coalesced
// `dispatchWith` wakes the app from a fresh task.
const sockets = [];
const cryptos = []; // id -> { state, hex, error, key }
// ECDSA P-256 keypairs (id -> CryptoKey or CryptoKeyPair). The PRIVATE half
// lives only here, in the host: it is non-extractable, so neither wasm nor
// this file can read it back out -- only sign with it.
const webKeys = [null]; // id -> CryptoKey | CryptoKeyPair; 0 is the null handle
const mediaTables = new Map(); // query -> { mql, wrapper }
// WebGL (`motes/web_wasm/src/gl.mo`). A context id names { gl, version,
// vao }: `vao` is the WebGL1 `OES_vertex_array_object` extension (null on
// WebGL2, which has VAOs in core). Objects of every kind share one table;
// id 0 is the null handle. `glLog` holds the last compile/link info log.
const glContexts = [null]; // id -> { gl, version, vao, uint, depthTex, canvas }
const glContextIds = new WeakMap(); // GL context -> id, so a re-get keeps its id
const glObjects = [null]; // id -> { ctx, kind, obj }
let glLog = '';
const images = [null]; // id -> { state, img }
// Web Audio (`motes/web_wasm/src/audio.mo`). `audioCtx` is the page's single
// `AudioContext` plus its master gain node; a context id of 0 means "not
// open". Decoded sounds, live voices and in-flight decodes each get their own
// table, so a handle can never be mistaken for another kind.
let audioCtx = null;
let audioMaster = null;
let audioCtxId = 0n;
const audioSounds = [null]; // id -> AudioBuffer
const audioNodes = [null]; // id -> AudioNode | AudioScheduledSourceNode
const audioDecodes = []; // id -> { state, buffer, error }
let timerSeq = 0n;
// Handler ids are masked to 31 bits (`Handler.id`), so the top bit is a
// disjoint space for timer callbacks.
const TIMER_BASE = 0x80000000n;

const EVENT_PREFIX = 'data-oak-on-';
const EVENT_FLAGS = 'cdsopr';
const FOCUS_TRAP_ATTR = 'data-oak-focus-trap';
const FOCUSABLE =
  'a[href],button:not([disabled]),input:not([disabled]),select:not([disabled]),' +
  'textarea:not([disabled]),[tabindex]:not([tabindex="-1"])';
const focusTraps = new WeakMap();

// The live event, set only for the duration of the synchronous
// `oak_dispatch_event` export call. Getters read it; after the call it is
// restored, so an event read from a later tick is `valid = 0`.
let currentEvent = null;

// Wake a watched socket's app once per task: the queue may gain several
// entries in one callback burst, and one dispatch drains them all.
function socket_wake(rec) {
  if (rec.scheduled) return;
  rec.scheduled = true;
  const hid = rec.handler;
  setTimeout(() => {
    dispatchWith({ type: 'websocket', timeStamp: Date.now() }, hid);
  }, 0);
}

function dispatchWith(evt, id) {
  const prev = currentEvent;
  currentEvent = evt;
  try {
    const dispatch = instance && instance.exports.oak_dispatch_event;
    if (dispatch) dispatch(id);
  } finally {
    currentEvent = prev;
  }
}

// A handler spec: "<id>" or "<id>:<flags>", flags in `cdsop` order.
function parseListenerSpec(text) {
  const sep = text.indexOf(':');
  const id = idFromText(sep < 0 ? text : text.slice(0, sep));
  if (id === null) return null;
  const flags = {
    capture: false, preventDefault: false, stopPropagation: false,
    once: false, passive: false, releaseCapture: false,
  };
  const letters = sep < 0 ? '' : text.slice(sep + 1);
  for (let i = 0; i < letters.length; i++) {
    const ch = letters[i];
    if (!EVENT_FLAGS.includes(ch)) continue;
    if (ch === 'c') flags.capture = true;
    else if (ch === 'd') flags.preventDefault = true;
    else if (ch === 's') flags.stopPropagation = true;
    else if (ch === 'o') flags.once = true;
    else if (ch === 'p') flags.passive = true;
    else if (ch === 'r') flags.releaseCapture = true;
  }
  return { id, flags };
}

const decoder = new TextDecoder();
const encoder = new TextEncoder();

function doc() {
  return globalThis.document;
}

function addNode(n) {
  if (!n) return 0n;
  const known = nodeIds.get(n);
  if (known !== undefined) return BigInt(known);
  nodes.push(n);
  const id = nodes.length - 1;
  nodeIds.set(n, id);
  return BigInt(id);
}

// Drop a detached subtree's handles. Without this the id table (and the
// strong references in it) grows by one entry per created node for the
// life of the page, because patch/replace creates fresh nodes every time.
function forget(n) {
  if (!n) return;
  removeFocusTrap(n);
  const id = nodeIds.get(n);
  if (id !== undefined) {
    nodes[id] = null;
    nodeIds.delete(n);
  }
  const children = n.childNodes || [];
  for (let i = 0; i < children.length; i++) forget(children[i]);
}

// ── focus trap (`data-oak-focus-trap`) ───────────────────────────────
//
// A dialog renders the attribute; Tab/Shift+Tab cycle inside it, and the
// previously focused element gets focus back when the dialog leaves the
// tree. Escape is the app's own keydown handler, so it needs focus inside.

function focusablesIn(n) {
  if (!n || typeof n.querySelectorAll !== 'function') return [];
  try {
    return Array.from(n.querySelectorAll(FOCUSABLE));
  } catch {
    return [];
  }
}

function installFocusTrap(n) {
  if (!n || typeof n.addEventListener !== 'function' || focusTraps.has(n)) return;
  const previous = globalThis.document ? globalThis.document.activeElement : null;
  const onKey = (evt) => {
    if (!evt || evt.key !== 'Tab') return;
    const list = focusablesIn(n);
    const active = globalThis.document ? globalThis.document.activeElement : null;
    if (list.length === 0) {
      if (evt.preventDefault) evt.preventDefault();
      return;
    }
    const first = list[0];
    const last = list[list.length - 1];
    if (!n.contains || !n.contains(active)) {
      if (evt.preventDefault) evt.preventDefault();
      first.focus();
      return;
    }
    if (list.indexOf(active) < 0) {
      if (evt.preventDefault) evt.preventDefault();
      (evt.shiftKey ? last : first).focus();
      return;
    }
    if (evt.shiftKey && active === first) {
      evt.preventDefault();
      last.focus();
    } else if (!evt.shiftKey && active === last) {
      evt.preventDefault();
      first.focus();
    }
  };
  n.addEventListener('keydown', onKey, true);
  focusTraps.set(n, { onKey, previous });
}

function removeFocusTrap(n) {
  const trap = focusTraps.get(n);
  if (!trap) return;
  n.removeEventListener('keydown', trap.onKey, true);
  focusTraps.delete(n);
  const active = globalThis.document ? globalThis.document.activeElement : null;
  if (trap.previous && (!n.contains || !n.contains(active))) {
    try {
      trap.previous.focus();
    } catch {
      // the opener may itself have left the tree
    }
  }
}

function idFromText(text) {
  try {
    return BigInt(text);
  } catch {
    return null;
  }
}

// Register (or REPLACE) the listener for one event on one node from a spec
// string. A re-render that changes a handler id must not stack a second
// listener, and removing the attribute must unregister. The capture flag is
// stored because `removeEventListener` must match it.
function attrOf(n, name) {
  return n && typeof n.getAttribute === 'function' ? n.getAttribute(name) : null;
}

// Declarative outgoing effects. The view names them as attributes; the host
// performs them on the listening element while the browser is dispatching.
function applyDeclarative(n, event, evt) {
  if (!evt) return;
  const dt = evt.dataTransfer || evt.clipboardData;
  if (!dt) return;
  if (event === 'dragstart') {
    const drag = attrOf(n, 'data-oak-drag');
    if (drag !== null) {
      const sep = drag.indexOf(':');
      const mimeLen = sep < 0 ? 0 : Number(drag.slice(0, sep));
      const mime = sep < 0 ? 'text/plain' : drag.slice(sep + 1, sep + 1 + mimeLen);
      const text = sep < 0 ? drag : drag.slice(sep + 1 + mimeLen);
      dt.setData(mime, text);
    }
    const effect = attrOf(n, 'data-oak-drag-effect');
    if (effect !== null) dt.effectAllowed = effect;
  } else if (event === 'dragover') {
    const effect = attrOf(n, 'data-oak-drop-effect');
    if (effect !== null) dt.dropEffect = effect;
  } else if (event === 'copy' || event === 'cut') {
    const text = attrOf(n, 'data-oak-copy-text');
    if (text !== null) {
      dt.setData('text/plain', text);
      if (evt.preventDefault) evt.preventDefault();
    }
  }
}

function makeWrapper(n, event, id, flags) {
  return (evt) => {
    applyDeclarative(n, event, evt);
    if (flags.preventDefault && evt && evt.preventDefault) evt.preventDefault();
    if (flags.stopPropagation && evt && evt.stopPropagation) evt.stopPropagation();
    dispatchWith(evt, id);
  };
}

function removeEntry(n, event, entry) {
  if (!entry) return;
  n.removeEventListener(event, entry.wrapper, { capture: entry.flags.capture });
  if (entry.release) {
    n.removeEventListener('gotpointercapture', entry.release, { passive: true });
  }
}

// The browser implicitly captures a touch pointer to the element it went
// down on; releasing it is what lets `pointerenter` fire on neighbours
// during a drag. A mouse drag never captures, so this is a no-op there.
function makeReleaseCapture(n) {
  return (evt) => {
    if (!evt || !n.hasPointerCapture) return;
    try {
      if (n.hasPointerCapture(evt.pointerId)) n.releasePointerCapture(evt.pointerId);
    } catch {
      // the pointer may already be gone
    }
  };
}

function setListener(n, event, spec) {
  let table = listenerTables.get(n);
  if (!table) {
    table = new Map();
    listenerTables.set(n, table);
  }
  removeEntry(n, event, table.get(event));
  const parsed = spec === null ? null : parseListenerSpec(spec);
  if (parsed === null) {
    table.delete(event);
    return;
  }
  const wrapper = makeWrapper(n, event, parsed.id, parsed.flags);
  const release = parsed.flags.releaseCapture ? makeReleaseCapture(n) : null;
  n.addEventListener(event, wrapper, {
    capture: parsed.flags.capture,
    once: parsed.flags.once,
    passive: parsed.flags.passive,
  });
  if (release) n.addEventListener('gotpointercapture', release, { passive: true });
  table.set(event, { id: parsed.id, flags: parsed.flags, wrapper, release });
}

function clearListener(n, event) {
  const table = listenerTables.get(n);
  if (!table) return;
  removeEntry(n, event, table.get(event));
  table.delete(event);
}

// Window (0), document (1) and animation-frame (2) listeners. Global events
// have no element to carry declarative attributes, so only the spec flags
// apply.
function globalTarget(which) {
  if (Number(which) === 1) return globalThis.document || null;
  return globalThis.window || globalThis;
}

function setGlobalListener(target, event, spec) {
  if (Number(target) === 2) {
    const parsed = spec === null ? null : parseListenerSpec(spec);
    frameHandler = parsed ? parsed.id : null;
    return;
  }
  const t = globalTarget(target);
  if (!t || typeof t.addEventListener !== 'function') return;
  const key = `${Number(target)}:${event}`;
  const previous = globalTables.get(key);
  if (previous) {
    t.removeEventListener(event, previous.wrapper, { capture: previous.flags.capture });
  }
  const parsed = spec === null ? null : parseListenerSpec(spec);
  if (parsed === null) {
    globalTables.delete(key);
    return;
  }
  const wrapper = makeWrapper(null, event, parsed.id, parsed.flags);
  t.addEventListener(event, wrapper, {
    capture: parsed.flags.capture,
    once: parsed.flags.once,
    passive: parsed.flags.passive,
  });
  globalTables.set(key, { flags: parsed.flags, wrapper });
}

function clearGlobalListener(target, event) {
  if (Number(target) === 2) {
    frameHandler = null;
    return;
  }
  const key = `${Number(target)}:${event}`;
  const previous = globalTables.get(key);
  const t = globalTarget(target);
  if (previous && t) {
    t.removeEventListener(event, previous.wrapper, { capture: previous.flags.capture });
  }
  globalTables.delete(key);
}

function nodeById(id) {
  return nodes[Number(id)] || null;
}

const WORKER_LOAD_HINT =
  'the engine worker failed to start: worker.js or one of its imports ' +
  '(web.js, web_runtime.js, float_format.js, try_engine.wasm) did not load. ' +
  'Check the browser console and rebuild with scripts/build-try.sh.';

/// A worker failure arrives as an ErrorEvent, a plain Event (a module
/// script or one of its imports failed to load), or a thrown value.
/// `String(event)` is `[object Event]`, which tells the user nothing.
function workerErrorMessage(ev) {
  if (!ev) return WORKER_LOAD_HINT;
  if (typeof ev === 'string') return ev;
  if (typeof ev.message === 'string' && ev.message) return ev.message;
  if (ev.error && typeof ev.error.message === 'string' && ev.error.message) {
    return ev.error.message;
  }
  if (ev.filename) return `${ev.filename}:${ev.lineno || 0}`;
  return WORKER_LOAD_HINT;
}

/// Terminate the run worker (if any), clear the timeout, and record `state`.
/// Called on completion, timeout, cancel and before a new run.
function tryStopWorker(state) {
  if (workerTimer !== null) {
    clearTimeout(workerTimer);
    workerTimer = null;
  }
  if (tryWorker) {
    tryWorker.onmessage = null;
    tryWorker.onerror = null;
    tryWorker.onmessageerror = null;
    tryWorker.terminate();
    tryWorker = null;
  }
  workerState = state;
}

// A wasm32 pointer is an unsigned 32-bit offset. `Number(ptr)` is signed, so
// a heap above 2 GB produced a negative offset and an unexplained
// `RangeError` (anidoku's crash) instead of addressing the right bytes.
function u32(ptr) {
  return Number(ptr) >>> 0;
}

function str(ptr, len) {
  // Re-read the buffer on every call: memory.grow detaches the old one.
  return decoder.decode(new Uint8Array(memory.buffer, u32(ptr), Number(len)));
}

// Copy `bytes` into the caller's wasm buffer, capped at `max`; returns the
// byte count written.
function writeBytes(ptr, bytes, max) {
  const n = Math.min(bytes.length, Number(max));
  new Uint8Array(memory.buffer, u32(ptr), n).set(bytes.subarray(0, n));
  return BigInt(n);
}

// Open the `monad_keys` database and run one request through `keys`.
//
// Every keystore call funnels through here so the schema (one store, one key
// column) is written once. A rejected promise is the caller's error state;
// `onupgradeneeded` creates the store on first use.
//
// The connection is CLOSED on both the success and the failure path. A page
// that signs in once and then makes a request per API call opens one
// connection per op otherwise, and an IndexedDB connection lives until the
// page unloads: they accumulate, and an open one also blocks a future
// `onupgradeneeded`, so the store could no longer be migrated in place.
function withStore(mode, request) {
  return new Promise((resolve, reject) => {
    const factory = globalThis.indexedDB;
    if (!factory || typeof factory.open !== 'function') {
      reject(new Error('NotSupportedError'));
      return;
    }
    const open = factory.open('monad_keys', 1);
    // One settle per connection: close it, then answer, so no path can
    // resolve twice or leave the connection open.
    const settle = (fn, value) => {
      try {
        if (open.result) open.result.close();
      } catch {
        // closing an already-closed connection is not an error here
      }
      fn(value);
    };
    open.onupgradeneeded = () => {
      const db = open.result;
      if (!db.objectStoreNames.contains('keys')) db.createObjectStore('keys');
    };
    open.onerror = () => reject(open.error || new Error('IndexedDBError'));
    open.onsuccess = () => {
      let tx;
      try {
        tx = open.result.transaction('keys', mode);
      } catch (err) {
        settle(reject, err);
        return;
      }
      tx.oncomplete = () => settle(resolve, undefined);
      tx.onerror = () => settle(reject, tx.error || new Error('IndexedDBError'));
      tx.onabort = () => settle(reject, tx.error || new Error('IndexedDBAbort'));
      let req;
      try {
        req = request(tx.objectStore('keys'));
      } catch (err) {
        settle(reject, err);
        return;
      }
      if (req && mode === 'readonly') {
        req.onsuccess = () => settle(resolve, req.result);
      }
    };
  });
}

function hexBytes(bytes) {
  let out = '';
  for (let i = 0; i < bytes.length; i++) {
    out += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
  }
  return out;
}

// The request/response header blob: `"<klen>:<key><vlen>:<value>"` repeated.
// Length prefixes mean a value may contain `:` or a newline, and HTTP header
// values cannot contain NUL, so nothing is escaped.
function parseHeaderBlob(text) {
  const out = {};
  let i = 0;
  while (i < text.length) {
    const kColon = text.indexOf(':', i);
    if (kColon < 0) break;
    const klen = Number(text.slice(i, kColon));
    if (!Number.isFinite(klen) || klen < 0) break;
    const key = text.slice(kColon + 1, kColon + 1 + klen);
    const vStart = kColon + 1 + klen;
    const vColon = text.indexOf(':', vStart);
    if (vColon < 0) break;
    const vlen = Number(text.slice(vStart, vColon));
    if (!Number.isFinite(vlen) || vlen < 0) break;
    const value = text.slice(vColon + 1, vColon + 1 + vlen);
    out[key] = value;
    i = vColon + 1 + vlen;
  }
  return out;
}

function encodeHeaderBlob(pairs) {
  return pairs
    .map(([key, value]) => `${key.length}:${key}${value.length}:${value}`)
    .join('');
}

function methodName(code) {
  switch (Number(code)) {
    case 1:
      return 'POST';
    case 2:
      return 'PUT';
    case 3:
      return 'DELETE';
    case 4:
      return 'PATCH';
    default:
      return 'GET';
  }
}

function storage() {
  try {
    return globalThis.localStorage || null;
  } catch {
    return null; // a private window can throw on access
  }
}

// Start one fetch and record its status, body and response headers. The
// promise never calls back into wasm; the Monad side polls.
function beginFetch(url, method, bodyText, headers) {
  const hasBody = Number(method) !== 0;
  const body = hasBody ? bodyText : undefined;
  const init = { method: methodName(method), body };
  if (headers && Object.keys(headers).length > 0) init.headers = headers;
  const record = {
    state: 0, status: 0, bytes: new Uint8Array(0), offset: 0, headers: [],
  };
  fetches.push(record);
  const id = BigInt(fetches.length - 1);
  globalThis
    .fetch(url, init)
    .then((r) => {
      record.status = r.status;
      if (r.headers && typeof r.headers.forEach === 'function') {
        r.headers.forEach((value, key) => { record.headers.push([key, value]); });
      }
      return r.arrayBuffer();
    })
    .then((buf) => {
      record.bytes = new Uint8Array(buf);
      record.state = 1;
    })
    .catch(() => {
      record.state = 2;
      record.bytes = new Uint8Array(0);
    });
  return id;
}


// ── Sound helpers ───────────────────────────────────────────────────

// The `Wave` codes `motes/web_wasm/src/audio.mo` assigns. `Wave` is the
// Monad-side enum; this table is its only mirror, so a new waveform is one
// arm on each side (`square`/`sawtooth`/`triangle` are the Web Audio names).
const OSC_TYPES = ['sine', 'square', 'sawtooth', 'triangle'];

// A noise burst is a materialised buffer, not a stream: cap it so a stuck
// parameter cannot ask the browser for minutes of audio.
const NOISE_MAX_SECONDS = 2;

// Resolve a media-element selector against the document. Only `<audio>` and
// `<video>` answer: a selector that happens to match a `<div>` is a wrong
// name, and play/pause on it would throw.
function mediaEl(selector) {
  const d = doc();
  if (!d || typeof d.querySelector !== 'function') return null;
  let el;
  try {
    el = d.querySelector(selector);
  } catch (e) {
    return null; // an invalid selector is a miss, not a broken frame
  }
  if (!el) return null;
  const tag = (el.tagName || '').toLowerCase();
  if (tag !== 'audio' && tag !== 'video') return null;
  return el;
}

// ── WebGL helpers ────────────────────────────────────────────────────

const GL_KIND_BUFFER = 0;
const GL_KIND_TEXTURE = 1;
const GL_KIND_VERTEX_ARRAY = 2;
const GL_KIND_PROGRAM = 3;
const GL_KIND_SHADER = 4;
const GL_KIND_UNIFORM = 5;
const GL_KIND_FRAMEBUFFER = 6;

function glCtx(id) {
  return glContexts[Number(id)] || null;
}

function glObj(id) {
  const rec = glObjects[Number(id)];
  return rec ? rec.obj : null;
}

function addGlObject(ctx, kind, obj) {
  if (obj === null || obj === undefined) return 0n;
  glObjects.push({ ctx: Number(ctx), kind, obj });
  return BigInt(glObjects.length - 1);
}

// The `canvas_get_context` flag bits (`GlOptions.flags` in gl.mo).
function contextAttributes(flags) {
  const f = Number(flags);
  return {
    alpha: (f & 1) !== 0,
    antialias: (f & 2) !== 0,
    depth: (f & 4) !== 0,
    stencil: (f & 8) !== 0,
    premultipliedAlpha: (f & 16) !== 0,
    preserveDrawingBuffer: (f & 32) !== 0,
  };
}

function createVertexArray(c) {
  if (c.version === 2) return c.gl.createVertexArray();
  return c.vao ? c.vao.createVertexArrayOES() : null;
}

// WebGL1's `WEBGL_depth_texture`, probed on first use so contexts that
// never ask keep their call stream.
function hasDepthTexture(c) {
  if (c.version === 2) return true;
  if (c.depthTex === undefined) c.depthTex = c.gl.getExtension('WEBGL_depth_texture');
  return c.depthTex !== null;
}

function bindVertexArray(c, obj) {
  if (c.version === 2) c.gl.bindVertexArray(obj);
  else if (c.vao) c.vao.bindVertexArrayOES(obj);
}

function deleteGlObject(c, kind, obj) {
  const gl = c.gl;
  switch (kind) {
    case GL_KIND_BUFFER: gl.deleteBuffer(obj); break;
    case GL_KIND_TEXTURE: gl.deleteTexture(obj); break;
    case GL_KIND_VERTEX_ARRAY:
      if (c.version === 2) gl.deleteVertexArray(obj);
      else if (c.vao) c.vao.deleteVertexArrayOES(obj);
      break;
    case GL_KIND_PROGRAM: gl.deleteProgram(obj); break;
    case GL_KIND_SHADER: gl.deleteShader(obj); break;
    case GL_KIND_FRAMEBUFFER: gl.deleteFramebuffer(obj); break;
    default: break;
  }
}

// A typed view of a `Buf` payload (`MONAD_ELEM_*` kinds the uploads take).
function elemView(kind, ptr, count) {
  const n = Number(count);
  switch (Number(kind)) {
    case 2: return new Float32Array(memory.buffer, u32(ptr), n);
    case 3: return new Uint32Array(memory.buffer, u32(ptr), n);
    case 4: return new Uint8Array(memory.buffer, u32(ptr), n);
    default: return null;
  }
}

export const host = {
  set_root(selector) {
    rootSelector = selector || 'body';
  },

  bind(inst) {
    instance = inst;
    memory = inst.exports.memory;
  },

  start_ticks(inst) {
    if (!inst.exports.oak_tick) return;
    const raf = globalThis.requestAnimationFrame;
    if (!raf) return; // no frame loop outside a browser; the caller drives ticks
    const loop = (ts) => {
      if (instance !== inst) return;
      if (frameHandler !== null) {
        // Dispatch through the slot with a synthetic event so a frame
        // handler's `Event` is valid and carries the rAF timestamp.
        const timeStamp = typeof ts === 'number'
          ? ts
          : (globalThis.performance && globalThis.performance.now
            ? globalThis.performance.now()
            : Date.now());
        dispatchWith({ type: 'frame', timeStamp, target: null }, frameHandler);
      }
      inst.exports.oak_tick();
      raf(loop);
    };
    raf(loop);
  },

  // ── DOM ────────────────────────────────────────────────────────────
  dom_create(ptr, len) {
    return addNode(doc().createElement(str(ptr, len)));
  },

  dom_create_svg(ptr, len) {
    return addNode(doc().createElementNS('http://www.w3.org/2000/svg', str(ptr, len)));
  },

  dom_create_text(ptr, len) {
    return addNode(doc().createTextNode(str(ptr, len)));
  },

  dom_create_comment(ptr, len) {
    return addNode(doc().createComment(str(ptr, len)));
  },

  dom_root() {
    const d = doc();
    // An explicit selector that matches nothing is an error, never a silent
    // fall back to <body>: mount CLEARS its container, so falling back would
    // erase the page.
    if (rootSelector === 'body') return addNode(d.body);
    const el = d.querySelector(rootSelector);
    if (!el) throw new Error(`oak: mount selector not found: ${rootSelector}`);
    return addNode(el);
  },

  dom_append(parent, child) {
    const p = nodeById(parent);
    const c = nodeById(child);
    if (p && c) p.appendChild(c);
    return 0n;
  },

  dom_insert_before(parent, child, before) {
    const p = nodeById(parent);
    const c = nodeById(child);
    if (p && c) p.insertBefore(c, nodeById(before));
    return 0n;
  },

  dom_remove(node) {
    const n = nodeById(node);
    if (n && n.parentNode) {
      n.parentNode.removeChild(n);
      forget(n);
    }
    return 0n;
  },

  dom_replace(oldNode, newNode) {
    const o = nodeById(oldNode);
    const n = nodeById(newNode);
    if (o && o.parentNode && n) {
      o.parentNode.replaceChild(n, o);
      forget(o);
    }
    return 0n;
  },

  dom_set_attr(node, kptr, klen, vptr, vlen) {
    const n = nodeById(node);
    if (!n) return 0n;
    const name = str(kptr, klen);
    const value = str(vptr, vlen);
    if (name.startsWith(EVENT_PREFIX)) {
      setListener(n, name.slice(EVENT_PREFIX.length), value);
    }
    n.setAttribute(name, value);
    if (name === FOCUS_TRAP_ATTR) installFocusTrap(n);
    return 0n;
  },

  dom_remove_attr(node, kptr, klen) {
    const n = nodeById(node);
    if (!n) return 0n;
    const name = str(kptr, klen);
    if (name.startsWith(EVENT_PREFIX)) clearListener(n, name.slice(EVENT_PREFIX.length));
    n.removeAttribute(name);
    if (name === FOCUS_TRAP_ATTR) removeFocusTrap(n);
    return 0n;
  },

  dom_set_text(node, ptr, len) {
    const n = nodeById(node);
    const text = str(ptr, len);
    if (!n) return 0n;
    if (n.nodeType === 3) n.nodeValue = text;
    else n.textContent = text;
    return 0n;
  },

  dom_add_listener(node, eptr, elen, sptr, slen) {
    const n = nodeById(node);
    if (!n) return 0n;
    setListener(n, str(eptr, elen), str(sptr, slen));
    return 0n;
  },

  dom_add_listener_global(target, eptr, elen, sptr, slen) {
    setGlobalListener(target, str(eptr, elen), str(sptr, slen));
    return 0n;
  },

  dom_remove_listener_global(target, eptr, elen) {
    clearGlobalListener(target, str(eptr, elen));
    return 0n;
  },

  dom_child(node, index) {
    const n = nodeById(node);
    const child = n ? n.childNodes[Number(index)] : null;
    return addNode(child);
  },

  dom_child_count(node) {
    const n = nodeById(node);
    return BigInt(n ? n.childNodes.length : 0);
  },

  // ── read-only introspection (hydration, form reads) ──────────────────
  // `Node` is opaque in Monad, so these reads are the only way to ask what
  // a handle points at. A null handle reads nodeType 0 / an empty string.
  dom_in_svg(node) {
    const n = nodeById(node);
    const inside = n && n.namespaceURI === 'http://www.w3.org/2000/svg'
      && n.localName !== 'foreignObject';
    return BigInt(inside ? 1 : 0);
  },

  dom_node_type(node) {
    const n = nodeById(node);
    return BigInt(n ? n.nodeType : 0);
  },

  // Lowercase here: the Monad side never pays for a per-node case fold, and
  // the view's tag names are lowercase.
  dom_tag_name(node, ptr, max) {
    const n = nodeById(node);
    const tag = n && n.nodeType === 1 && n.tagName ? n.tagName.toLowerCase() : '';
    return writeBytes(ptr, encoder.encode(tag), max);
  },

  dom_value(node, ptr, max) {
    const n = nodeById(node);
    const value = n && typeof n.value === 'string' ? n.value : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  // A handler only carries a message id, so this is how it addresses a node
  // it wants to read. No match is the null handle (0), like dom_child.
  dom_query(ptr, len) {
    return addNode(doc().querySelector(str(ptr, len)));
  },

  // ── current event (see motes/web_wasm/src/event.mo) ─────────────────
  event_i64(which) {
    const e = currentEvent;
    if (!e) return 0n;
    switch (Number(which)) {
      case 1: return BigInt(e.button || 0);
      case 2: return BigInt(e.buttons || 0);
      case 3: return BigInt(e.detail || 0);
      case 4: return BigInt(e.pointerId || 0);
      case 5: return BigInt(e.location || 0);
      case 6: return BigInt(e.deltaMode || 0);
      case 7: return e.repeat ? 1n : 0n;
      case 8: return e.isPrimary ? 1n : 0n;
      case 9: return e.target && e.target.checked ? 1n : 0n;
      case 10: return e.dataTransfer || e.clipboardData ? 1n : 0n;
      case 11:
        return BigInt((e.shiftKey ? 1 : 0) | (e.ctrlKey ? 2 : 0)
          | (e.altKey ? 4 : 0) | (e.metaKey ? 8 : 0));
      case 12: return 1n;
      case 13: return e.defaultPrevented ? 1n : 0n;
      case 14: return BigInt(e.which || 0);
      default: return 0n;
    }
  },

  event_f64(which) {
    const e = currentEvent;
    if (!e) return 0;
    switch (Number(which)) {
      case 1: return Number(e.clientX) || 0;
      case 2: return Number(e.clientY) || 0;
      case 3: return Number(e.pageX) || 0;
      case 4: return Number(e.pageY) || 0;
      case 5: return Number(e.screenX) || 0;
      case 6: return Number(e.screenY) || 0;
      case 7: return Number(e.offsetX) || 0;
      case 8: return Number(e.offsetY) || 0;
      case 9: return Number(e.deltaX) || 0;
      case 10: return Number(e.deltaY) || 0;
      case 11: return Number(e.deltaZ) || 0;
      case 12: return Number(e.pressure) || 0;
      case 13: return Number(e.width) || 0;
      case 14: return Number(e.height) || 0;
      case 15: return Number(e.timeStamp) || 0;
      default: return 0;
    }
  },

  event_str(which, ptr, max) {
    const e = currentEvent;
    let text = '';
    switch (Number(which)) {
      case 1: text = e ? String(e.type || '') : ''; break;
      case 2: text = e ? String(e.pointerType || '') : ''; break;
      case 3: text = e ? String(e.key || '') : ''; break;
      case 4: text = e ? String(e.code || '') : ''; break;
      case 5:
        text = e && e.target && typeof e.target.value === 'string'
          ? e.target.value : '';
        break;
      case 6:
        text = e && e.dataTransfer
          ? String(e.dataTransfer.effectAllowed || '') : '';
        break;
      case 7:
        text = e && e.dataTransfer ? String(e.dataTransfer.dropEffect || '') : '';
        break;
    }
    return writeBytes(ptr, encoder.encode(text), max);
  },

  event_data(mptr, mlen, ptr, max) {
    const e = currentEvent;
    const dt = e && (e.clipboardData || e.dataTransfer);
    const text = dt && typeof dt.getData === 'function'
      ? String(dt.getData(str(mptr, mlen)) || '') : '';
    return writeBytes(ptr, encoder.encode(text), max);
  },

  event_types(ptr, max) {
    const e = currentEvent;
    const dt = e && (e.dataTransfer || e.clipboardData);
    const text = dt && dt.types ? Array.from(dt.types).join('\n') : '';
    return writeBytes(ptr, encoder.encode(text), max);
  },

  event_files_count() {
    const e = currentEvent;
    const dt = e && (e.dataTransfer || e.clipboardData);
    return BigInt(dt && dt.files ? dt.files.length : 0);
  },

  event_file_i64(index, which) {
    const e = currentEvent;
    const dt = e && (e.dataTransfer || e.clipboardData);
    const f = dt && dt.files ? dt.files[Number(index)] : null;
    if (!f) return 0n;
    return BigInt(Number(which) === 2 ? (f.lastModified || 0) : (f.size || 0));
  },

  event_file_str(index, which, ptr, max) {
    const e = currentEvent;
    const dt = e && (e.dataTransfer || e.clipboardData);
    const f = dt && dt.files ? dt.files[Number(index)] : null;
    const text = !f ? '' : (Number(which) === 2
      ? String(f.type || '') : String(f.name || ''));
    return writeBytes(ptr, encoder.encode(text), max);
  },

  event_prevent_default() {
    if (currentEvent && currentEvent.preventDefault) currentEvent.preventDefault();
    return 0n;
  },

  event_stop_propagation() {
    if (currentEvent && currentEvent.stopPropagation) currentEvent.stopPropagation();
    return 0n;
  },

  // ── fetch (two-phase: a promise must not re-enter wasm) ─────────────
  fetch_begin(uptr, ulen, method, bptr, blen) {
    return beginFetch(str(uptr, ulen), method, str(bptr, blen), null);
  },

  fetch_begin_headers(uptr, ulen, method, bptr, blen, hptr, hlen) {
    const headers = parseHeaderBlob(str(hptr, hlen));
    return beginFetch(str(uptr, ulen), method, str(bptr, blen), headers);
  },

  fetch_poll(id) {
    const r = fetches[Number(id)];
    return BigInt(r ? r.state : 2);
  },

  fetch_status(id) {
    const r = fetches[Number(id)];
    return BigInt(r ? r.status : 0);
  },

  fetch_headers(id, ptr, max) {
    const r = fetches[Number(id)];
    return writeBytes(ptr, encoder.encode(encodeHeaderBlob(r ? r.headers : [])), max);
  },

  fetch_read(id, ptr, max) {
    const r = fetches[Number(id)];
    if (!r) return 0n;
    const rest = r.bytes.subarray(r.offset);
    const n = writeBytes(ptr, rest, max);
    r.offset += Number(n);
    // The body is fully consumed: release it rather than retaining every
    // response for the life of the page (status stays readable).
    if (r.offset >= r.bytes.length) {
      r.bytes = new Uint8Array(0);
      r.offset = 0;
    }
    return n;
  },

  // ── async clipboard (two-phase: a promise must not re-enter wasm) ──
  clipboard_available() {
    const cb = globalThis.navigator && globalThis.navigator.clipboard;
    return cb && typeof cb.readText === 'function' ? 1n : 0n;
  },

  clipboard_read_begin() {
    const rec = { state: 0, text: '', error: '' };
    clips.push(rec);
    const id = BigInt(clips.length - 1);
    const cb = globalThis.navigator && globalThis.navigator.clipboard;
    if (!cb || typeof cb.readText !== 'function') {
      rec.state = 2;
      rec.error = 'NotSupportedError';
      return id;
    }
    cb.readText()
      .then((text) => { rec.text = String(text || ''); rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  clipboard_write_begin(ptr, len) {
    const rec = { state: 0, text: '', error: '' };
    clips.push(rec);
    const id = BigInt(clips.length - 1);
    const cb = globalThis.navigator && globalThis.navigator.clipboard;
    if (!cb || typeof cb.writeText !== 'function') {
      rec.state = 2;
      rec.error = 'NotSupportedError';
      return id;
    }
    cb.writeText(str(ptr, len))
      .then(() => { rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  clipboard_poll(id) {
    const rec = clips[Number(id)];
    return BigInt(rec ? rec.state : 2);
  },

  clipboard_read(id, ptr, max) {
    const rec = clips[Number(id)];
    return writeBytes(ptr, encoder.encode(rec ? rec.text : ''), max);
  },

  clipboard_error(id, ptr, max) {
    const rec = clips[Number(id)];
    return writeBytes(ptr, encoder.encode(rec ? rec.error : ''), max);
  },

  // ── clock, storage, console, stdio ──────────────────────────────────
  now_ms() {
    return BigInt(Date.now());
  },

  storage_get_raw(kptr, klen, ptr, max) {
    const store = storage();
    const value = store ? store.getItem(str(kptr, klen)) : null;
    return writeBytes(ptr, encoder.encode(value || ''), max);
  },

  storage_set(kptr, klen, vptr, vlen) {
    const store = storage();
    if (store) store.setItem(str(kptr, klen), str(vptr, vlen));
    return 0n;
  },

  storage_has(kptr, klen) {
    const store = storage();
    return store && store.getItem(str(kptr, klen)) !== null ? 1n : 0n;
  },

  storage_remove(kptr, klen) {
    const store = storage();
    if (store) store.removeItem(str(kptr, klen));
    return 0n;
  },

  storage_clear() {
    const store = storage();
    if (store) store.clear();
    return 0n;
  },

  monotonic_ms() {
    const perf = globalThis.performance;
    const ms = perf && typeof perf.now === 'function' ? perf.now() : Date.now();
    return BigInt(Math.floor(ms));
  },

  // ── media queries ──────────────────────────────────────────────────
  media_matches(qptr, qlen) {
    const mm = globalThis.matchMedia;
    if (typeof mm !== 'function') return 0n;
    try {
      return mm.call(globalThis, str(qptr, qlen)).matches ? 1n : 0n;
    } catch {
      return 0n;
    }
  },

  // A `change` listener per query; the spec carries the handler id, and the
  // live event is a MediaQueryListEvent snapshot.
  media_watch(qptr, qlen, sptr, slen) {
    const mm = globalThis.matchMedia;
    const query = str(qptr, qlen);
    const previous = mediaTables.get(query);
    if (previous) {
      previous.mql.removeEventListener('change', previous.wrapper);
      mediaTables.delete(query);
    }
    if (typeof mm !== 'function') return 0n;
    const parsed = parseListenerSpec(str(sptr, slen));
    if (parsed === null) return 0n;
    let mql;
    try {
      mql = mm.call(globalThis, query);
    } catch {
      return 0n;
    }
    const wrapper = (evt) => dispatchWith(
      { type: 'change', matches: !!(evt && evt.matches), media: query, timeStamp: Date.now() },
      parsed.id,
    );
    mql.addEventListener('change', wrapper);
    mediaTables.set(query, { mql, wrapper });
    return 0n;
  },

  media_unwatch(qptr, qlen) {
    const query = str(qptr, qlen);
    const previous = mediaTables.get(query);
    if (previous) {
      previous.mql.removeEventListener('change', previous.wrapper);
      mediaTables.delete(query);
    }
    return 0n;
  },

  // ── hit testing, attribute reads, focus ────────────────────────────
  dom_element_at(x, y) {
    const d = doc();
    if (!d || typeof d.elementFromPoint !== 'function') return 0n;
    return addNode(d.elementFromPoint(Number(x), Number(y)));
  },

  dom_attr(node, kptr, klen, ptr, max) {
    const n = nodeById(node);
    const name = str(kptr, klen);
    const value = n && typeof n.getAttribute === 'function'
      ? (n.getAttribute(name) || '')
      : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  dom_focus(ptr, len) {
    const d = doc();
    if (!d || typeof d.querySelector !== 'function') return 0n;
    const el = d.querySelector(str(ptr, len));
    if (el && typeof el.focus === 'function') {
      try {
        el.focus();
      } catch {
        // a detached or inert element cannot take focus; nothing to do
      }
    }
    return 0n;
  },

  // ── WebSocket ───────────────────────────────────────────────────────
  ws_open(uptr, ulen, pptr, plen) {
    const url = str(uptr, ulen);
    const protocols = str(pptr, plen)
      .split(',')
      .map((p) => p.trim())
      .filter((p) => p.length > 0);
    const rec = { ws: null, queue: [], handler: 0n, state: 0, code: 1006, reason: '', clean: false, scheduled: false };
    sockets.push(rec);
    const id = BigInt(sockets.length - 1);
    if (typeof globalThis.WebSocket !== 'function') {
      rec.queue.push({ kind: 5, bytes: null });
      return id;
    }
    let ws;
    try {
      ws = protocols.length > 0 ? new WebSocket(url, protocols) : new WebSocket(url);
    } catch (e) {
      rec.queue.push({ kind: 5, bytes: null });
      return id;
    }
    rec.ws = ws;
    ws.binaryType = 'arraybuffer';
    const push = (kind, bytes) => {
      if (rec.freed) return;
      rec.queue.push({ kind, bytes });
      rec.scheduled = false;
      if (rec.handler !== 0n) socket_wake(rec);
    };
    ws.onopen = () => {
      rec.state = 1;
      push(1, null);
    };
    ws.onmessage = (ev) => {
      if (typeof ev.data === 'string') push(2, encoder.encode(ev.data));
      else push(3, new Uint8Array(ev.data));
    };
    ws.onerror = () => {
      push(5, null);
    };
    ws.onclose = (ev) => {
      rec.state = 3;
      rec.code = Number(ev.code || 1006);
      rec.reason = ev.reason || '';
      rec.clean = Boolean(ev.wasClean);
      push(4, null);
    };
    return id;
  },

  ws_state(id) {
    const rec = sockets[Number(id)];
    return BigInt(rec ? rec.state : -1);
  },

  // which 0 -> queued entries, 1 -> head kind, 2 -> head payload length in
  // bytes, 3 -> head is a close (0/1)
  ws_peek(id, which) {
    const rec = sockets[Number(id)];
    if (!rec) return -1n;
    if (which === 0n) return BigInt(rec.queue.length);
    const head = rec.queue[0];
    if (!head) return 0n;
    if (which === 1n) return BigInt(head.kind);
    if (which === 2n) return BigInt(head.bytes ? head.bytes.length : 0);
    return 0n;
  },

  // Copies the head payload out and pops the entry; returns its kind (0
  // when the queue is empty).
  ws_read(id, ptr, max) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    const head = rec.queue.shift();
    if (!head) return 0n;
    if (head.bytes) writeBytes(ptr, head.bytes, max);
    return BigInt(head.kind);
  },

  // which 0 -> close code, 1 -> wasClean (0/1), 2 -> queued bytes
  ws_info(id, which) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    if (which === 0n) return BigInt(rec.code);
    if (which === 1n) return rec.clean ? 1n : 0n;
    let n = 0;
    for (const e of rec.queue) n += e.bytes ? e.bytes.length : 0;
    return BigInt(n);
  },

  // which 0 -> negotiated protocol, 1 -> close reason
  ws_text(id, which, ptr, max) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    const text = which === 0n ? (rec.ws ? rec.ws.protocol || '' : '') : rec.reason || '';
    return writeBytes(ptr, encoder.encode(text), max);
  },

  ws_send(id, ptr, len, is_binary) {
    const rec = sockets[Number(id)];
    if (!rec || !rec.ws || rec.ws.readyState !== 1) return 0n;
    const bytes = new Uint8Array(memory.buffer, u32(ptr), Number(len)).slice();
    try {
      if (is_binary !== 0n) rec.ws.send(bytes.buffer);
      else rec.ws.send(decoder.decode(bytes));
    } catch (e) {
      return 0n;
    }
    return 1n;
  },

  ws_close(id, code, ptr, len) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    if (rec.ws && (rec.ws.readyState === 0 || rec.ws.readyState === 1)) {
      const reason = str(ptr, len);
      try {
        rec.ws.close(Number(code), reason);
      } catch (e) {
        rec.ws.close();
      }
    }
    return 1n;
  },

  ws_watch(id, handler) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    rec.handler = handler;
    if (rec.queue.length > 0) socket_wake(rec);
    return 1n;
  },

  ws_unwatch(id) {
    const rec = sockets[Number(id)];
    if (rec) rec.handler = 0n;
    return 1n;
  },

  ws_buffered(id) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    return BigInt(rec.queue.length);
  },

  // Detach the handlers FIRST: closing fires `onclose`, and any in-flight
  // frame would otherwise push into the queue just cleared (and keep the
  // record alive for a socket nobody reads).
  ws_free(id) {
    const rec = sockets[Number(id)];
    if (!rec) return 0n;
    rec.freed = true;
    rec.handler = 0n;
    const ws = rec.ws;
    rec.ws = null;
    rec.queue = [];
    if (ws) {
      ws.onopen = null;
      ws.onmessage = null;
      ws.onerror = null;
      ws.onclose = null;
      if (ws.readyState === 0 || ws.readyState === 1) {
        try {
          ws.close(1000, '');
        } catch (e) {
          /* already gone */
        }
      }
    }
    return 1n;
  },

  // One-shot delayed message. The id is reserved in the top bit, which
  // `Handler.id` never uses; wasm keeps the Msg and resolves the id in
  // `Runtime.dispatch`. `setTimeout` runs after the current export returns,
  // so re-entering wasm through `oak_dispatch_event` is safe.
  timer_after(ms) {
    timerSeq += 1n;
    const id = TIMER_BASE | timerSeq;
    const delay = Math.max(0, Number(ms));
    setTimeout(() => {
      dispatchWith({ type: 'timer', timeStamp: Date.now() }, id);
    }, delay);
    return id;
  },

  // ── WebCrypto (random is synchronous; digest is two-phase) ──────────
  crypto_random_fill(ptr, len) {
    const c = globalThis.crypto;
    if (!c || typeof c.getRandomValues !== 'function') return 0n;
    const n = Math.max(0, Number(len));
    if (n === 0) return 1n;
    try {
      c.getRandomValues(new Uint8Array(memory.buffer, u32(ptr), n));
      return 1n;
    } catch {
      return 0n;
    }
  },

  crypto_sha256_begin(ptr, len) {
    const rec = { state: 0, hex: '', error: '' };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const subtle = globalThis.crypto && globalThis.crypto.subtle;
    if (!subtle || typeof subtle.digest !== 'function') {
      rec.state = 2;
      rec.error = 'NotSupportedError';
      return id;
    }
    // Copy before the promise: memory.grow detaches the old buffer.
    const data = new Uint8Array(memory.buffer, u32(ptr), Number(len)).slice();
    subtle.digest('SHA-256', data)
      .then((buf) => { rec.hex = hexBytes(new Uint8Array(buf)); rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  crypto_poll(op) {
    const rec = cryptos[Number(op)];
    return BigInt(rec ? rec.state : 2);
  },

  crypto_result_hex(op, ptr, max) {
    const rec = cryptos[Number(op)];
    return writeBytes(ptr, encoder.encode(rec ? rec.hex : ''), max);
  },

  crypto_error(op, ptr, max) {
    const rec = cryptos[Number(op)];
    return writeBytes(ptr, encoder.encode(rec ? rec.error : ''), max);
  },

  // The keypair a generate/get produced. `0` (the null handle) when there is
  // none, which is what an empty keystore slot answers.
  crypto_op_key(op) {
    const rec = cryptos[Number(op)];
    return rec && rec.key !== undefined ? rec.key : 0n;
  },

  // ── ECDSA P-256 (two-phase; the private key never leaves the host) ──
  //
  // generateKey is NON-EXTRACTABLE and sign-only: `subtle.exportKey` on the
  // private half would reject, so a page bug cannot exfiltrate it. Only the
  // PUBLIC half is ever exported (as a JWK, and as the raw SEC1 point).
  ecdsa_generate_begin() {
    const rec = { state: 0, hex: '', error: '', key: 0n };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const subtle = globalThis.crypto && globalThis.crypto.subtle;
    if (!subtle || typeof subtle.generateKey !== 'function') {
      rec.state = 2;
      rec.error = 'NotSupportedError';
      return id;
    }
    subtle
      .generateKey({ name: 'ECDSA', namedCurve: 'P-256' }, false, ['sign', 'verify'])
      .then((pair) => {
        webKeys.push(pair);
        rec.key = BigInt(webKeys.length - 1);
        rec.state = 1;
      })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  // The public half as a JWK, JSON-encoded into `hex`. The field is named
  // `hex` because that is the one string channel every op result uses; a JWK
  // is JSON text, not hex bytes.
  ecdsa_export_jwk_begin(key) {
    const rec = { state: 0, hex: '', error: '', key: 0n };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const pair = webKeys[Number(key)];
    const subtle = globalThis.crypto && globalThis.crypto.subtle;
    if (!pair || !subtle || typeof subtle.exportKey !== 'function') {
      rec.state = 2;
      rec.error = 'InvalidAccessError';
      return id;
    }
    subtle
      .exportKey('jwk', pair.publicKey)
      .then((jwk) => { rec.hex = JSON.stringify(jwk); rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  // The public half as the raw 65-byte SEC1 point (0x04 || X || Y), hex.
  // This is the encoding a did:key / multikey uses.
  ecdsa_export_raw_begin(key) {
    const rec = { state: 0, hex: '', error: '', key: 0n };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const pair = webKeys[Number(key)];
    const subtle = globalThis.crypto && globalThis.crypto.subtle;
    if (!pair || !subtle || typeof subtle.exportKey !== 'function') {
      rec.state = 2;
      rec.error = 'InvalidAccessError';
      return id;
    }
    subtle
      .exportKey('raw', pair.publicKey)
      .then((buf) => { rec.hex = hexBytes(new Uint8Array(buf)); rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  // ES256: ECDSA over SHA-256. WebCrypto's output is already IEEE P1363
  // r||s, which IS the JWS form, so no DER conversion happens here. It does
  // not guarantee low-S; JWS ES256 does not require it and DPoP servers
  // accept either form.
  ecdsa_sign_begin(key, ptr, len) {
    const rec = { state: 0, hex: '', error: '', key: 0n };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const pair = webKeys[Number(key)];
    const subtle = globalThis.crypto && globalThis.crypto.subtle;
    if (!pair || !subtle || typeof subtle.sign !== 'function') {
      rec.state = 2;
      rec.error = 'InvalidAccessError';
      return id;
    }
    // Copy before the promise: memory.grow detaches the old buffer.
    const data = new Uint8Array(memory.buffer, u32(ptr), Number(len)).slice();
    subtle
      .sign({ name: 'ECDSA', hash: 'SHA-256' }, pair.privateKey, data)
      .then((buf) => { rec.hex = hexBytes(new Uint8Array(buf)); rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  // ── IndexedDB over a non-extractable CryptoKey ─────────────────────
  //
  // The page UNLOADS between PAR and the callback, so the DPoP key has to
  // survive. A CryptoKey is not serialisable by wasm, but IndexedDB stores it
  // by structured clone: the browser keeps the material opaque and hands back
  // a live handle next page. `get` answers state 3 when the slot is EMPTY,
  // which is a miss rather than an error.
  keystore_put_begin(sptr, slen, key) {
    const rec = { state: 0, key: 0n, error: '' };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const slot = str(sptr, slen);
    const pair = webKeys[Number(key)];
    if (!pair) {
      rec.state = 2;
      rec.error = 'InvalidAccessError';
      return id;
    }
    withStore('readwrite', (store) => store.put(pair, slot))
      .then(() => { rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  keystore_get_begin(sptr, slen) {
    const rec = { state: 0, key: 0n, error: '' };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const slot = str(sptr, slen);
    withStore('readonly', (store) => store.get(slot))
      .then((found) => {
        if (found === undefined || found === null) {
          rec.state = 3; // done, and the slot holds nothing
          return;
        }
        webKeys.push(found);
        rec.key = BigInt(webKeys.length - 1);
        rec.state = 1;
      })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  keystore_delete_begin(sptr, slen) {
    const rec = { state: 0, key: 0n, error: '' };
    cryptos.push(rec);
    const id = BigInt(cryptos.length - 1);
    const slot = str(sptr, slen);
    // Succeeds when the slot was already empty, so a logout need not check.
    withStore('readwrite', (store) => store.delete(slot))
      .then(() => { rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  window_replace(ptr, len) {
    const loc = globalThis.location;
    if (loc && typeof loc.replace === 'function') {
      try {
        loc.replace(str(ptr, len));
      } catch {
        // see window_reload
      }
    }
    return 0n;
  },

  // ── location reads ─────────────────────────────────────────────────
  //
  // An OAuth redirect delivers its result in the URL: atproto returns
  // code/state/iss (and on failure error/error_description) as query
  // parameters of the page the provider sends the user back to.
  location_origin(ptr, max) {
    const loc = globalThis.location;
    const value = loc && loc.origin ? String(loc.origin) : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  location_href(ptr, max) {
    const loc = globalThis.location;
    const value = loc && loc.href ? String(loc.href) : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  location_pathname(ptr, max) {
    const loc = globalThis.location;
    const value = loc && loc.pathname ? String(loc.pathname) : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  location_search(ptr, max) {
    const loc = globalThis.location;
    const value = loc && loc.search ? String(loc.search) : '';
    return writeBytes(ptr, encoder.encode(value), max);
  },

  // URLSearchParams does the percent-decoding (and turns `+` into a space),
  // which is what keeps a base64url `code` or a `state` carrying `=`
  // intact. An absent parameter answers a zero-length string, which the Monad
  // side reads as `none`.
  location_search_param(nptr, nlen, ptr, max) {
    const loc = globalThis.location;
    const raw = loc && loc.search ? String(loc.search) : '';
    let value = '';
    if (raw) {
      try {
        const params = new URLSearchParams(raw);
        const found = params.get(str(nptr, nlen));
        value = found === null ? '' : String(found);
      } catch {
        value = '';
      }
    }
    return writeBytes(ptr, encoder.encode(value), max);
  },

  // ── window / navigation ────────────────────────────────────────────
  window_reload() {
    const loc = globalThis.location;
    if (loc && typeof loc.reload === 'function') {
      try {
        loc.reload();
      } catch {
        // a sandboxed frame may refuse; nothing to do
      }
    }
    return 0n;
  },

  window_navigate(ptr, len) {
    const loc = globalThis.location;
    if (loc && typeof loc.assign === 'function') {
      try {
        loc.assign(str(ptr, len));
      } catch {
        // see window_reload
      }
    }
    return 0n;
  },

  // The allocator traps after this; the message is the user-visible half.
  oom(want, have) {
    console.error(
      `monad: wasm heap exhausted (want ${Number(want)} bytes, have ${Number(have)})`,
    );
    return 0n;
  },

  console_log(ptr, len) {
    console.log(str(ptr, len));
    return 0n;
  },

  // ── /try engine result (pushed from try_engine.wasm in the worker) ──
  // The engine's `try_run` ends by calling this with its status and four
  // rendered strings; the worker reads them with `takeTryResult` after the
  // export returns and posts them to the UI.
  try_result(status, vp, vl, tp, tl, ep, el, np, nl) {
    tryResult = {
      status: Number(status),
      value: str(vp, vl),
      type: str(tp, tl),
      error: str(ep, el),
      notes: str(np, nl),
    };
    return 0n;
  },

  takeTryResult() {
    const r = tryResult;
    tryResult = null;
    return r;
  },

  // ── /try worker channel (UI side) ──
  worker_run(ptr, len) {
    tryStopWorker(0);
    const source = str(ptr, len);
    workerSeq += 1;
    workerState = 1;
    workerResult = null;
    const WorkerCtor = globalThis.Worker;
    if (!WorkerCtor) {
      workerState = 4;
      workerResult = { status: 'internal', value: '', type: '',
                       error: 'Web Workers are not available in this browser', notes: '' };
      return BigInt(workerSeq);
    }
    const workerUrl = new URL('./worker.js', import.meta.url);
    try {
      tryWorker = new WorkerCtor(workerUrl, { type: 'module' });
    } catch (err) {
      const message = workerErrorMessage(err);
      console.error('oak: could not start the /try worker', workerUrl.href, err);
      workerState = 4;
      workerResult = { status: 'internal', value: '', type: '', error: message, notes: '' };
      return BigInt(workerSeq);
    }
    const seq = workerSeq;
    tryWorker.onmessage = (ev) => {
      const d = ev.data || {};
      if (d.seq !== seq) return;
      if (d.type === 'started') {
        if (workerTimer !== null) clearTimeout(workerTimer);
        workerTimer = setTimeout(() => {
          workerResult = { status: 'timeout', value: '', type: '',
                           error: 'the evaluation did not finish within 30 seconds', notes: '' };
          tryStopWorker(3);
        }, WORKER_EVAL_TIMEOUT_MS);
        return;
      }
      workerResult = {
        status: d.status || 'internal',
        value: d.value || '',
        type: d.typeText || '',
        error: d.error || '',
        notes: d.notes || '',
      };
      workerState = d.type === 'result' ? 2 : 4;
      tryStopWorker(workerState);
    };
    tryWorker.onerror = (ev) => {
      console.error('oak: /try worker failed', workerUrl.href, ev);
      workerResult = { status: 'internal', value: '', type: '',
                       error: workerErrorMessage(ev), notes: '' };
      tryStopWorker(4);
    };
    tryWorker.onmessageerror = (ev) => {
      console.error('oak: /try worker message could not be deserialized', workerUrl.href, ev);
      workerResult = { status: 'internal', value: '', type: '',
                       error: 'the engine worker sent a message this page could not read', notes: '' };
      tryStopWorker(4);
    };
    tryWorker.postMessage({ type: 'run', seq, source });
    workerTimer = setTimeout(() => {
      workerResult = { status: 'timeout', value: '', type: '',
                       error: 'loading the engine did not finish within 30 seconds', notes: '' };
      tryStopWorker(3);
    }, WORKER_LOAD_TIMEOUT_MS);
    return BigInt(seq);
  },

  worker_poll() {
    return BigInt(workerState);
  },

  worker_status(ptr, max) {
    return writeBytes(ptr, encoder.encode(workerResult ? workerResult.status : ''), max);
  },

  worker_value(ptr, max) {
    return writeBytes(ptr, encoder.encode(workerResult ? workerResult.value : ''), max);
  },

  worker_type(ptr, max) {
    return writeBytes(ptr, encoder.encode(workerResult ? workerResult.type : ''), max);
  },

  worker_error(ptr, max) {
    return writeBytes(ptr, encoder.encode(workerResult ? workerResult.error : ''), max);
  },

  worker_notes(ptr, max) {
    return writeBytes(ptr, encoder.encode(workerResult ? workerResult.notes : ''), max);
  },

  worker_cancel() {
    tryStopWorker(0);
    return 0n;
  },

  // ── Canvas + WebGL ─────────────────────────────────────────────────
  //
  // `gl.mo` owns every selector and GL enum value; these only dispatch.

  canvas_get_context(node, flags) {
    const canvas = nodeById(node);
    if (!canvas || typeof canvas.getContext !== 'function') return 0n;
    const attrs = contextAttributes(flags);
    const webgl1Only = (Number(flags) & 64) !== 0;
    let gl = null;
    let version = 1;
    try {
      if (!webgl1Only) gl = canvas.getContext('webgl2', attrs);
      if (gl) version = 2;
      else gl = canvas.getContext('webgl', attrs);
    } catch {
      gl = null;
    }
    if (!gl) return 0n;
    const known = glContextIds.get(gl);
    if (known !== undefined) return BigInt(known);
    const rec = { gl, version, vao: null, uint: version === 2, canvas };
    if (version === 1) {
      rec.vao = gl.getExtension('OES_vertex_array_object');
      rec.uint = gl.getExtension('OES_element_index_uint') !== null;
    }
    // Without preventDefault a lost context is never restored.
    if (typeof canvas.addEventListener === 'function') {
      canvas.addEventListener('webglcontextlost', (ev) => ev.preventDefault());
    }
    glContexts.push(rec);
    const id = glContexts.length - 1;
    glContextIds.set(gl, id);
    return BigInt(id);
  },

  canvas_fit(node) {
    const canvas = nodeById(node);
    if (!canvas) return 0n;
    const dpr = Number(globalThis.devicePixelRatio) || 1;
    const w = Math.max(1, Math.round((Number(canvas.clientWidth) || 0) * dpr));
    const h = Math.max(1, Math.round((Number(canvas.clientHeight) || 0) * dpr));
    if (canvas.width === w && canvas.height === h) return 0n;
    canvas.width = w;
    canvas.height = h;
    return 1n;
  },

  dom_metric(node, which) {
    const w = Number(which);
    if (w === 2) return Number(globalThis.devicePixelRatio) || 1;
    const n = nodeById(node);
    if (!n) return 0;
    switch (w) {
      case 0: return Number(n.clientWidth) || 0;
      case 1: return Number(n.clientHeight) || 0;
      case 3: return Number(n.width) || 0;
      case 4: return Number(n.height) || 0;
      default: return 0;
    }
  },

  gl_info(ctx, which) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    switch (Number(which)) {
      case 0: return BigInt(c.version);
      case 1: return c.gl.isContextLost() ? 1n : 0n;
      case 2: return BigInt(c.gl.drawingBufferWidth | 0);
      case 3: return BigInt(c.gl.drawingBufferHeight | 0);
      case 4: return BigInt(c.gl.getError() | 0);
      case 5: return (c.version === 2 || c.vao) ? 1n : 0n;
      case 6: return c.uint ? 1n : 0n;
      case 7: return hasDepthTexture(c) ? 1n : 0n;
      case 8: {
        const gl = c.gl;
        return gl.checkFramebufferStatus(gl.FRAMEBUFFER) === gl.FRAMEBUFFER_COMPLETE ? 1n : 0n;
      }
      default: return 0n;
    }
  },

  gl_create(ctx, kind) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const k = Number(kind);
    switch (k) {
      case GL_KIND_BUFFER: return addGlObject(ctx, k, c.gl.createBuffer());
      case GL_KIND_TEXTURE: return addGlObject(ctx, k, c.gl.createTexture());
      case GL_KIND_VERTEX_ARRAY: return addGlObject(ctx, k, createVertexArray(c));
      case GL_KIND_PROGRAM: return addGlObject(ctx, k, c.gl.createProgram());
      case GL_KIND_FRAMEBUFFER: return addGlObject(ctx, k, c.gl.createFramebuffer());
      default: return 0n;
    }
  },

  gl_delete(ctx, kind, id) {
    const c = glCtx(ctx);
    const rec = glObjects[Number(id)];
    if (c && rec && rec.kind === Number(kind)) {
      deleteGlObject(c, rec.kind, rec.obj);
      glObjects[Number(id)] = null;
    }
    return 0n;
  },

  gl_bind(ctx, kind, target, id) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const obj = glObj(id);
    switch (Number(kind)) {
      case GL_KIND_BUFFER: c.gl.bindBuffer(Number(target), obj); break;
      case GL_KIND_TEXTURE: c.gl.bindTexture(Number(target), obj); break;
      case GL_KIND_VERTEX_ARRAY: bindVertexArray(c, obj); break;
      case GL_KIND_PROGRAM: c.gl.useProgram(obj); break;
      // id 0 is null: the canvas's own framebuffer.
      case GL_KIND_FRAMEBUFFER: c.gl.bindFramebuffer(Number(target), obj); break;
      default: break;
    }
    return 0n;
  },

  gl_shader(ctx, stage, ptr, len) {
    const c = glCtx(ctx);
    if (!c) {
      glLog = 'no WebGL context';
      return 0n;
    }
    const gl = c.gl;
    const sh = gl.createShader(Number(stage));
    if (!sh) {
      glLog = 'createShader failed';
      return 0n;
    }
    gl.shaderSource(sh, str(ptr, len));
    gl.compileShader(sh);
    if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) {
      glLog = gl.getShaderInfoLog(sh) || 'shader compile failed';
      gl.deleteShader(sh);
      return 0n;
    }
    glLog = '';
    return addGlObject(ctx, GL_KIND_SHADER, sh);
  },

  gl_link(ctx, program, vs, fs) {
    const c = glCtx(ctx);
    const p = glObj(program);
    const v = glObj(vs);
    const f = glObj(fs);
    if (!c || !p || !v || !f) {
      glLog = 'link: missing context, program or shader';
      return 0n;
    }
    const gl = c.gl;
    gl.attachShader(p, v);
    gl.attachShader(p, f);
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) {
      glLog = gl.getProgramInfoLog(p) || 'program link failed';
      // The caller gets an error, not the handle: free it here.
      gl.deleteProgram(p);
      glObjects[Number(program)] = null;
      return 0n;
    }
    glLog = '';
    return 1n;
  },

  gl_log(ptr, max) {
    return writeBytes(ptr, encoder.encode(glLog), max);
  },

  gl_location(ctx, program, kind, ptr, len) {
    const c = glCtx(ctx);
    const p = glObj(program);
    if (!c || !p) return Number(kind) === 0 ? -1n : 0n;
    const name = str(ptr, len);
    if (Number(kind) === 0) return BigInt(c.gl.getAttribLocation(p, name));
    return addGlObject(ctx, GL_KIND_UNIFORM, c.gl.getUniformLocation(p, name));
  },

  gl_vertex_attrib(ctx, index, size, type, normalized, stride, offset) {
    const c = glCtx(ctx);
    if (c) {
      c.gl.vertexAttribPointer(Number(index), Number(size), Number(type),
        Number(normalized) !== 0, Number(stride), Number(offset));
    }
    return 0n;
  },

  gl_uniform_f(ctx, loc, n, x, y, z, w) {
    const c = glCtx(ctx);
    const l = glObj(loc);
    if (!c || !l) return 0n;
    switch (Number(n)) {
      case 1: c.gl.uniform1f(l, x); break;
      case 2: c.gl.uniform2f(l, x, y); break;
      case 3: c.gl.uniform3f(l, x, y, z); break;
      case 4: c.gl.uniform4f(l, x, y, z, w); break;
      default: break;
    }
    return 0n;
  },

  gl_clear_color(ctx, r, g, b, a) {
    const c = glCtx(ctx);
    if (c) c.gl.clearColor(r, g, b, a);
    return 0n;
  },

  // The integer state selector; `GlState.code` in gl.mo is its other half.
  gl_state(ctx, which, a, b, cc, d) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const gl = c.gl;
    const A = Number(a);
    const B = Number(b);
    switch (Number(which)) {
      case 0: gl.viewport(A, B, Number(cc), Number(d)); break;
      case 1: gl.clear(A); break;
      case 2: if (B !== 0) gl.enable(A); else gl.disable(A); break;
      case 3: gl.blendFunc(A, B); break;
      case 4: gl.depthFunc(A); break;
      case 5: gl.cullFace(A); break;
      case 6: gl.frontFace(A); break;
      case 7: gl.depthMask(A !== 0); break;
      case 8: gl.activeTexture(gl.TEXTURE0 + A); break;
      case 9: gl.generateMipmap(A); break;
      case 10: gl.texParameteri(A, B, Number(cc)); break;
      case 11: gl.pixelStorei(A, B); break;
      case 12:
        if (B !== 0) gl.enableVertexAttribArray(A);
        else gl.disableVertexAttribArray(A);
        break;
      case 13: {
        const l = glObj(a);
        if (l) gl.uniform1i(l, B);
        break;
      }
      case 14: gl.colorMask(A !== 0, B !== 0, Number(cc) !== 0, Number(d) !== 0); break;
      default: break;
    }
    return 0n;
  },

  // The float state selector, numbered in gl.mo (`Gl.polygon_offset`).
  gl_state_f(ctx, which, a, b, cc, d) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    switch (Number(which)) {
      case 0: c.gl.polygonOffset(a, b); break;
      default: break;
    }
    return 0n;
  },

  // A data-less depth texture in the bound TEXTURE_2D (the C side bounded
  // the size). 0n without depth-texture support.
  gl_tex_image_depth(ctx, w, h) {
    const c = glCtx(ctx);
    if (!c || !hasDepthTexture(c)) return 0n;
    const gl = c.gl;
    if (c.version === 2) {
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT24, Number(w), Number(h), 0,
        gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, null);
    } else {
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT, Number(w), Number(h), 0,
        gl.DEPTH_COMPONENT, gl.UNSIGNED_SHORT, null);
    }
    return 1n;
  },

  gl_framebuffer_texture(ctx, attachment, tex) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const gl = c.gl;
    gl.framebufferTexture2D(gl.FRAMEBUFFER, Number(attachment), gl.TEXTURE_2D, glObj(tex), 0);
    return 0n;
  },

  gl_draw(ctx, indexed, mode, a, b) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    if (Number(indexed) !== 0) {
      c.gl.drawElements(Number(mode), Number(a), c.gl.UNSIGNED_INT, Number(b));
    } else {
      c.gl.drawArrays(Number(mode), Number(a), Number(b));
    }
    return 0n;
  },

  gl_tex_image_from_image(ctx, target, image) {
    const c = glCtx(ctx);
    const rec = images[Number(image)];
    if (!c || !rec || rec.state !== 1) return 0n;
    const gl = c.gl;
    gl.texImage2D(Number(target), 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, rec.img);
    return 1n;
  },

  // Bulk uploads. The C wrapper checked the `Buf`'s kind and length; `kind`
  // is its MONAD_ELEM_* code (2 f32, 3 i32, 4 u8) and `count` its element
  // count, so the view below covers exactly the buffer's payload. 1n once
  // the GL call ran, 0n for an unknown context or uniform.
  gl_buffer_data(ctx, target, sub, a, kind, ptr, count) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const view = elemView(kind, ptr, count);
    if (!view) return 0n;
    if (Number(sub) !== 0) c.gl.bufferSubData(Number(target), Number(a), view);
    else c.gl.bufferData(Number(target), view, Number(a));
    return 1n;
  },

  gl_uniform_matrix(ctx, loc, n, ptr) {
    const c = glCtx(ctx);
    const l = glObj(loc);
    if (!c || !l) return 0n;
    const k = Number(n);
    const m = new Float32Array(memory.buffer, u32(ptr), k * k);
    if (k === 2) c.gl.uniformMatrix2fv(l, false, m);
    else if (k === 3) c.gl.uniformMatrix3fv(l, false, m);
    else if (k === 4) c.gl.uniformMatrix4fv(l, false, m);
    return 1n;
  },

  gl_tex_image_pixels(ctx, target, w, h, ptr) {
    const c = glCtx(ctx);
    if (!c) return 0n;
    const gl = c.gl;
    const W = Number(w);
    const H = Number(h);
    const px = new Uint8Array(memory.buffer, u32(ptr), W * H * 4);
    gl.texImage2D(Number(target), 0, gl.RGBA, W, H, 0, gl.RGBA, gl.UNSIGNED_BYTE, px);
    return 1n;
  },

  // A promise-free two-phase load: the handlers only update the record.
  image_load_begin(ptr, len) {
    const rec = { state: 0, img: null };
    images.push(rec);
    const id = BigInt(images.length - 1);
    const Img = globalThis.Image;
    if (typeof Img !== 'function') {
      rec.state = 2;
      return id;
    }
    const img = new Img();
    img.crossOrigin = 'anonymous';
    img.onload = () => { rec.state = 1; };
    img.onerror = () => { rec.state = 2; };
    rec.img = img;
    img.src = str(ptr, len);
    return id;
  },

  image_info(image, which) {
    const rec = images[Number(image)];
    if (!rec) return Number(which) === 0 ? 2n : 0n;
    switch (Number(which)) {
      case 0: return BigInt(rec.state);
      case 1: return rec.img ? BigInt(rec.img.naturalWidth || rec.img.width || 0) : 0n;
      case 2: return rec.img ? BigInt(rec.img.naturalHeight || rec.img.height || 0) : 0n;
      default: return 0n;
    }
  },

  // The BINARY half of a response body. `fetch_read` returns a Monad
  // String, which is NUL-terminated, so a media or image body would stop at
  // its first zero byte; these two cover the whole body. `fetch_len` is the
  // bytes REMAINING (the read cursor walks), so a partial read is honest.
  fetch_len(id) {
    const r = fetches[Number(id)];
    if (!r || !r.bytes) return 0n;
    return BigInt(Math.max(0, r.bytes.length - r.offset));
  },

  fetch_read_bytes(id, ptr, max) {
    const r = fetches[Number(id)];
    if (!r || !r.bytes) return 0n;
    const n = writeBytes(ptr, r.bytes.subarray(r.offset), max);
    r.offset += Number(n);
    if (r.offset >= r.bytes.length) {
      r.bytes = new Uint8Array(0);
      r.offset = 0;
    }
    return n;
  },

  // ── Sound and audio ────────────────────────────────────────────────
  //
  // Web Audio synthesizes; `<audio>`/`<video>` plays files. They are
  // separate here because they fail separately: a context that never resumed
  // is silent but healthy, while a media element that 404'd reports through
  // its own state. Every id is an index into a table, never a pointer.
  //
  // A `Buf F32` of PCM arrives as (payload, element count); the C wrapper
  // already checked the kind, so the view below covers exactly the buffer.

  audio_open() {
    if (audioCtx) return audioCtxId;
    const AC = globalThis.AudioContext || globalThis.webkitAudioContext;
    if (typeof AC !== 'function') return 0n;
    try {
      audioCtx = new AC();
    } catch (e) {
      audioCtx = null;
      return 0n;
    }
    // The master gain is the one node every voice passes through, so it is
    // where a page-wide mute lives. Unity by default: a program that wants
    // quiet says so.
    try {
      audioMaster = audioCtx.createGain();
      audioMaster.gain.value = 1;
      audioMaster.connect(audioCtx.destination);
    } catch (e) {
      audioMaster = null;
    }
    audioCtxId = 1n;
    return audioCtxId;
  },

  audio_state(ctx) {
    if (!audioCtx || !ctx) return 2n;
    switch (audioCtx.state) {
      case 'suspended': return 0n;
      case 'running': return 1n;
      case 'closed': return 2n;
      case 'interrupted': return 3n;
      default: return 0n;
    }
  },

  // `resume()` is a promise, but it settles into a state `audio_state`
  // already reports, so the answer here is the state RIGHT NOW. A caller
  // that needs certainty polls the state rather than trusting this word.
  audio_resume(ctx) {
    if (!audioCtx || !ctx) return 0n;
    try {
      const p = audioCtx.resume();
      if (p && typeof p.catch === 'function') p.catch(() => {});
    } catch (e) {
      return 0n;
    }
    return audioCtx.state === 'running' ? 1n : 0n;
  },

  audio_now_us(ctx) {
    if (!audioCtx || !ctx) return 0n;
    return BigInt(Math.round(audioCtx.currentTime * 1e6));
  },

  audio_sample_rate(ctx) {
    if (!audioCtx || !ctx) return 0n;
    return BigInt(Math.round(audioCtx.sampleRate || 0));
  },

  audio_set_master(ctx, gain) {
    if (!audioCtx || !audioMaster || !ctx) return 0n;
    audioMaster.gain.value = Number(gain);
    return 0n;
  },

  // One oscillator voice with a linear attack/release envelope. It is
  // scheduled start-to-stop in one go: a short SFX must not depend on a
  // later wasm call to end it, because the app may never make one.
  audio_tone(ctx, wave, freq, gain, duration_ms, attack_ms, release_ms) {
    if (!audioCtx || !ctx) return 0n;
    const d = Number(duration_ms) / 1000;
    if (!(d > 0)) return 0n;
    const a = Number(attack_ms) / 1000;
    const r = Number(release_ms) / 1000;
    try {
      const osc = audioCtx.createOscillator();
      osc.type = OSC_TYPES[Number(wave)] || 'sine';
      osc.frequency.value = Number(freq);
      const env = audioCtx.createGain();
      const t0 = audioCtx.currentTime;
      const peak = Number(gain);
      // A zero attack would be a click; `setValueAtTime` first keeps the
      // ramp's start well-defined even when the browser's clock has moved.
      env.gain.setValueAtTime(0, t0);
      env.gain.linearRampToValueAtTime(peak, t0 + a);
      env.gain.setValueAtTime(peak, t0 + Math.max(a, d - r));
      env.gain.linearRampToValueAtTime(0, t0 + d);
      osc.connect(env);
      env.connect(audioMaster || audioCtx.destination);
      osc.start(t0);
      osc.stop(t0 + d);
      audioNodes.push(osc);
      return BigInt(audioNodes.length - 1);
    } catch (e) {
      return 0n;
    }
  },

  audio_stop(node) {
    const n = audioNodes[Number(node)];
    if (!n) return 0n;
    try {
      n.stop(0);
    } catch (e) {
      /* already stopped: the voice stopped itself at its scheduled end */
    }
    return 0n;
  },

  // A white-noise burst through an optional lowpass. Two seconds is the
  // ceiling: a noise node is a long buffer the browser materialises, and an
  // app that asks for a minute of it has a stuck parameter, not a sound.
  audio_noise(ctx, gain, duration_ms, lowpass_hz) {
    if (!audioCtx || !ctx) return 0n;
    let d = Number(duration_ms) / 1000;
    if (!(d > 0)) return 0n;
    if (d > NOISE_MAX_SECONDS) d = NOISE_MAX_SECONDS;
    try {
      const frames = Math.max(1, Math.floor(audioCtx.sampleRate * d));
      const buf = audioCtx.createBuffer(1, frames, audioCtx.sampleRate);
      const ch = buf.getChannelData(0);
      for (let i = 0; i < frames; i++) ch[i] = Math.random() * 2 - 1;
      const src = audioCtx.createBufferSource();
      src.buffer = buf;
      const env = audioCtx.createGain();
      const t0 = audioCtx.currentTime;
      const peak = Number(gain);
      env.gain.setValueAtTime(peak, t0);
      // A short release so the burst does not end on a sample boundary
      // discontinuity (a click at these amplitudes is audible).
      const rel = Math.min(0.02, d / 4);
      env.gain.setValueAtTime(peak, t0 + d - rel);
      env.gain.linearRampToValueAtTime(0, t0 + d);
      let tail = env;
      if (Number(lowpass_hz) > 0) {
        const f = audioCtx.createBiquadFilter();
        f.type = 'lowpass';
        f.frequency.value = Number(lowpass_hz);
        env.connect(f);
        tail = f;
      }
      src.connect(env);
      tail.connect(audioMaster || audioCtx.destination);
      src.start(t0);
      src.stop(t0 + d);
      audioNodes.push(src);
      return BigInt(audioNodes.length - 1);
    } catch (e) {
      return 0n;
    }
  },

  // Mono PCM from wasm. The frames are COPIED into an AudioBuffer before the
  // view is used: a buffer the wasm heap owns can move when memory grows, and
  // the source node outlives this call.
  audio_play_pcm(ctx, ptr, count, sample_rate, gain) {
    if (!audioCtx || !ctx) return 0n;
    const n = Number(count);
    if (!(n > 0)) return 0n;
    try {
      const view = new Float32Array(memory.buffer, u32(ptr), n).slice();
      const buf = audioCtx.createBuffer(1, n, Number(sample_rate));
      buf.copyToChannel(view, 0);
      const src = audioCtx.createBufferSource();
      src.buffer = buf;
      const env = audioCtx.createGain();
      env.gain.value = Number(gain);
      src.connect(env);
      env.connect(audioMaster || audioCtx.destination);
      src.start();
      audioNodes.push(src);
      return BigInt(audioNodes.length - 1);
    } catch (e) {
      return 0n;
    }
  },

  // `decodeAudioData` detaches its input ArrayBuffer, so the bytes are
  // copied off the wasm heap first -- and copied BEFORE the promise, which
  // is also why this is two-phase: the callback must not re-enter wasm.
  audio_decode_begin(ctx, ptr, len) {
    const rec = { state: 0, buffer: null, error: '' };
    audioDecodes.push(rec);
    const id = BigInt(audioDecodes.length - 1);
    if (!audioCtx || !ctx) {
      rec.state = 2;
      rec.error = 'InvalidStateError';
      return id;
    }
    const bytes = new Uint8Array(memory.buffer, u32(ptr), Number(len)).slice();
    const p = audioCtx.decodeAudioData(bytes.buffer);
    if (!p || typeof p.then !== 'function') {
      rec.state = 2;
      rec.error = 'NotSupportedError';
      return id;
    }
    p.then((buf) => { rec.buffer = buf; rec.state = 1; })
      .catch((err) => { rec.error = (err && err.name) || 'Error'; rec.state = 2; });
    return id;
  },

  audio_decode_poll(op) {
    const rec = audioDecodes[Number(op)];
    return rec ? BigInt(rec.state) : 2n;
  },

  audio_decode_sound(op) {
    const rec = audioDecodes[Number(op)];
    if (!rec || rec.state !== 1 || !rec.buffer) return 0n;
    audioSounds.push(rec.buffer);
    return BigInt(audioSounds.length - 1);
  },

  audio_decode_error(op, ptr, max) {
    const rec = audioDecodes[Number(op)];
    if (!rec) return 0n;
    return writeBytes(ptr, encoder.encode(rec.error || ''), max);
  },

  // `offset`/`duration` are 0 for "all of it", which is why the C side
  // clamps them to non-negative rather than treating 0 as a real duration.
  audio_play_sound(ctx, sound, gain, offset_ms, duration_ms) {
    if (!audioCtx || !ctx) return 0n;
    const buf = audioSounds[Number(sound)];
    if (!buf) return 0n;
    try {
      const src = audioCtx.createBufferSource();
      src.buffer = buf;
      const env = audioCtx.createGain();
      env.gain.value = Number(gain);
      src.connect(env);
      env.connect(audioMaster || audioCtx.destination);
      const off = Number(offset_ms) / 1000;
      const dur = Number(duration_ms) / 1000;
      if (off > 0 && dur > 0) src.start(0, off, dur);
      else if (off > 0) src.start(0, off);
      else if (dur > 0) src.start(0, 0, dur);
      else src.start();
      audioNodes.push(src);
      return BigInt(audioNodes.length - 1);
    } catch (e) {
      return 0n;
    }
  },

  audio_sound_duration_ms(sound) {
    const buf = audioSounds[Number(sound)];
    if (!buf) return 0n;
    return BigInt(Math.round((buf.duration || 0) * 1000));
  },

  // ── `<audio>` / `<video>` element control ──────────────────────────
  //
  // The element is mounted by the view, so every call resolves a selector.
  // A miss returns 0 rather than throwing: a selector typo is a bug the
  // caller must be able to SEE (`MediaElement.play` reports it), but it is
  // not a reason to break a frame.

  media_play(ptr, len) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    try {
      const p = el.play();
      if (p && typeof p.catch === 'function') {
        // The autoplay policy rejects with NotAllowedError; record it so a
        // later `media_info` read can report the block instead of the page
        // looking merely paused.
        p.catch((err) => {
          el.__oakPlayBlocked = (err && err.name) || 'Error';
        });
        return 1n;
      }
      return 1n;
    } catch (e) {
      return 3n;
    }
  },

  media_pause(ptr, len) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    el.pause();
    el.__oakPlayBlocked = '';
    return 1n;
  },

  media_seek(ptr, len, ms) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    const want = Number(ms) / 1000;
    // Clamp to the known duration: seeking past the end leaves the element
    // in `ended` with an unmovable `currentTime`, which reads as a bug.
    const dur = el.duration;
    el.currentTime = Number.isFinite(dur) && dur > 0 ? Math.min(want, dur) : want;
    return 1n;
  },

  media_set_volume(ptr, len, volume) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    el.volume = Number(volume);
    return 1n;
  },

  media_set_muted(ptr, len, muted) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    el.muted = Number(muted) !== 0;
    return 1n;
  },

  media_set_loop(ptr, len, looping) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 0n;
    el.loop = Number(looping) !== 0;
    return 1n;
  },

  media_info(ptr, len, which) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 3n; // "no such element", distinct from paused
    switch (Number(which)) {
      case 0: return el.paused ? 1n : 0n;
      case 1: return el.ended ? 1n : 0n;
      case 2: return BigInt(el.readyState || 0);
      case 3: return el.seeking ? 1n : 0n;
      case 4: return el.muted ? 1n : 0n;
      case 5: return el.loop ? 1n : 0n;
      case 6: return BigInt(Math.round((el.playbackRate || 1) * 1000));
      // `blocked` and `present` are ABOUT the element rather than read off
      // it. A missing element answered 3 above, which no field here can be
      // confused with.
      case 7: return el.__oakPlayBlocked ? 1n : 0n; // autoplay-blocked
      case 8: return 1n; // present
      default: return 0n;
    }
  },

  // 0 `currentTime`, 1 `duration`; whole milliseconds, and -1 for a
  // duration the metadata has not supplied yet (`NaN` before load), so a
  // caller can tell "unknown" from "zero length".
  media_time_ms(ptr, len, which) {
    const el = mediaEl(str(ptr, len));
    if (!el) return -1n;
    if (Number(which) === 1) {
      const d = el.duration;
      return Number.isFinite(d) ? BigInt(Math.round(d * 1000)) : -1n;
    }
    const t = el.currentTime;
    return Number.isFinite(t) ? BigInt(Math.round(t * 1000)) : 0n;
  },

  media_volume(ptr, len) {
    const el = mediaEl(str(ptr, len));
    if (!el) return 1;
    return el.volume;
  },

  write_stdout(ptr, len) {
    const text = str(ptr, len);
    const out = globalThis.process && globalThis.process.stdout;
    if (out) out.write(text);
    else console.log(text);
    return BigInt(Number(len));
  },

  write_stderr(ptr, len) {
    const text = str(ptr, len);
    const out = globalThis.process && globalThis.process.stderr;
    if (out) out.write(text);
    else console.error(text);
    return BigInt(Number(len));
  },

  read_stdin() {
    return 0n; // interactive stdin is not part of the SPA ABI
  },

  // `F64.to_string` on the freestanding web profile: the host owns the
  // float -> decimal formatting the profile's missing libc would do.
  f64_to_string(bits, ptr, max) {
    const view = new DataView(new ArrayBuffer(8));
    view.setBigUint64(0, BigInt.asUintN(64, BigInt(bits)), true);
    return writeBytes(ptr, encoder.encode(f64ToRustString(view.getFloat64(0, true))), max);
  },
};
