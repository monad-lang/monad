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
let kept = 0n; // the export-call state slot (`Keep.save`/`Keep.load`)

const nodes = [null]; // id -> DOM node; 0 is the null handle
const nodeIds = new WeakMap(); // node -> id, so a re-read keeps its handle
const listenerTables = new WeakMap(); // node -> Map(event -> { id, wrapper })
const globalTables = new Map(); // "target:event" -> { flags, wrapper }
let frameHandler = null; // the animation-frame subscription's handler id
const fetches = []; // id -> { state, status, bytes, offset }
const clips = []; // id -> { state, text, error }

const EVENT_PREFIX = 'data-oak-on-';
const EVENT_FLAGS = 'cdsop';

// The live event, set only for the duration of the synchronous
// `oak_dispatch_event` export call. Getters read it; after the call it is
// restored, so an event read from a later tick is `valid = 0`.
let currentEvent = null;

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
    once: false, passive: false,
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
  const id = nodeIds.get(n);
  if (id !== undefined) {
    nodes[id] = null;
    nodeIds.delete(n);
  }
  const children = n.childNodes || [];
  for (let i = 0; i < children.length; i++) forget(children[i]);
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
  if (entry) {
    n.removeEventListener(event, entry.wrapper, { capture: entry.flags.capture });
  }
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
  n.addEventListener(event, wrapper, {
    capture: parsed.flags.capture,
    once: parsed.flags.once,
    passive: parsed.flags.passive,
  });
  table.set(event, { id: parsed.id, flags: parsed.flags, wrapper });
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

function str(ptr, len) {
  // Re-read the buffer on every call: memory.grow detaches the old one.
  return decoder.decode(new Uint8Array(memory.buffer, Number(ptr), Number(len)));
}

// Copy `bytes` into the caller's wasm buffer, capped at `max`; returns the
// byte count written.
function writeBytes(ptr, bytes, max) {
  const n = Math.min(bytes.length, Number(max));
  new Uint8Array(memory.buffer, Number(ptr), n).set(bytes.subarray(0, n));
  return BigInt(n);
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
    return 0n;
  },

  dom_remove_attr(node, kptr, klen) {
    const n = nodeById(node);
    if (!n) return 0n;
    const name = str(kptr, klen);
    if (name.startsWith(EVENT_PREFIX)) clearListener(n, name.slice(EVENT_PREFIX.length));
    n.removeAttribute(name);
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
    const url = str(uptr, ulen);
    const hasBody = Number(method) !== 0;
    const body = hasBody ? str(bptr, blen) : undefined;
    const record = { state: 0, status: 0, bytes: new Uint8Array(0), offset: 0 };
    fetches.push(record);
    const id = BigInt(fetches.length - 1);
    globalThis
      .fetch(url, { method: methodName(method), body })
      .then((r) => {
        record.status = r.status;
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
  },

  fetch_poll(id) {
    const r = fetches[Number(id)];
    return BigInt(r ? r.state : 2);
  },

  fetch_status(id) {
    const r = fetches[Number(id)];
    return BigInt(r ? r.status : 0);
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

  console_log(ptr, len) {
    console.log(str(ptr, len));
    return 0n;
  },

  // Opaque state for the export calls: a Monad `Ref` word, stored verbatim.
  keep_set(value) {
    kept = value;
    return 0n;
  },

  keep_get() {
    return kept;
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
