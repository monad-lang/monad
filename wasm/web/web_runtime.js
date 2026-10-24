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
const fetches = []; // id -> { state, status, bytes, offset }

const EVENT_PREFIX = 'data-oak-on-';

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

// Register (or REPLACE) the listener for one event on one node. A re-render
// that changes a handler id must not stack a second listener, and removing
// the attribute must unregister.
function setListener(n, event, id) {
  let table = listenerTables.get(n);
  if (!table) {
    table = new Map();
    listenerTables.set(n, table);
  }
  const previous = table.get(event);
  if (previous) n.removeEventListener(event, previous.wrapper);
  if (id === null) {
    table.delete(event);
    return;
  }
  const wrapper = () => {
    const dispatch = instance && instance.exports.oak_dispatch_event;
    if (dispatch) dispatch(id);
  };
  n.addEventListener(event, wrapper);
  table.set(event, { id, wrapper });
}

function clearListener(n, event) {
  const table = listenerTables.get(n);
  if (!table) return;
  const previous = table.get(event);
  if (previous) n.removeEventListener(event, previous.wrapper);
  table.delete(event);
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
    const loop = () => {
      if (instance !== inst) return;
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
      setListener(n, name.slice(EVENT_PREFIX.length), idFromText(value));
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

  dom_add_listener(node, eptr, elen, handler) {
    const n = nodeById(node);
    if (!n) return 0n;
    setListener(n, str(eptr, elen), BigInt(handler));
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
