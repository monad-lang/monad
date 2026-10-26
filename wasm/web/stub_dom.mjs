// A minimal stub DOM shared by the Node harnesses.
//
// The harnesses drive the REAL `wasm/web/web_runtime.js` and the generated
// `wasm/web/web.js` import object over this tree, so the externs, the C
// wrappers and the JS host are checked against each other -- not against
// hand-written mocks of each side.
//
// It models exactly the DOM surface the runtime uses: childNodes (text
// nodes included), attributes, listeners, nodeType, tagName, value, and a
// tiny selector match for `document.querySelector`. Real-DOM semantics that
// the patcher depends on are preserved deliberately:
//   * `insertBefore` DETACHES a node from its previous parent (a keyed
//     `move` relies on this; without it a moved node appears twice);
//   * `insertBefore(node, null)` appends;
//   * setting the `value` attribute on an INPUT mirrors `value` (the
//     default-value behavior `Dom.value` reads);
//   * `textContent` returns `_text` for non-element nodes and the joined
//     children for elements.

export class FakeDataTransfer {
  constructor() {
    this._data = {};
    this.effectAllowed = 'uninitialized';
    this.dropEffect = 'none';
    this.files = [];
  }

  setData(mime, value) {
    this._data[mime] = String(value);
  }

  getData(mime) {
    return this._data[mime] || '';
  }

  clearData(mime) {
    if (mime) delete this._data[mime];
    else this._data = {};
  }

  get types() {
    return Object.keys(this._data);
  }
}

export class FakeEvent {
  constructor(type, init = {}) {
    this.type = type;
    this.target = init.target || null;
    this.defaultPrevented = false;
    this.stopped = false;
    this.preventCount = 0;
    this.stopCount = 0;
    this.dataTransfer = init.dataTransfer || null;
    this.clipboardData = init.clipboardData || null;
    for (const [k, v] of Object.entries(init)) {
      if (k !== 'target') this[k] = v;
    }
  }

  preventDefault() {
    this.defaultPrevented = true;
    this.preventCount += 1;
  }

  stopPropagation() {
    this.stopped = true;
    this.stopCount += 1;
  }
}

export class FakeNode {
  constructor(nodeType, tagName) {
    this.nodeType = nodeType;
    this.tagName = tagName;
    this.childNodes = [];
    this.attrs = {};
    this.listeners = {};
    this.parentNode = null;
    this._text = '';
    this.value = '';
    this.checked = false;
  }

  appendChild(child) {
    if (child.parentNode) child.parentNode.removeChild(child);
    child.parentNode = this;
    this.childNodes.push(child);
    return child;
  }

  insertBefore(child, before) {
    // Real DOM insertBefore moves an already-attached node.
    if (child.parentNode) child.parentNode.removeChild(child);
    const at = before ? this.childNodes.indexOf(before) : -1;
    child.parentNode = this;
    if (at < 0) this.childNodes.push(child);
    else this.childNodes.splice(at, 0, child);
    return child;
  }

  removeChild(child) {
    const at = this.childNodes.indexOf(child);
    if (at >= 0) this.childNodes.splice(at, 1);
    child.parentNode = null;
    return child;
  }

  replaceChild(next, old) {
    if (next.parentNode) next.parentNode.removeChild(next);
    const at = this.childNodes.indexOf(old);
    if (at >= 0) this.childNodes[at] = next;
    next.parentNode = this;
    old.parentNode = null;
    return old;
  }

  setAttribute(name, value) {
    this.attrs[name] = value;
    // `input.value` reflects its value attribute until it is dirtied.
    if (name === 'value' && this.tagName === 'INPUT') this.value = value;
  }

  removeAttribute(name) {
    delete this.attrs[name];
  }

  getAttribute(name) {
    return Object.prototype.hasOwnProperty.call(this.attrs, name) ? this.attrs[name] : null;
  }

  addEventListener(event, handler, options) {
    (this.listeners[event] ||= []).push({ handler, options: options || {} });
  }

  removeEventListener(event, handler, options) {
    const capture = !!(options && options.capture);
    const entries = this.listeners[event] || [];
    this.listeners[event] = entries.filter(
      (e) => !(e.handler === handler && !!e.options.capture === capture),
    );
  }

  fire(event, init) {
    const evt = init instanceof FakeEvent ? init : new FakeEvent(event, { target: this, ...(init || {}) });
    const entries = (this.listeners[event] || []).slice();
    for (const entry of entries) {
      entry.handler(evt);
      if (entry.options && entry.options.once) {
        this.removeEventListener(event, entry.handler, entry.options);
      }
    }
    return evt;
  }

  get textContent() {
    if (this.nodeType === 1) return this.childNodes.map((c) => c.textContent).join('');
    return this._text;
  }

  set textContent(value) {
    this.childNodes = [];
    this._text = '';
    if (value === '') return;
    const t = new FakeNode(3, '#text');
    t.nodeValue = value;
    t.parentNode = this;
    this.childNodes.push(t);
  }

  get nodeValue() {
    return this._text;
  }

  set nodeValue(value) {
    this._text = value;
  }
}

/// Module-level observation of `createElement`, for identity/count asserts.
export const stub = {
  lastCreated: null,
  createdCount: 0,
  clipboardText: 'from-clipboard',
  clipboardWritten: null,
};

export const body = new FakeNode(1, 'BODY');

function matches(node, selector) {
  if (selector.startsWith('#')) return node.attrs && node.attrs.id === selector.slice(1);
  return node.tagName && node.tagName.toLowerCase() === selector.toLowerCase();
}

function find(node, selector) {
  for (const child of node.childNodes) {
    if (child.nodeType !== 1) continue;
    if (matches(child, selector)) return child;
    const deeper = find(child, selector);
    if (deeper) return deeper;
  }
  return null;
}

/// Install the `document` the runtime talks to. `#app` is the mount
/// container the harnesses select, and is `body`; `body` is `body`; any
/// other selector is matched against the tree (null when absent, which the
/// runtime turns into a thrown "mount selector not found").
export function installDocument() {
  // `document` and `window` are event targets too: give them the same
  // listener bookkeeping a node has, so global subscriptions are observable.
  const documentEvents = new FakeNode(9, '#document');
  const windowEvents = new FakeNode(9, '#window');

  globalThis.document = {
    body,
    querySelector(selector) {
      if (selector === 'body' || selector === '#app') return body;
      return find(body, selector);
    },
    createElement(tag) {
      stub.lastCreated = new FakeNode(1, tag.toUpperCase());
      stub.createdCount += 1;
      return stub.lastCreated;
    },
    createTextNode(text) {
      stub.lastCreated = new FakeNode(3, '#text');
      stub.lastCreated.nodeValue = text;
      return stub.lastCreated;
    },
    createComment(text) {
      stub.lastCreated = new FakeNode(8, '#comment');
      stub.lastCreated.nodeValue = text;
      return stub.lastCreated;
    },
    listeners: documentEvents.listeners,
    addEventListener: documentEvents.addEventListener.bind(documentEvents),
    removeEventListener: documentEvents.removeEventListener.bind(documentEvents),
    fire: documentEvents.fire.bind(documentEvents),
  };

  globalThis.window = {
    listeners: windowEvents.listeners,
    addEventListener: windowEvents.addEventListener.bind(windowEvents),
    removeEventListener: windowEvents.removeEventListener.bind(windowEvents),
    fire: windowEvents.fire.bind(windowEvents),
  };

  // Node exposes `navigator` as a getter-only global; define our own.
  Object.defineProperty(globalThis, 'navigator', {
    value: {
      clipboard: {
        readText: () => Promise.resolve(stub.clipboardText),
        writeText: (text) => { stub.clipboardWritten = text; return Promise.resolve(); },
      },
    },
    configurable: true,
    writable: true,
  });
}

export function fail(message) {
  console.error(message);
  process.exit(1);
}
