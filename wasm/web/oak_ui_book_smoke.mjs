#!/usr/bin/env node
// Node smoke test for the oak_ui component explorer. Usage:
//   node wasm/web/oak_ui_book_smoke.mjs <oak_ui_book.wasm>
//
// Built from `motes/oak_ui_book` (`--bin book`). Drives the REAL
// `web_runtime.js` and generated `web.js` over `stub_dom.mjs`, with a
// Map-backed localStorage, and checks the explorer end to end:
//   * the stored story/theme are restored on the first animation frame;
//   * a story's button click lands in the Actions log;
//   * a knob edit re-renders the story;
//   * the theme switch re-themes the frame and is persisted;
//   * selecting a story from the sidebar, opening its modal and closing it
//     with Escape (the controlled overlay round trip).

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';
import { body, installDocument, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/oak_ui_book_smoke.mjs <oak_ui_book.wasm>');
  process.exit(2);
}

const stored = new Map([['oak-ui-book.story', 'button'], ['oak-ui-book.theme', 'light']]);
globalThis.localStorage = {
  getItem: (k) => (stored.has(k) ? stored.get(k) : null),
  setItem: (k, v) => { stored.set(k, String(v)); },
  removeItem: (k) => { stored.delete(k); },
};

let pendingFrame = null;
globalThis.requestAnimationFrame = (cb) => { pendingFrame = cb; return 1; };
globalThis.cancelAnimationFrame = () => {};
function frame() {
  const cb = pendingFrame;
  pendingFrame = null;
  if (cb) cb(performance.now());
}

installDocument();
const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();
host.start_ticks(instance);

const tick = () => instance.exports.oak_tick();

function findAll(node, pred, acc = []) {
  for (const child of node.childNodes) {
    if (child.nodeType === 1) {
      if (pred(child)) acc.push(child);
      findAll(child, pred, acc);
    }
  }
  return acc;
}
const all = (pred) => findAll(body, pred);
const one = (pred, what) => {
  const found = all(pred)[0];
  if (!found) fail(`not found: ${what}`);
  return found;
};
const hasClass = (n, c) => (n.attrs.class || '').split(' ').includes(c);
const title = () => one((n) => n.tagName === 'H1', 'the story title').textContent;
const frames = () => all((n) => hasClass(n, 'book-frame'));

// 1. Preferences: the first animation frame asks the host for them.
frame();
tick();
tick();
if (title() !== 'Button') fail(`stored story not restored; title is ${JSON.stringify(title())}`);

// 2. The story's button logs its click.
const storyButton = one((n) => n.tagName === 'BUTTON' && n.textContent === 'Save changes', 'the story button');
storyButton.fire('click');
tick();
const actionsTab = one((n) => n.attrs.role === 'tab' && n.textContent.startsWith('Actions'), 'the Actions tab');
if (actionsTab.textContent !== 'Actions (1)') fail(`Actions tab reads ${JSON.stringify(actionsTab.textContent)}`);

// 3. A knob edit re-renders the story.
const labelKnob = one((n) => n.tagName === 'INPUT' && n.attrs.id === 'knob-label', 'the label knob');
labelKnob.value = 'Ship it';
labelKnob.fire('input');
tick();
one((n) => n.tagName === 'BUTTON' && n.textContent === 'Ship it', 'the relabelled story button');

// 4. Theme switch: the frame follows and the choice is persisted.
one((n) => n.tagName === 'BUTTON' && n.textContent === 'Dark', 'the Dark theme button').fire('click');
tick();
tick();
if (frames().length !== 1 || frames()[0].attrs['data-theme'] !== 'dark') {
  fail(`frame theme is ${JSON.stringify(frames().map((f) => f.attrs['data-theme']))}`);
}
if (stored.get('oak-ui-book.theme') !== 'dark') fail(`theme not persisted: ${stored.get('oak-ui-book.theme')}`);
one((n) => n.tagName === 'BUTTON' && n.textContent === 'Both', 'the Both theme button').fire('click');
tick();
if (frames().length !== 2) fail(`side-by-side shows ${frames().length} frames`);

// 5. Sidebar navigation, then the modal round trip.
const modalLink = one((n) => n.tagName === 'A' && n.textContent === 'Modal and drawer', 'the Modal story link');
const click = modalLink.fire('click');
if (!click.defaultPrevented) fail('the sidebar link click was not default-prevented');
tick();
if (title() !== 'Modal and drawer') fail(`sidebar did not select the story; title is ${JSON.stringify(title())}`);
if (stored.get('oak-ui-book.story') !== 'modal') fail(`story not persisted: ${stored.get('oak-ui-book.story')}`);
one((n) => n.tagName === 'BUTTON' && n.textContent === 'Open modal', 'the Open modal button').fire('click');
tick();
const dialogs = all((n) => n.attrs.role === 'dialog');
if (dialogs.length !== 2) fail(`expected one open dialog per frame (2), found ${dialogs.length}`);
const esc = dialogs[0].fire('keydown', { key: 'Escape' });
if (!esc.defaultPrevented) fail('Escape was not default-prevented');
tick();
if (all((n) => n.attrs.role === 'dialog').length !== 0) fail('Escape did not close the modal');

console.log(`ok: ${path} -> explorer restores prefs, logs actions, applies knobs and themes, opens and closes a modal`);
