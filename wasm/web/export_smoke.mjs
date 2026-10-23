#!/usr/bin/env node
// Node smoke test for `#[export "c"]`. Usage:
//   node wasm/web/export_smoke.mjs <module.wasm> [exports-only|keep]
//
// The default mode runs fixtures/wasm/export_probe.mo and asserts the three
// properties the export ABI promises:
//
//   1. `probe_add` and `probe_emit` are EXPORTED under their source names
//      (the compiler emits every def under its module-qualified symbol and
//      adds a thunk for each export, because `wasm-ld --export=` cannot
//      rename);
//   2. a pure i64 export is callable and returns its value;
//   3. an `IO`-typed export performs its effects when CALLED (`io_bind`
//      applies its continuation eagerly) and returns the `IO.mk` box,
//      which JS ignores.
//
// The `exports-only` mode runs fixtures/wasm/export_only.mo: no `def main`,
// so the runtime's weak `main_monad` is 0, the module still links, and
// `monad_main` returns 0 while the exports work.
//
// The `keep` mode runs fixtures/wasm/web_keep.mo: one export saves a `Ref`
// through the JS state slot, a later export reads it back and logs it --
// the state channel every SPA export call relies on.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';
import { host } from './web_runtime.js';

const path = process.argv[2];
const mode = process.argv[3] ?? 'probe';
if (!path) {
  console.error('usage: node wasm/web/export_smoke.mjs <module.wasm> [exports-only|keep]');
  process.exit(2);
}
const exportsOnly = mode === 'exports-only';
const keepMode = mode === 'keep';

const bytes = await readFile(path);
let memory = null;
let stdout = '';
const logs = [];

const importObject = {
  monad: {
    ...imports.monad,
    write_stdout(ptr, len) {
      stdout += Buffer.from(memory.buffer, Number(ptr), Number(len)).toString('utf8');
      return 0n;
    },
    console_log(ptr, len) {
      logs.push(Buffer.from(memory.buffer, Number(ptr), Number(len)).toString('utf8'));
      return 0n;
    },
  },
};

const module = new WebAssembly.Module(bytes);
const names = WebAssembly.Module.exports(module).map((e) => e.name);
if (exportsOnly) {
  for (const want of ['only_add', 'monad_main']) {
    if (!names.includes(want)) {
      console.error(`missing export ${want}; exports are ${names.join(', ')}`);
      process.exit(1);
    }
  }
  const instance = await WebAssembly.instantiate(module, importObject);
  memory = instance.exports.memory;
  const rc = instance.exports.monad_main(0n);
  if (rc !== 0n) {
    console.error(`monad_main without a def main returned ${rc}`);
    process.exit(1);
  }
  const sum = instance.exports.only_add(1n);
  if (sum !== 6n) {
    console.error(`only_add(1) returned ${sum}`);
    process.exit(1);
  }
  console.log(`ok: ${path} -> exports-only module, monad_main is a no-op`);
  process.exit(0);
}

if (keepMode) {
  // The state slot lives in the REAL runtime, so bind the instance to it.
  const instance = await WebAssembly.instantiate(module, importObject);
  memory = instance.exports.memory;
  host.bind(instance);
  instance.exports.probe_set();
  instance.exports.probe_get();
  if (logs.length !== 1 || logs[0] !== '41') {
    console.error(`Keep round-trip failed; console saw ${JSON.stringify(logs)}`);
    process.exit(1);
  }
  console.log(`ok: ${path} -> Keep carried a Ref between export calls`);
  process.exit(0);
}

for (const want of ['probe_add', 'probe_emit']) {
  if (!names.includes(want)) {
    console.error(`missing export ${want}; exports are ${names.join(', ')}`);
    process.exit(1);
  }
}

const instance = await WebAssembly.instantiate(module, importObject);
memory = instance.exports.memory;
host.bind(instance);

const sum = instance.exports.probe_add(41n);
if (sum !== 42n) {
  console.error(`probe_add(41) returned ${sum}`);
  process.exit(1);
}

instance.exports.probe_emit();
if (stdout !== 'probe\n') {
  console.error(
    `probe_emit did not perform its IO when called: stdout is ${JSON.stringify(stdout)}`,
  );
  process.exit(1);
}

console.log(`ok: ${path} -> exports probe_add/probe_emit, eager IO`);


