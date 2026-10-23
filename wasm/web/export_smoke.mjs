#!/usr/bin/env node
// Node smoke test for `#[export "c"]`. Usage:
//   node wasm/web/export_smoke.mjs <module.wasm>
//
// Built from fixtures/wasm/export_probe.mo. Asserts the three properties
// the export ABI promises:
//
//   1. `probe_add` and `probe_emit` are EXPORTED under their source names
//      (the compiler emits every def under its module-qualified symbol and
//      adds a thunk for each export, because `wasm-ld --export=` cannot
//      rename);
//   2. a pure i64 export is callable and returns its value;
//   3. an `IO`-typed export performs its effects when CALLED (`io_bind`
//      applies its continuation eagerly) and returns the `IO.mk` box,
//      which JS ignores.

import { readFile } from 'node:fs/promises';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/export_smoke.mjs <module.wasm>');
  process.exit(2);
}

const bytes = await readFile(path);
let memory = null;
let stdout = '';

const imports = {
  monad: {
    write_stdout(ptr, len) {
      stdout += Buffer.from(memory.buffer, Number(ptr), Number(len)).toString('utf8');
      return 0n;
    },
    write_stderr() {
      return 0n;
    },
    read_stdin() {
      return 0n;
    },
    now_ms() {
      return BigInt(Date.now());
    },
  },
};

const module = new WebAssembly.Module(bytes);
const names = WebAssembly.Module.exports(module).map((e) => e.name);
for (const want of ['probe_add', 'probe_emit']) {
  if (!names.includes(want)) {
    console.error(`missing export ${want}; exports are ${names.join(', ')}`);
    process.exit(1);
  }
}

const instance = await WebAssembly.instantiate(module, imports);
memory = instance.exports.memory;

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
