#!/usr/bin/env node
// Node smoke test for the /try engine's staging ABI.
//   node wasm/web/try_abi_smoke.mjs <try_abi.wasm>
//
// Asserts the two properties Phase 0 exists to retire:
//   1. the C-only `try_alloc` export hands JS a writable Number pointer into
//      linear memory (a no-header bump allocation);
//   2. a `#[export "c"]` def taking a `String` PARAMETER receives the exact
//      UTF-8 JS wrote, through the (ptr,len) boundary.
//
// Also prints the module's imports and exports, which is the gated-native
// audit the engine's harnesses repeat: a `read_file`/`exec_cmd`/`get_env`
// import here would mean the pure pipeline reached a native the web profile
// cannot serve.

import { readFile } from 'node:fs/promises';
import { imports } from './web.js';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/try_abi_smoke.mjs <try_abi.wasm>');
  process.exit(2);
}

const bytes = await readFile(path);
let memory = null;
let stdout = '';

const importObject = {
  monad: {
    ...imports.monad,
    write_stdout(ptr, len) {
      stdout += Buffer.from(memory.buffer, Number(ptr), Number(len)).toString('utf8');
      return 0n;
    },
  },
};

const module = new WebAssembly.Module(bytes);
const exported = WebAssembly.Module.exports(module).map((e) => e.name);
const imported = WebAssembly.Module.imports(module).map((i) => `${i.module}.${i.name}`);

function fail(message) {
  console.error(message);
  process.exit(1);
}

for (const want of ['try_alloc', 'try_echo', 'monad_main', 'memory']) {
  if (!exported.includes(want)) fail(`missing export ${want}; exports are ${exported.join(', ')}`);
}

const instance = await WebAssembly.instantiate(module, importObject);
memory = instance.exports.memory;

const text = 'hello from js — 世界 ✓';
const utf8 = new TextEncoder().encode(text);

// 1. The allocator export is a pointer into linear memory. C's int64_t
//    parameter crosses as an i64 (BigInt); the int32_t return is a Number.
const raw = instance.exports.try_alloc(BigInt(utf8.length + 1));
const ptr = Number(raw);
if (typeof raw !== 'number' && typeof raw !== 'bigint') {
  fail(`try_alloc returned a ${typeof raw}, expected a pointer`);
}
if (ptr <= 0) fail(`try_alloc returned ${raw}`);
if (ptr + utf8.length + 1 > memory.buffer.byteLength) {
  fail(`try_alloc returned ${ptr}, outside ${memory.buffer.byteLength} bytes of memory`);
}

// 2. Write UTF-8 + NUL and hand the pointer to the String export.
const view = new Uint8Array(memory.buffer, ptr, utf8.length + 1);
view.set(utf8);
view[utf8.length] = 0;

instance.exports.try_echo(BigInt(ptr));
if (stdout !== text) {
  fail(`try_echo saw ${JSON.stringify(stdout)}, expected ${JSON.stringify(text)}`);
}

console.log(`ok: ${path} -> try_alloc + String export param round-trip`);
console.log(`imports: ${imported.join(', ') || '(none)'}`);
console.log(`exports: ${exported.join(', ')}`);
