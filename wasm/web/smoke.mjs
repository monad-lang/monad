#!/usr/bin/env node
// Node smoke test for the web profile. Usage:
//   node wasm/web/smoke.mjs <module.wasm> [expected-stdout]
//
// Asserts the module instantiates with the `monad` imports it declares,
// exports monad_main/memory, runs `monad_main(0n)`, returns 0, and prints
// the expected text (default "hello") followed by a newline.

import { readFile } from 'node:fs/promises';
import { f64ToRustString } from './float_format.js';

const path = process.argv[2];
const expected = process.argv[3] ?? 'hello';
if (!path) {
  console.error('usage: node wasm/web/smoke.mjs <module.wasm> [expected-stdout]');
  process.exit(2);
}

const bytes = await readFile(path);

let memory = null;
let stdout = '';
let stderr = '';

const imports = {
  monad: {
    write_stdout(ptr, len) {
      stdout += new TextDecoder().decode(
        new Uint8Array(memory.buffer, Number(ptr), Number(len)),
      );
      return 0n;
    },
    write_stderr(ptr, len) {
      stderr += new TextDecoder().decode(
        new Uint8Array(memory.buffer, Number(ptr), Number(len)),
      );
      return 0n;
    },
    read_stdin() {
      return 0n;
    },
    now_ms() {
      return BigInt(Date.now());
    },
    f64_to_string(bits, ptr, max) {
      const view = new DataView(new ArrayBuffer(8));
      view.setBigUint64(0, BigInt.asUintN(64, BigInt(bits)), true);
      const bytes = new TextEncoder().encode(f64ToRustString(view.getFloat64(0, true)));
      const n = Math.min(bytes.length, Number(max));
      new Uint8Array(memory.buffer, Number(ptr), n).set(bytes.subarray(0, n));
      return BigInt(n);
    },
  },
};

const { instance } = await WebAssembly.instantiate(bytes, imports);
memory = instance.exports.memory;

if (!memory) throw new Error('missing memory export');
if (typeof instance.exports.monad_main !== 'function') {
  throw new Error('missing monad_main export');
}

const rc = instance.exports.monad_main(0n);

if (rc !== 0n) {
  console.error(`monad_main returned ${rc}; stderr=${JSON.stringify(stderr)}`);
  process.exit(1);
}
if (stdout !== expected + '\n') {
  console.error(
    `unexpected stdout: ${JSON.stringify(stdout)} (expected ${JSON.stringify(expected + '\n')})`,
  );
  process.exit(1);
}
if (stderr !== '') {
  console.error(`unexpected stderr: ${JSON.stringify(stderr)}`);
  process.exit(1);
}

console.log(`ok: ${path} -> ${JSON.stringify(stdout)} rc=0`);
