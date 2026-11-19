#!/usr/bin/env node
// Ownership drop glue on the web profile. Usage:
//   node wasm/web/smoke/ownership_smoke.mjs <ownership_web.wasm> <owned|none>
//
// Calls fixtures/wasm/ownership_web.mo's `own_run 1000` (3 Owned cells per
// iteration) and reads the runtime's owned counters. `owned` (a
// MONAD_OWNERSHIP=1 or =poison build) requires allocations == frees > 0;
// `none` (a default build) requires both to be 0.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, fail } from './stub_dom.mjs';

const [path, mode] = process.argv.slice(2);
if (!path || !['owned', 'none'].includes(mode)) {
  console.error('usage: node wasm/web/smoke/ownership_smoke.mjs <module.wasm> <owned|none>');
  process.exit(2);
}

installDocument();
const { instance } = await WebAssembly.instantiate(await readFile(path), imports);
host.bind(instance);
const ex = instance.exports;
const n = 1000;
const got = ex.own_run(BigInt(n));
if (got !== BigInt(n * 47)) fail(`own_run(${n}) = ${got}, want ${n * 47}`);
const allocs = Number(ex.web_gc_owned_allocs());
const frees = Number(ex.web_gc_owned_frees());
if (mode === 'owned') {
  if (allocs === 0) fail('no owned allocations: drop glue is not in this build');
  if (allocs !== frees) fail(`owned allocations ${allocs} != frees ${frees}`);
} else if (allocs !== 0 || frees !== 0) {
  fail(`default build reported owned allocations ${allocs}, frees ${frees}`);
}
console.log(`ok: ${path} -> ${allocs} owned allocations, ${frees} frees`);
