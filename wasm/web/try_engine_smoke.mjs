#!/usr/bin/env node
// Node smoke test for the /try engine module. Usage:
//   node wasm/web/try_engine_smoke.mjs <built-try-dir>
//
// `<dir>` is a built /try directory (the output of `scripts/build-try.sh`):
// it holds `try_engine.wasm`, `sources.json` and the `sources/` tree the
// page fetches. The prelude is NOT compiled into the engine, so the harness
// frames the served files exactly as `worker.js` does -- through the same
// `sources.js` encoder -- and passes them as `try_run`'s first argument.
//
// Drives the real export ABI (`try_alloc` + `try_run(String, String)`), the
// real `web.js` import object and the real `web_runtime.js` host. A FRESH
// INSTANCE PER CASE, exactly like the worker's per-run instance: the web
// bump allocator never frees, so one run already grows memory to ~170 MB
// (it elaborates the prelude) and reusing an instance would both accumulate
// that and eventually cross the 2 GiB pointer range.
//
// Also prints the module's imports -- the gated-native audit: the engine
// must not import `read_file`, `exec_cmd`, `get_env` or any other native
// the web profile cannot serve.

import { readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { encodeSources } from '../../docs/site/static/try/sources.js';
import { imports } from './web.js';
import { host } from './web_runtime.js';

const dir = process.argv[2];
if (!dir) {
  console.error('usage: node wasm/web/try_engine_smoke.mjs <built-try-dir>');
  process.exit(2);
}

function fail(message) {
  console.error(message);
  process.exit(1);
}

const bytes = await readFile(join(dir, 'try_engine.wasm'));
const module = new WebAssembly.Module(bytes);
const imported = WebAssembly.Module.imports(module).map((i) => `${i.module}.${i.name}`);
const exported = WebAssembly.Module.exports(module).map((e) => e.name);
for (const want of ['try_alloc', 'try_run', 'monad_main', 'memory']) {
  if (!exported.includes(want)) fail(`missing export ${want}; exports are ${exported.join(', ')}`);
}
for (const banned of ['read_file', 'exec_cmd', 'get_env', 'file_exists', 'list_dir', 'is_dir']) {
  if (imported.some((n) => n.endsWith(`.${banned}`))) {
    fail(`the engine imports the gated native ${banned}; the pure pipeline reached it`);
  }
}

// The served sources, framed exactly as the worker frames them.
async function loadSources() {
  const index = JSON.parse(await readFile(join(dir, 'sources.json'), 'utf8'));
  if (!Array.isArray(index.modules) || index.modules.length === 0) {
    fail(`sources.json has no modules: ${JSON.stringify(index)}`);
  }
  const entries = [];
  for (const path of index.modules) {
    entries.push({ path, source: await readFile(join(dir, 'sources', path), 'utf8') });
  }
  return entries;
}

const encoder = new TextEncoder();
const payload = encodeSources(await loadSources());

function stage(instance, payload, what) {
  const ptr = Number(instance.exports.try_alloc(BigInt(payload.length + 1)));
  if (!ptr) fail(`try_alloc returned 0 for ${what}`);
  new Uint8Array(instance.exports.memory.buffer, ptr, payload.length).set(payload);
  return ptr;
}

async function runWith(payloadBytes, source) {
  const instance = await WebAssembly.instantiate(module, imports);
  host.bind(instance);
  const sourcesPtr = stage(instance, payloadBytes, 'the prelude sources');
  const sourcePtr = stage(instance, encoder.encode(source), 'the program');
  instance.exports.try_run(BigInt(sourcesPtr), BigInt(sourcePtr));
  const result = host.takeTryResult();
  if (!result) fail(`no result pushed for ${JSON.stringify(source)}`);
  return result;
}

const run = (source) => runWith(payload, source);

async function expect(source, status, value, typeText) {
  const r = await run(source);
  if (r.status !== status) fail(`${JSON.stringify(source)} gave status ${r.status}, expected ${status} (error: ${r.error})`);
  if (value !== null && r.value !== value) fail(`${JSON.stringify(source)} gave value ${JSON.stringify(r.value)}, expected ${JSON.stringify(value)}`);
  if (typeText !== null && r.type !== typeText) fail(`${JSON.stringify(source)} gave type ${JSON.stringify(r.type)}, expected ${JSON.stringify(typeText)}`);
  return r;
}

await expect('def main : I64 := 2 + 3\n', 0, '5', 'I64');
await expect('def square (n : I64) : I64 := I64.mul n n\n\ndef main : I64 := square 12\n', 0, '144', 'I64');
await expect('def main : String := String.concat "Hello, " "Monad!"\n', 0, '"Hello, Monad!"', 'String');
await expect('def main : List I64 := List.map (fn (x : I64) => I64.mul x 2) [1, 2, 3]\n', 0, '[2, 4, 6]', '(List I64)');
await expect('def main : String := I64.to_string (I64.div 7 2)\n', 0, '"3"', 'String');
await expect('def describe (o : Option I64) : String :=\n    match o { some x => "some", none => "none" }\n\ndef main : String := describe (Option.some 3)\n', 0, '"some"', 'String');

// A module that was never part of the old embedded nine: the served tree is
// all of init/src, so the page can reach beyond the prelude closure.
await expect('use init::foldable {}\n\ndef main : I64 := 7\n', 0, '7', 'I64');

// Native fixes from review: explicit-length string primitives, a
// zero-arity native as a value, and MIN / -1.
await expect('def main : I64 := String.count_newlines "a\\nb\\nc" 2\n', 0, '1', 'I64');
await expect('def main : Ptr := Ptr.null\n', 0, '0', 'Ptr');
await expect('def main : I64 := I64.div (I64.sub (I64.sub 0 9223372036854775807) 1) (0 - 1)\n', 0, '-9223372036854775808', 'I64');

// Ordinary recursion works; past 200 nested calls the depth counter stops
// cleanly instead of trapping the wasm stack.
const sumSource = (n) =>
  `#[terminating]\ndef sum (n : I64) : I64 := if I64.beq n 0 then 0 else I64.add n (sum (I64.sub n 1))\n\ndef main : I64 := sum ${n}\n`;
await expect(sumSource(100), 0, '5050', 'I64');
const deep = await run(sumSource(300));
if (deep.status !== 4 || !deep.error.includes('recursed')) {
  fail(`deep recursion gave ${deep.status}/${JSON.stringify(deep.error)}, expected a depth error`);
}

await expect('def main : I64 := 2 +\n', 1, '', null);
await expect('def main : I64 := totally_unknown\n', 2, '', null);
// A mistyped native argument is now a TYPECHECK failure: main's stricter
// call checking rejects `I64.mul "a" "b"` before lowering. The eval-stage
// (status 4) path is covered by the deep-recursion case above.
await expect('def main : I64 := I64.mul "a" "b"\n', 2, '', null);
await expect('def main : F64 := 1.5\n', 3, '', null);
await expect('def helper : I64 := 1\n', 2, '', null);

const fuel = await run('def main : I64 := I64.div 1 0\n');
if (fuel.status !== 0 || fuel.value !== '0') fail(`guarded division gave ${fuel.status}/${fuel.value}`);

// A page that serves no sources, or a payload that is not in the record
// format, is a load failure with the reason -- never a silent empty run.
const noSources = await runWith(encodeSources([]), 'def main : I64 := 1\n');
if (noSources.status !== 2 || !noSources.error.includes('unresolved module: prelude')) {
  fail(`an empty source tree gave ${noSources.status}/${JSON.stringify(noSources.error)}`);
}
const garbage = await runWith(encoder.encode('not a header'), 'def main : I64 := 1\n');
if (garbage.status !== 2 || !garbage.error.includes('could not be read')) {
  fail(`a malformed payload gave ${garbage.status}/${JSON.stringify(garbage.error)}`);
}

console.log(`ok: ${dir} -> /try engine evaluates programs against the served prelude`);
console.log(`imports: ${imported.join(', ')}`);
console.log(`exports: ${exported.join(', ')}`);
