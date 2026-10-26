// The /try engine's Web Worker host.
//
// The Oak UI (`try_ui.wasm`, main thread) never compiles Monad itself: it
// posts the scratchpad source here, and this worker instantiates the
// engine module (`try_engine.wasm`, 100% compiled Monad: parser, scope
// builder, typechecker, lowerer, interpreter) and calls its `try_run`
// export.
//
// THE PRELUDE IS NOT IN THE ENGINE. The real `init/src/*.mo` files are
// served under `sources/` beside the wasm, indexed by `sources.json`; this
// worker fetches them, frames their text (`sources.js`) and passes it as
// `try_run`'s first argument, so the program is checked against exactly the
// files the site ships. Fetching before `started` keeps the main thread's
// load timer covering this phase.
//
// A FRESH INSTANCE PER RUN. The web runtime's allocator is a bump
// allocator that never frees, and a run allocates the whole elaborated
// graph; reusing an instance would grow memory without bound. A fresh
// instance also isolates a stack-overflow trap, and terminating this
// worker is what Cancel does.
//
// Protocol (structured-clone only, no wasm types cross the boundary):
//   main -> worker: { type: 'run', seq: number, source: string }
//   worker -> main: { type: 'started', seq }
//                   { type: 'result', seq, status, value, typeText,
//                     error, notes, elapsedMs }
//                   { type: 'failure', seq, error }

import { encodeSources } from './sources.js';
import { imports } from './web.js';
import { host } from './web_runtime.js';

const ENGINE_URL = './try_engine.wasm';
const SOURCES_INDEX = './sources.json';
const SOURCES_ROOT = './sources/';
const STATUS = ['ok', 'parse', 'type', 'lower', 'eval', 'fuel', 'internal', 'size'];

const encoder = new TextEncoder();

// Compile once per worker; `compileStreaming` is an optimisation only, so
// a server that does not send `application/wasm` still works.
const compiled = (async () => {
  try {
    return await WebAssembly.compileStreaming(fetch(ENGINE_URL));
  } catch {
    const bytes = await (await fetch(ENGINE_URL)).arrayBuffer();
    return WebAssembly.compile(bytes);
  }
})();

async function fetchText(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`could not load ${url} (HTTP ${response.status})`);
  return response.text();
}

// The index names every served source; a malformed index is a failure with
// the file named, never a silent empty prelude.
async function loadSources() {
  const response = await fetch(SOURCES_INDEX);
  if (!response.ok) throw new Error(`could not load ${SOURCES_INDEX} (HTTP ${response.status})`);
  let index;
  try {
    index = await response.json();
  } catch (err) {
    throw new Error(`${SOURCES_INDEX} is not valid JSON: ${err.message}`);
  }
  const modules = index && index.modules;
  if (!Array.isArray(modules) || modules.length === 0 || !modules.every((m) => typeof m === 'string')) {
    throw new Error(`${SOURCES_INDEX} must carry a non-empty "modules" array of paths`);
  }
  const entries = [];
  for (const path of modules) {
    const url = SOURCES_ROOT + path;
    entries.push({ path, source: await fetchText(url) });
  }
  return entries;
}

// Stage one NUL-terminated Monad string in the engine's memory. The
// allocator is zeroed, so the trailing NUL is already there.
function stage(instance, bytes, what) {
  const ptr = Number(instance.exports.try_alloc(BigInt(bytes.length + 1)));
  if (!ptr) throw new Error(`out of memory staging ${what}`);
  new Uint8Array(instance.exports.memory.buffer, ptr, bytes.length).set(bytes);
  return ptr;
}

async function run(source, seq) {
  const sources = await loadSources();
  const instance = await WebAssembly.instantiate(await compiled, imports);
  host.bind(instance);
  // The main thread's timer covers download+compile+fetch only; once the
  // module is up, `started` switches it to the evaluation backstop.
  postMessage({ type: 'started', seq });
  const sourcesPtr = stage(instance, encodeSources(sources), 'the prelude sources');
  const sourcePtr = stage(instance, encoder.encode(source), 'the program');
  instance.exports.try_run(BigInt(sourcesPtr), BigInt(sourcePtr));
  return host.takeTryResult();
}

onmessage = async (event) => {
  const data = event.data || {};
  if (data.type !== 'run') return;
  const started = performance.now();
  try {
    const result = await run(String(data.source ?? ''), data.seq);
    if (!result) throw new Error('the engine returned no result');
    postMessage({
      type: 'result',
      seq: data.seq,
      status: STATUS[Number(result.status)] || 'internal',
      value: result.value,
      typeText: result.type,
      error: result.error,
      notes: result.notes,
      elapsedMs: Math.round(performance.now() - started),
    });
  } catch (err) {
    postMessage({
      type: 'failure',
      seq: data.seq,
      error: String(err && err.message ? err.message : err),
      elapsedMs: Math.round(performance.now() - started),
    });
  }
};
