// Direct WebAssembly loader for a compiled Monad module.
//
// No wasm-bindgen, no Rust glue: the module is instantiated with the four
// imports its runtime declares (module "monad"), and JS calls the exported
// `monad_main` entry. The Phase 3 workbench REPL replaces this page with a
// session-aware loader over the same ABI.
//
// Pick a module with `?wasm=./path/to/app.wasm`; the default is ./app.wasm.
//
// Verification modes, used by the browser proof and safe to ignore:
//   ?autorun=1  load synchronously and run as soon as the page loads, so a
//               headless screenshot sees the finished result. Synchronous
//               XHR + `new WebAssembly.Module/Instance` are used only here;
//               the default path stays async.
//   ?render=1   put the program's stdout (a full HTML document) into the
//               iframe's srcdoc, so a page-generating program is rendered
//               rather than shown as text.

const params = new URLSearchParams(window.location.search);
const wasmUrl = params.get('wasm') || './app.wasm';
const autorun = params.get('autorun') === '1';
const renderMode = params.get('render') === '1';

const status = document.getElementById('status');
const output = document.getElementById('output');
const runBtn = document.getElementById('run');
const clearBtn = document.getElementById('clear');
const code = document.getElementById('code');
const renderContainer = document.getElementById('render-container');
const renderFrame = document.getElementById('render');

let instance = null;

function memoryBytes(memory, ptr, len) {
  // Re-read the buffer on every call: memory.grow detaches the old one.
  return new Uint8Array(memory.buffer, Number(ptr), Number(len));
}

function decoder() {
  return new TextDecoder('utf-8');
}

function append(bytes, isError) {
  const text = decoder().decode(bytes);
  output.textContent += text;
  output.className = isError ? 'error' : 'success';
}

function importObject(memoryRef) {
  return {
    monad: {
      write_stdout(ptr, len) {
        append(memoryBytes(memoryRef(), ptr, len), false);
        return 0n;
      },
      write_stderr(ptr, len) {
        append(memoryBytes(memoryRef(), ptr, len), true);
        return 0n;
      },
      read_stdin(_ptr, _max) {
        // The Phase 2 fixtures do not read input; EOF.
        return 0n;
      },
      now_ms() {
        return BigInt(Date.now());
      },
    },
  };
}

function markReady() {
  status.textContent = 'Ready';
  status.className = 'ready';
  runBtn.disabled = false;
  if (code) {
    code.value = `compiled module: ${wasmUrl}`;
    code.readOnly = true;
  }
  if (autorun) run();
}

function fail(e) {
  status.textContent = `Failed to load: ${e.message}`;
  status.className = 'error';
  console.error(e);
}

function checkExports() {
  if (!instance.exports.memory) throw new Error('module does not export memory');
  if (typeof instance.exports.monad_main !== 'function') {
    throw new Error('module does not export monad_main');
  }
}

function loadSync() {
  status.textContent = 'Loading…';
  status.className = '';
  const request = new XMLHttpRequest();
  request.open('GET', wasmUrl, false);
  // Synchronous XHR cannot set responseType; x-user-defined maps each byte
  // to U+00XX, so responseText can be turned back into bytes.
  request.overrideMimeType('text/plain; charset=x-user-defined');
  request.send(null);
  if (request.status !== 0 && (request.status < 200 || request.status >= 300)) {
    throw new Error(`${request.status} ${request.statusText}`);
  }
  const text = request.responseText;
  const bytes = new Uint8Array(text.length);
  for (let i = 0; i < text.length; i++) bytes[i] = text.charCodeAt(i) & 0xff;
  let memory = null;
  const imports = importObject(() => memory);
  const module = new WebAssembly.Module(bytes);
  instance = new WebAssembly.Instance(module, imports);
  memory = instance.exports.memory;
  checkExports();
  markReady();
}

async function loadAsync() {
  try {
    status.textContent = 'Loading…';
    status.className = '';
    const response = await fetch(wasmUrl);
    if (!response.ok) throw new Error(`${response.status} ${response.statusText}`);
    const bytes = await response.arrayBuffer();

    let memory = null;
    const imports = importObject(() => memory);
    const result = await WebAssembly.instantiate(bytes, imports);
    instance = result.instance;
    memory = instance.exports.memory;
    checkExports();
    markReady();
  } catch (e) {
    fail(e);
  }
}

function load() {
  if (autorun) {
    try {
      loadSync();
    } catch (e) {
      fail(e);
    }
    return;
  }
  loadAsync();
}

function applyRender() {
  if (!renderMode || !renderFrame || !renderContainer) return;
  renderFrame.srcdoc = output.textContent;
  renderFrame.hidden = false;
  renderContainer.hidden = false;
}

function run() {
  if (!instance) return;
  output.textContent = '';
  output.className = '';
  try {
    const rc = instance.exports.monad_main(0n);
    const text = Number(rc);
    if (text !== 0) output.textContent += `\n[exit ${text}]`;
  } catch (e) {
    output.textContent += `\n[trapped: ${e.message}]`;
    output.className = 'error';
  }
  applyRender();
}

runBtn.addEventListener('click', run);
clearBtn.addEventListener('click', () => {
  output.textContent = '';
  output.className = '';
});

load();
