// Direct WebAssembly loader for a compiled Monad module.
//
// No wasm-bindgen, no Rust glue: the module is instantiated with the four
// imports its runtime declares (module "monad"), and JS calls the exported
// `monad_main` entry. The Phase 3 workbench REPL replaces this page with a
// session-aware loader over the same ABI.
//
// Pick a module with `?wasm=./path/to/app.wasm`; the default is ./app.wasm.

const wasmUrl = new URLSearchParams(window.location.search).get('wasm') || './app.wasm';

const status = document.getElementById('status');
const output = document.getElementById('output');
const runBtn = document.getElementById('run');
const clearBtn = document.getElementById('clear');
const code = document.getElementById('code');

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

async function load() {
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
    if (!memory) throw new Error('module does not export memory');
    if (typeof instance.exports.monad_main !== 'function') {
      throw new Error('module does not export monad_main');
    }
    status.textContent = 'Ready';
    status.className = 'ready';
    runBtn.disabled = false;
    if (code) {
      code.value = `compiled module: ${wasmUrl}`;
      code.readOnly = true;
    }
  } catch (e) {
    status.textContent = `Failed to load: ${e.message}`;
    status.className = 'error';
    console.error(e);
  }
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
}

runBtn.addEventListener('click', run);
clearBtn.addEventListener('click', () => {
  output.textContent = '';
  output.className = '';
});

load();
