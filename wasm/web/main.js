import init, { eval_term } from './monad_wasm.js';

let wasmReady = false;

async function main() {
  const status = document.getElementById('status');
  const code = document.getElementById('code');
  const lineNumbers = document.getElementById('line-numbers');
  const output = document.getElementById('output');
  const runBtn = document.getElementById('run');
  const clearBtn = document.getElementById('clear');
  
  try {
    await init();
    wasmReady = true;
    status.textContent = 'Ready';
    status.className = 'ready';
    runBtn.disabled = false;
  } catch (e) {
    status.textContent = 'Failed to load';
    status.className = 'error';
    console.error('WASM init error:', e);
    return;
  }
  
  function updateLineNumbers() {
    const lines = code.value.split('\n').length;
    lineNumbers.innerHTML = Array.from({ length: lines }, (_, i) => i + 1).join('<br>');
  }
  
  function runCode() {
    if (!wasmReady) return;
    
    const source = code.value.trim();
    if (!source) {
      output.textContent = '';
      output.className = '';
      return;
    }
    
    try {
      const result = eval_term(source);
      if (result.is_ok) {
        output.textContent = result.value;
        output.className = 'success';
      } else {
        output.textContent = result.error;
        output.className = 'error';
      }
    } catch (e) {
      output.textContent = `Error: ${e.message}`;
      output.className = 'error';
    }
  }
  
  code.addEventListener('input', updateLineNumbers);
  code.addEventListener('scroll', () => {
    lineNumbers.scrollTop = code.scrollTop;
  });
  
  code.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
      e.preventDefault();
      runCode();
    }
    if (e.key === 'Tab') {
      e.preventDefault();
      const start = code.selectionStart;
      const end = code.selectionEnd;
      code.value = code.value.substring(0, start) + '  ' + code.value.substring(end);
      code.selectionStart = code.selectionEnd = start + 2;
      updateLineNumbers();
    }
  });
  
  runBtn.addEventListener('click', runCode);
  
  clearBtn.addEventListener('click', () => {
    code.value = '';
    output.textContent = '';
    output.className = '';
    updateLineNumbers();
  });
  
  document.querySelectorAll('.example-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      const example = btn.dataset.example.replace(/\\n/g, '\n').replace(/\\t/g, '\t');
      code.value = example;
      updateLineNumbers();
      runCode();
    });
  });
  
  updateLineNumbers();
}

main();
