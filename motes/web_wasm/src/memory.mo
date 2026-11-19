/// Heap introspection for the freestanding web profile.
///
/// The heap is collected when an export returns to JS
/// (`runtime/src/gc_wasm.c`), and exhaustion traps with a diagnostic
/// (`oom`). `heap_bytes` is committed linear memory
/// (`memory.buffer.byteLength`), which never shrinks. `heap_used` is the
/// bytes live after the last collection plus everything allocated since. Only
/// code that never returns to JS (a long `main`) cannot be collected; such an
/// app can persist its state and call `Window.reload` above a threshold.

use lib::ffi {memory_heap_bytes_raw, memory_heap_used_raw}

pub def Memory.heap_bytes : IO I64 := IO.mk memory_heap_bytes_raw

pub def Memory.heap_used : IO I64 := IO.mk memory_heap_used_raw
