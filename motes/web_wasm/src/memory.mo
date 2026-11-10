/// Heap introspection for the freestanding web profile.
///
/// The allocator is a bump allocator: it never frees, and exhaustion now
/// traps with a diagnostic (`oom`). `heap_bytes` is committed linear memory
/// (`memory.buffer.byteLength`), `heap_used` is the bump pointer minus the
/// heap base. An app that cannot shed allocations can persist its state and
/// call `Window.reload` above a threshold.

use lib::ffi {memory_heap_bytes_raw, memory_heap_used_raw}

pub def Memory.heap_bytes : IO I64 := IO.mk memory_heap_bytes_raw

pub def Memory.heap_used : IO I64 := IO.mk memory_heap_used_raw
