/* The runtime's word ABI.
 *
 * Codegen types every Monad value, parameter and result as i64, and that is
 * what the emitted `declare` block and every call site say. On LP64 a C
 * `void*`/`char*`/`size_t` is that same 64-bit word, so the native runtime
 * keeps its pointer-typed signatures. On wasm32 a C pointer is 32 bits, and
 * wasm-ld reports a signature mismatch (and links anyway), so every
 * IR-facing function takes and returns int64_t there and converts at the
 * boundary. `rt_*` is the C type the IR sees; `RT_*` converts between it and
 * the pointer an implementation works with.
 */
#ifndef MONAD_RUNTIME_ABI_H
#define MONAD_RUNTIME_ABI_H

#include <stdint.h>
#include <stddef.h>

#if !defined(MONAD_TARGET_WASI) && !defined(MONAD_TARGET_WEB)
#define MONAD_TARGET_NATIVE 1
#endif

#if defined(MONAD_TARGET_WASI) || defined(MONAD_TARGET_WEB)
#define MONAD_TARGET_WASM 1
#endif

/* Ownership mode allocates with `calloc`/`free` and its drop glue emits
   `call void @monad_owned_free`; the wasm profiles keep the IR-facing
   declaration as i64 (`rt_void`) and have no allocator to return memory to.
   `llvm/src/link.mo` therefore turns the combination into this define, so
   the build fails with a message instead of emitting invalid IR. */
#ifdef MONAD_OWNERSHIP_UNSUPPORTED_TARGET
#error "MONAD_OWNERSHIP is native-only: the wasm profiles have no allocator to free to"
#endif

#ifdef MONAD_TARGET_WASM
/* Every wasm-facing boundary is exactly the i64 the IR declares. */
typedef int64_t rt_word;   /* any pointer-valued codegen word */
typedef int64_t rt_str;    /* a String value (raw char* in a word) */
typedef int64_t rt_size;
typedef int64_t rt_void;   /* the four natives the IR types i64 but C calls void */
typedef int64_t rt_refcount;  /* no atomics, no libatomic, no threads */
/* A Constructor field / closure env slot. Monad values are always i64
   words, so the slot is 8 bytes on wasm; native `void*` is already 8. */
typedef int64_t rt_field;
/* An i64 scalar or pointer word <-> one field slot. */
#define RT_FIELD(v) ((int64_t)(v))
#define RT_VALUE(f) ((int64_t)(f))
/* Pointer -> the function's own return type: the i64 word on wasm. */
#define RT_WORD(p) ((int64_t)(intptr_t)(p))
#define RT_STR_WORD(p) ((int64_t)(intptr_t)(p))
#define RT_NULL 0
#define RT_VOID_RETURN return 0

/* Freestanding web profile has no libc headers; platform_web.c defines
   these, but core code above it needs the declarations. */
#ifdef MONAD_TARGET_WEB
void* memcpy(void* dst, const void* src, size_t n);
void* memmove(void* dst, const void* src, size_t n);
void* memset(void* dst, int c, size_t n);
void* memchr(const void* s, int c, size_t n);
int memcmp(const void* a, const void* b, size_t n);
size_t strlen(const char* s);
int strcmp(const char* a, const char* b);
#endif
#else
typedef void* rt_word;
typedef char* rt_str;
typedef size_t rt_size;
typedef void rt_void;
typedef _Atomic(int64_t) rt_refcount;
typedef void* rt_field;
#define RT_FIELD(v) ((void*)(intptr_t)(v))
#define RT_VALUE(f) ((int64_t)(intptr_t)(f))
/* Pointer -> the function's own return type. Native keeps the pointer
   type (`void*` or `char*`); wasm returns the i64 word. */
#define RT_WORD(p) ((rt_word)(p))
#define RT_STR_WORD(p) ((rt_str)(p))
#define RT_NULL NULL
#define RT_VOID_RETURN return
#endif

/* Word <-> pointer conversions accept either an integer word or a pointer
   on both targets; the target differs only in the width. */
#define RT_PTR(w) ((void*)(intptr_t)(w))
#define RT_STR(w) ((char*)(intptr_t)(w))

/* Defined by the platform block (Boehm, wasi-libc malloc, or the web bump
   allocator) and called from the portable core. */
rt_word monad_alloc(rt_size size);
rt_word monad_alloc_atomic(rt_size size);
void monad_retain(rt_word ptr);
void monad_release(rt_word ptr);

/* Ownership / region split (ownership-regions-memory O3/O4).
 *
 * `monad_region_alloc[_atomic]` are the Region halves: values that may be
 * shared, cyclic or Copy, and must never be freed individually. In this
 * phase they forward to the platform allocator exactly as before, so the
 * split is a naming boundary, not a behaviour change.
 *
 * `monad_owned_alloc`/`monad_owned_free` are the Owned halves. Default
 * builds forward to `monad_alloc` and a no-op (the block is GC-owned, and
 * `free()` on it would corrupt the collector's heap). Under
 * `-DMONAD_OWNERSHIP` they are `calloc`/`free`; under
 * `-DMONAD_OWNERSHIP_POISON` the free poisons the allocation and never
 * frees, so a use-after-free is deterministic during bring-up. Ownership
 * mode is native-only: `llvm/src/link.mo` refuses it for wasm/web, and the
 * wasi/web blocks below forward so the runtime still compiles. */
rt_word monad_owned_alloc(rt_size size);
void monad_owned_free(rt_word ptr);
rt_word monad_region_alloc(rt_size size);
rt_word monad_region_alloc_atomic(rt_size size);

/* Per-kind allocation counters (ownership-regions-memory O-M0; print with
   MONAD_ALLOC_STATS=1). Native only: wasi/web compile the call sites away
   (MONAD_STAT is a no-op) because they have no getenv/atexit contract, and
   the counters would be process-local numbers nobody can print. The note
   function is a branch on a startup flag, so the instrumentation is inert
   when the variable is unset. */
enum MonadAllocKind {
    MONAD_STAT_CTOR = 0,
    MONAD_STAT_CLOSURE,
    MONAD_STAT_ARRAY,
    MONAD_STAT_REF,
    MONAD_STAT_BYTEBUF,
    MONAD_STAT_ATOMIC,
    MONAD_STAT_SCANNED,
    /* Appended after the original kinds so their indices stay stable:
       `owned-constructors` counts every `alloc_constructor_owned`, and
       `owned-frees` every `monad_owned_free` call. Under
       MONAD_OWNERSHIP=1 the two must balance for a program whose Owned
       values are all dropped; under poison every free still counts even
       though nothing is actually returned to the allocator. */
    MONAD_STAT_OWNED_CTOR,
    MONAD_STAT_OWNED_FREE,
    MONAD_STAT_KIND_COUNT,
};
#ifdef MONAD_TARGET_NATIVE
void monad_alloc_stats_note(int kind, rt_size bytes);
#define MONAD_STAT(kind, bytes) monad_alloc_stats_note((int)(kind), (rt_size)(bytes))
#else
#define MONAD_STAT(kind, bytes) ((void)0)
#endif

/* Cooperative cancellation (async-threading S1).
 *
 * Every IO bind is a potential cancellation point: `monad_io_bind` checks
 * the running fiber's `cancelled` flag and, when it is set, returns
 * MONAD_CANCELLED_SENTINEL without applying the continuation. Enclosing
 * binds propagate the sentinel unchanged, so the rest of the do-block
 * (side effects included) never runs. Only fiber answers interpret it:
 * the flag that caused it is also what makes await/poll say `err
 * cancelled`, so the sentinel never escapes to user code.
 *
 * The sentinel is a word no pointer and no constructor can have (it is
 * INT64_MIN); the fiber trampoline publishes the flag's address here. A
 * NULL flag means "not on a fiber" (main, the wasm profiles), where no
 * cancellation exists. */
#define MONAD_CANCELLED_SENTINEL INT64_MIN
void monad_set_cancel_flag(int64_t* flag);
int monad_fiber_cancelled(void);

/* Codegen's entry point: `main` is renamed at emit time and takes one i64
   argument (the List String). */
rt_word main_monad(rt_word args);

#endif /* MONAD_RUNTIME_ABI_H */
