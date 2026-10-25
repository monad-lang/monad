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

/* Codegen's entry point: `main` is renamed at emit time and takes one i64
   argument (the List String). */
rt_word main_monad(rt_word args);

#endif /* MONAD_RUNTIME_ABI_H */
