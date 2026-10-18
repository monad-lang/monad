/* Web platform (wasm32-unknown-unknown).
 *
 * Freestanding: no libc, no WASI imports, no GC. The heap is a bump
 * allocator over the linker's `__heap_base`, grown with
 * `memory.grow`; codegen never emits monad_release, so leaking is the same
 * discipline the native build already has. Console I/O is four JS imports
 * (module "monad"), and `monad_main` is the exported entry a direct
 * `WebAssembly.instantiate` loader calls.
 *
 * Phase 3 (the REPL bridge and `#[export "c"]`) builds on these exports;
 * this file is the interim ABI seam.
 */
#include <stdint.h>
#include <stddef.h>

/* ── freestanding string primitives ─────────────────────────────────── */

void* memcpy(void* dst, const void* src, size_t n) {
    unsigned char* d = (unsigned char*)dst;
    const unsigned char* s = (const unsigned char*)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void* memmove(void* dst, const void* src, size_t n) {
    unsigned char* d = (unsigned char*)dst;
    const unsigned char* s = (const unsigned char*)src;
    if (d < s) {
        for (size_t i = 0; i < n; i++) d[i] = s[i];
    } else if (d > s) {
        for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1];
    }
    return dst;
}

void* memset(void* dst, int c, size_t n) {
    unsigned char* d = (unsigned char*)dst;
    for (size_t i = 0; i < n; i++) d[i] = (unsigned char)c;
    return dst;
}

void* memchr(const void* s, int c, size_t n) {
    const unsigned char* p = (const unsigned char*)s;
    for (size_t i = 0; i < n; i++) {
        if (p[i] == (unsigned char)c) return (void*)(p + i);
    }
    return 0;
}

int memcmp(const void* a, const void* b, size_t n) {
    const unsigned char* x = (const unsigned char*)a;
    const unsigned char* y = (const unsigned char*)b;
    for (size_t i = 0; i < n; i++) {
        if (x[i] != y[i]) return (int)x[i] - (int)y[i];
    }
    return 0;
}

size_t strlen(const char* s) {
    size_t n = 0;
    if (s) while (s[n]) n++;
    return n;
}

int strcmp(const char* a, const char* b) {
    while (*a && *a == *b) { a++; b++; }
    return (int)(unsigned char)*a - (int)(unsigned char)*b;
}

/* ── bump allocator ─────────────────────────────────────────────────── */

extern unsigned char __heap_base;
static uintptr_t web_heap = 0;

static rt_word web_alloc(rt_size size, int zero) {
    if (size < 0) return 0;
    uintptr_t base = web_heap ? web_heap : (uintptr_t)&__heap_base;
    uintptr_t p = (base + 15u) & ~(uintptr_t)15u;
    uintptr_t end = p + (uintptr_t)size;
    uintptr_t have = __builtin_wasm_memory_size(0) * 65536u;
    if (end > have) {
        uintptr_t pages = (end - have + 65535u) / 65536u;
        if (__builtin_wasm_memory_grow(0, pages) == (size_t)-1) return 0;
    }
    web_heap = end;
    if (zero && size) memset((void*)p, 0, (size_t)size);
    return (rt_word)p;
}

rt_word monad_alloc(rt_size size) {
    rt_word ptr = web_alloc(size, 0);
    if (ptr) {
        Header* h = (Header*)RT_PTR(ptr);
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return ptr;
}

rt_word monad_alloc_atomic(rt_size size) {
    return web_alloc(size, 0);
}

void monad_retain(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    h->refcount += 1;
}

void monad_release(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    h->refcount -= 1;
}

/* ── JS imports ─────────────────────────────────────────────────────── */

__attribute__((import_module("monad"), import_name("write_stdout")))
extern int64_t monad_js_write_stdout(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("write_stderr")))
extern int64_t monad_js_write_stderr(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("read_stdin")))
extern int64_t monad_js_read_stdin(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("now_ms")))
extern int64_t monad_js_now_ms(void);

rt_void monad_print_str(rt_str s) {
    const char* str = RT_STR(s);
    if (str) {
        int64_t len = (int64_t)strlen(str);
        monad_js_write_stdout((int64_t)(intptr_t)str, len);
        monad_js_write_stdout((int64_t)(intptr_t)"\n", 1);
    }
    RT_VOID_RETURN;
}

int64_t monad_current_time(void) {
    return monad_js_now_ms();
}

int64_t monad_current_time_nano(void) {
    return monad_js_now_ms() * 1000000;
}

rt_str monad_read_stdin_exact(int64_t n) {
    if (n <= 0) {
        char* empty = (char*)RT_PTR(monad_alloc_atomic(1));
        if (empty) empty[0] = '\0';
        return RT_WORD(empty);
    }
    char* buf = (char*)RT_PTR(monad_alloc_atomic((rt_size)(n + 1)));
    if (!buf) return 0;
    int64_t got = monad_js_read_stdin((int64_t)(intptr_t)buf, n);
    if (got < 0) got = 0;
    if (got > n) got = n;
    buf[got] = '\0';
    return RT_WORD(buf);
}

rt_word monad_flush_stdout(void) {
    return alloc_constructor(0, 0);
}

/* ── byte streams over fds 0/1/2 ────────────────────────────────────── */
static rt_word wasm_ok(rt_word payload) {
    Constructor* ok = (Constructor*)RT_PTR(alloc_constructor(10, 1));
    if (ok) ok->fields[0] = RT_FIELD(payload);
    return RT_WORD(ok);
}

rt_word monad_stream_write(int64_t fd, rt_word bufw) {
    BufObj* obj = (BufObj*)RT_PTR(bufw);
    int64_t n = obj ? obj->len : 0;
    int64_t ptr = obj ? (int64_t)(intptr_t)obj->payload : 0;
    if (fd == 1) monad_js_write_stdout(ptr, n);
    else if (fd == 2) monad_js_write_stderr(ptr, n);
    return wasm_ok((rt_word)n);
}

rt_word monad_stream_read(int64_t fd, int64_t max_bytes) {
    (void)fd;
    if (max_bytes <= 0) return wasm_ok(RT_WORD(bytebuf_new(0)));
    BufObj* obj = bytebuf_new(max_bytes);
    if (!obj) return wasm_ok(0);
    int64_t got = monad_js_read_stdin((int64_t)(intptr_t)obj->payload, max_bytes);
    if (got < 0) got = 0;
    if (got > max_bytes) got = max_bytes;
    obj->len = got;
    return wasm_ok(RT_WORD(obj));
}

rt_word monad_stream_close(int64_t fd) {
    (void)fd;
    return alloc_constructor(0, 0);
}

int64_t monad_stream_fd(int64_t fd) {
    return fd;
}

int64_t monad_std_fd(int64_t which) {
    return which;
}

/* ── integer formatting without snprintf ────────────────────────────── */

static rt_str web_unsigned_to_string(uint64_t n, int negative) {
    char buf[32];
    int i = 0;
    if (n == 0) buf[i++] = '0';
    while (n > 0) {
        buf[i++] = (char)('0' + (int)(n % 10u));
        n /= 10u;
    }
    if (negative) buf[i++] = '-';
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)(i + 1)));
    if (!out) return 0;
    for (int k = 0; k < i; k++) out[k] = buf[i - 1 - k];
    out[i] = '\0';
    return RT_WORD(out);
}

rt_str monad_i64_to_string(int64_t n) {
    if (n < 0) return web_unsigned_to_string((uint64_t)(-(n + 1)) + 1u, 1);
    return web_unsigned_to_string((uint64_t)n, 0);
}

rt_str monad_i32_to_string(int64_t n) {
    return monad_i64_to_string((int64_t)(int32_t)n);
}

rt_str monad_u8_to_string(int64_t n) {
    return web_unsigned_to_string((uint64_t)(uint8_t)n, 0);
}

rt_str monad_u16_to_string(int64_t n) {
    return web_unsigned_to_string((uint64_t)(uint16_t)n, 0);
}

rt_str monad_u64_to_string(int64_t n) {
    return web_unsigned_to_string((uint64_t)n, 0);
}

/* ── entry point ────────────────────────────────────────────────────── */

__attribute__((export_name("monad_main")))
int64_t monad_web_entry(int64_t args) {
    rt_word list = args ? (rt_word)args : alloc_constructor(5, 0);
    return (int64_t)(intptr_t)main_monad(list);
}
