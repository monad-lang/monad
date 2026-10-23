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
    /* Boehm returns cleared memory; match it so a codegen path that reads a
       field before writing it sees the same zero on every target. */
    rt_word ptr = web_alloc(size, 1);
    if (ptr) {
        Header* h = (Header*)RT_PTR(ptr);
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return ptr;
}

rt_word monad_alloc_atomic(rt_size size) {
    return web_alloc(size, 1);
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

/* `monad_main` is only emitted for a program with a `def main`. An
   exports-only SPA (`#[export "c"]` defs and no main) is legitimate, so the
   entry reference is weak: wasm-ld resolves it to 0 and `monad_web_entry`
   returns without calling. A module WITH a main is unaffected. */
__attribute__((weak))
extern int64_t main_monad(int64_t args);

/* ── web_wasm externs (motes/web_wasm/src/ffi.mo) ───────────────────────
   The browser boundary. `motes/web_wasm` declares each of these as
   `#[extern "c" {link_name := "web_..."}]`; the JS side is
   `wasm/web/web_runtime.js` (the `host` object the generated loader
   imports), reached through one import module ("monad").

   Marshalling, both directions:
   * a Monad `String` is a NUL-terminated char* word, so a string ARGUMENT
     crosses as (ptr, len) with `strlen` done here (the loader's own strings
     come from Monad source, where an embedded NUL cannot survive anyway);
   * a string RESULT is written by JS into a buffer THIS side allocates,
     and copied into a fresh `monad_alloc_atomic` string, because successive
     calls must not alias (Monad strings are immutable values);
   * a Node/RequestId is an opaque numeric id: JS owns the table, wasm holds
     the id in a word. Nothing here dereferences it. */

__attribute__((import_module("monad"), import_name("dom_create")))
extern int64_t monad_js_dom_create(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("dom_create_text")))
extern int64_t monad_js_dom_create_text(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("dom_create_comment")))
extern int64_t monad_js_dom_create_comment(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("dom_root")))
extern int64_t monad_js_dom_root(void);

__attribute__((import_module("monad"), import_name("dom_append")))
extern int64_t monad_js_dom_append(int64_t parent, int64_t child);

__attribute__((import_module("monad"), import_name("dom_insert_before")))
extern int64_t monad_js_dom_insert_before(int64_t parent, int64_t child, int64_t before);

__attribute__((import_module("monad"), import_name("dom_remove")))
extern int64_t monad_js_dom_remove(int64_t node);

__attribute__((import_module("monad"), import_name("dom_replace")))
extern int64_t monad_js_dom_replace(int64_t old_node, int64_t new_node);

__attribute__((import_module("monad"), import_name("dom_set_attr")))
extern int64_t monad_js_dom_set_attr(int64_t node, int64_t kptr, int64_t klen,
                                     int64_t vptr, int64_t vlen);

__attribute__((import_module("monad"), import_name("dom_remove_attr")))
extern int64_t monad_js_dom_remove_attr(int64_t node, int64_t kptr, int64_t klen);

__attribute__((import_module("monad"), import_name("dom_set_text")))
extern int64_t monad_js_dom_set_text(int64_t node, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("dom_add_listener")))
extern int64_t monad_js_dom_add_listener(int64_t node, int64_t eptr, int64_t elen,
                                         int64_t handler);

__attribute__((import_module("monad"), import_name("dom_child")))
extern int64_t monad_js_dom_child(int64_t node, int64_t index);

__attribute__((import_module("monad"), import_name("fetch_begin")))
extern int64_t monad_js_fetch_begin(int64_t uptr, int64_t ulen, int64_t method,
                                    int64_t bptr, int64_t blen);

__attribute__((import_module("monad"), import_name("fetch_poll")))
extern int64_t monad_js_fetch_poll(int64_t request);

__attribute__((import_module("monad"), import_name("fetch_status")))
extern int64_t monad_js_fetch_status(int64_t request);

__attribute__((import_module("monad"), import_name("fetch_read")))
extern int64_t monad_js_fetch_read(int64_t request, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("storage_get_raw")))
extern int64_t monad_js_storage_get(int64_t kptr, int64_t klen, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("storage_set")))
extern int64_t monad_js_storage_set(int64_t kptr, int64_t klen, int64_t vptr, int64_t vlen);

__attribute__((import_module("monad"), import_name("console_log")))
extern int64_t monad_js_console_log(int64_t ptr, int64_t len);

/* A result string can be at most this long; `storage_get_raw` has no
   length channel, and a longer value is truncated rather than overrunning
   the scratch buffer. `fetch_read` takes its cap from the caller. */
#define WEB_SCRATCH_BYTES 65536
static char web_scratch[WEB_SCRATCH_BYTES];

static int64_t web_str_len(const char* p) {
    return p ? (int64_t)strlen(p) : 0;
}

static int64_t web_str_ptr(const char* p) {
    return (int64_t)(intptr_t)p;
}

/* `buf[0..n)` -> a fresh NUL-terminated Monad string. A Monad `String`
   crosses the FFI as `i8*`, so this returns `char*`, not a word. */
static char* web_take_str(const char* buf, int64_t n) {
    if (n < 0) n = 0;
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)(n + 1)));
    if (!out) return 0;
    if (n > 0) memcpy(out, buf, (size_t)n);
    out[n] = '\0';
    return out;
}

/* A `Node`/`RequestId` is an inductive value: an i64 word in codegen.
   A `Unit` result is a word too (the constructor). Only `String` is a
   pointer, and only in the `web_fetch_read`/`web_storage_get_raw`
   returns above. */

int64_t web_dom_create(const char* tag) {
    return monad_js_dom_create(web_str_ptr(tag), web_str_len(tag));
}

int64_t web_dom_create_text(const char* text) {
    return monad_js_dom_create_text(web_str_ptr(text), web_str_len(text));
}

int64_t web_dom_create_comment(const char* text) {
    return monad_js_dom_create_comment(web_str_ptr(text), web_str_len(text));
}

int64_t web_dom_root(void) {
    return monad_js_dom_root();
}

int64_t web_dom_append(int64_t parent, int64_t child) {
    return monad_js_dom_append(parent, child);
}

int64_t web_dom_insert_before(int64_t parent, int64_t child, int64_t before) {
    return monad_js_dom_insert_before(parent, child, before);
}

int64_t web_dom_remove(int64_t node) {
    return monad_js_dom_remove(node);
}

int64_t web_dom_replace(int64_t old_node, int64_t new_node) {
    return monad_js_dom_replace(old_node, new_node);
}

int64_t web_dom_set_attr(int64_t node, const char* key, const char* value) {
    return monad_js_dom_set_attr(node, web_str_ptr(key), web_str_len(key),
                                 web_str_ptr(value), web_str_len(value));
}

int64_t web_dom_remove_attr(int64_t node, const char* key) {
    return monad_js_dom_remove_attr(node, web_str_ptr(key), web_str_len(key));
}

int64_t web_dom_set_text(int64_t node, const char* text) {
    return monad_js_dom_set_text(node, web_str_ptr(text), web_str_len(text));
}

int64_t web_dom_add_listener(int64_t node, const char* event, int64_t handler) {
    return monad_js_dom_add_listener(node, web_str_ptr(event), web_str_len(event), handler);
}

int64_t web_dom_child(int64_t node, int64_t index) {
    return monad_js_dom_child(node, index);
}

int64_t web_fetch_begin(const char* url, int64_t method, const char* body) {
    return monad_js_fetch_begin(web_str_ptr(url), web_str_len(url), method,
                                web_str_ptr(body), web_str_len(body));
}

int64_t web_fetch_poll(int64_t request) {
    return monad_js_fetch_poll(request);
}

int64_t web_fetch_status(int64_t request) {
    return monad_js_fetch_status(request);
}

char* web_fetch_read(int64_t request, int64_t max) {
    if (max <= 0) return web_take_str("", 0);
    if (max > WEB_SCRATCH_BYTES) max = WEB_SCRATCH_BYTES;
    int64_t n = monad_js_fetch_read(request, (int64_t)(intptr_t)web_scratch, max);
    return web_take_str(web_scratch, n);
}

int64_t web_now_ms(void) {
    return monad_js_now_ms();
}

char* web_storage_get_raw(const char* key) {
    int64_t n = monad_js_storage_get(web_str_ptr(key), web_str_len(key),
                                     (int64_t)(intptr_t)web_scratch,
                                     WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_storage_set(const char* key, const char* value) {
    return monad_js_storage_set(web_str_ptr(key), web_str_len(key),
                                web_str_ptr(value), web_str_len(value));
}

int64_t web_console_log(const char* s) {
    return monad_js_console_log(web_str_ptr(s), web_str_len(s));
}

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

/* `stream_read_line : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) (Option String))` -- one line WITHOUT its newline, or
   `Option.none` at end of stream and for a discarded partial line. A C
   loop over one-byte stdin reads, so no stack growth and no carry; a
   read failure reads as end of stream, like the natives above. */
rt_word monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard) {
    (void)fd;
    size_t cap = 256, len = 0;
    /* Bump allocator, no free: the old buffer is abandoned when the line
       grows, the same leak discipline every allocation in this profile
       has (there is no libc malloc here). */
    char* buf = (char*)RT_PTR(monad_alloc_atomic((rt_size)cap));
    if (!buf) return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    int eof = 0;
    for (;;) {
        char c = '\0';
        int64_t r = monad_js_read_stdin((int64_t)(intptr_t)&c, 1);
        if (r <= 0) { eof = 1; break; }
        if (c == '\n') break;
        if (max_len > 0 && (int64_t)len >= max_len) {
            return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
        }
        if (len + 1 >= cap) {
            size_t want = cap * 2;
            char* grown = (char*)RT_PTR(monad_alloc_atomic((rt_size)want));
            if (!grown) return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
            memcpy(grown, buf, len);
            buf = grown;
            cap = want;
        }
        buf[len++] = c;
    }
    if (eof && (discard || len == 0)) {
        return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    }
    char* copy = (char*)RT_PTR(monad_alloc_atomic((rt_size)(len + 1)));
    if (!copy) return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    memcpy(copy, buf, len);
    copy[len] = '\0';
    Constructor* some = (Constructor*)RT_PTR(alloc_constructor(4, 1));
    if (some) some->fields[0] = RT_FIELD(RT_WORD(copy));
    return wasm_ok(RT_WORD(some));
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
    /* Exports-only module: no `def main` was compiled, so the weak
       reference is 0 and there is nothing to run. */
    if (!main_monad) return 0;
    rt_word list = args ? (rt_word)args : alloc_constructor(5, 0);
    return (int64_t)(intptr_t)main_monad(list);
}
