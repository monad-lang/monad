/* Web platform (wasm32-unknown-unknown).
 *
 * Freestanding: no libc, no WASI imports. The heap is gc_wasm.c's
 * conservative mark-sweep over linear memory above `__heap_base`. It
 * collects only when the export depth returns to 0
 * (`monad_export_leave`), because a running frame's wasm locals are
 * invisible to a scan. Console I/O is four JS imports
 * (module "monad"), plus `f64_to_string` for a program that formats a
 * float (`F64.to_string`), and `monad_main` is the exported entry a direct
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

/* ── heap: conservative mark-sweep (gc_wasm.c) ──────────────────────── */

/* Heap exhaustion is a trap with a diagnostic, never a silent 0: a 0 word
   is not a valid constructor pointer, and returning one turns the failure
   into a negative-offset RangeError in the JS host (anidoku's 2 GB wall).
   The import is declared here, ahead of the import block below, because
   the allocator is its only caller. */
__attribute__((import_module("monad"), import_name("oom")))
extern int64_t monad_js_oom(int64_t want, int64_t have);

static void web_oom(uint64_t want, uint64_t have) {
    monad_js_oom((int64_t)want, (int64_t)have);
    __builtin_trap();
}

#include "gc_wasm.c"

static rt_word web_alloc(rt_size size, int noscan) {
    if (size < 0) web_oom(0, 0);
    return (rt_word)(uintptr_t)gc_alloc((uint64_t)size, noscan);
}

/* Committed and used heap, for `web_wasm::memory`. C-only exports: no JS
   import, so they do not appear in `WebAbi`. `used` is the live bytes
   after the last collection plus everything allocated since. */
int64_t web_memory_heap_bytes(void) {
    return (int64_t)gc_heap_committed();
}

int64_t web_memory_heap_used(void) {
    return (int64_t)gc_heap_used();
}

/* Collector counters for the smoke harnesses; C-only exports. */
__attribute__((export_name("web_gc_collections")))
int64_t web_gc_collections(void) {
    return gc.collections;
}

__attribute__((export_name("web_gc_live_bytes")))
int64_t web_gc_live_bytes(void) {
    return (int64_t)gc.live_bytes;
}

/* Ownership-mode counters (`scripts/check-ownership.sh`'s web leg): every
   owned allocation and every drop-glue free, poison mode included. */
__attribute__((export_name("web_gc_owned_allocs")))
int64_t web_gc_owned_allocs(void) {
    return gc.owned_allocs;
}

__attribute__((export_name("web_gc_owned_frees")))
int64_t web_gc_owned_frees(void) {
    return gc.owned_frees;
}

rt_word monad_alloc(rt_size size) {
    /* Boehm returns cleared memory; match it so a codegen path that reads a
       field before writing it sees the same zero on every target. */
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
    return web_alloc(size, 1);
}

/* Ownership mode: Owned cells come from the same scanned heap, and drop
   glue returns them to it. Poison fills the cell and never frees, so a
   use-after-free is deterministic during bring-up. Default builds keep the
   no-op free: the collector reclaims the cell. */
rt_word monad_owned_alloc(rt_size size) {
    gc.owned_allocs++;
    return monad_alloc(size);
}
#if defined(MONAD_OWNERSHIP_POISON)
rt_void monad_owned_free(rt_word ptr) {
    if (!ptr) return 0;
    uint32_t page, slot;
    uint8_t* obj = gc_resolve((uint64_t)ptr, &page, &slot);
    if (!obj || (uint64_t)(uintptr_t)obj != (uint64_t)ptr) __builtin_trap();
    memset(obj, 0xDE, (size_t)gc_obj_size(obj));
    gc.owned_frees++;
    return 0;
}
#elif defined(MONAD_OWNERSHIP)
rt_void monad_owned_free(rt_word ptr) { if (ptr) gc_free((uint64_t)ptr); return 0; }
#else
rt_void monad_owned_free(rt_word ptr) { (void)ptr; return 0; }
#endif

/* The /try engine stages the source text JS wants evaluated here: JS calls
 * `try_alloc(len + 1)`, writes UTF-8 plus a NUL, then calls the module's
 * `try_run(source : String)` export with the returned Number.
 *
 * A C-only linker export with NO Monad declaration, exactly like
 * `monad_alloc`: the pointer never round-trips through Monad, so no Monad
 * code gains an address-producing primitive. It is a no-header allocation
 * (`monad_alloc_atomic`), so JS owns exactly the bytes it asked for and
 * must not read a header that is not there. Exhaustion traps (see
 * `web_oom`); it never returns 0. The i32 return is the /try staging ABI
 * (source text is small); a program whose heap crosses 2 GB must not use
 * this channel.
 *
 * Lifetime: only JS holds the block, so it survives until the next export
 * returns to depth 0 (the collector runs there). Pass it to the very next
 * export call, as the /try worker does: two `try_alloc`s, then `try_run`
 * consumes both. Allocating here never collects. */
__attribute__((export_name("try_alloc")))
int32_t try_alloc(int64_t size) {
    return (int32_t)(intptr_t)RT_PTR(monad_alloc_atomic((rt_size)size));
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

/* `F64.to_string`. The freestanding web profile has no libc float
   formatting, so the host renders the number: JS's shortest round-trip
   decimal, expanded to the positional spelling `runtime_libc.c` produces
   with snprintf/strtod. The host writes UTF-8 into the caller's buffer
   and returns the byte count (negative on failure). Declared here rather
   than beside `web_unsigned_to_string` so every JS import stays in one
   block; the wrapper below is its only user. */
__attribute__((import_module("monad"), import_name("f64_to_string")))
extern int64_t monad_js_f64_to_string(int64_t bits, int64_t ptr, int64_t max);

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

__attribute__((import_module("monad"), import_name("dom_create_svg")))
extern int64_t monad_js_dom_create_svg(int64_t ptr, int64_t len);

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
                                         int64_t sptr, int64_t slen);

__attribute__((import_module("monad"), import_name("clipboard_available")))
extern int64_t monad_js_clipboard_available(void);

__attribute__((import_module("monad"), import_name("clipboard_read_begin")))
extern int64_t monad_js_clipboard_read_begin(void);

__attribute__((import_module("monad"), import_name("clipboard_write_begin")))
extern int64_t monad_js_clipboard_write_begin(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("clipboard_poll")))
extern int64_t monad_js_clipboard_poll(int64_t op);

__attribute__((import_module("monad"), import_name("clipboard_read")))
extern int64_t monad_js_clipboard_read(int64_t op, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("clipboard_error")))
extern int64_t monad_js_clipboard_error(int64_t op, int64_t ptr, int64_t max);

/* ── WebSocket (motes/web_wasm/src/websocket.mo) ───────────────────────── */
__attribute__((import_module("monad"), import_name("ws_open")))
extern int64_t monad_js_ws_open(int64_t uptr, int64_t ulen, int64_t pptr, int64_t plen);

__attribute__((import_module("monad"), import_name("ws_state")))
extern int64_t monad_js_ws_state(int64_t id);

__attribute__((import_module("monad"), import_name("ws_peek")))
extern int64_t monad_js_ws_peek(int64_t id, int64_t which);

__attribute__((import_module("monad"), import_name("ws_read")))
extern int64_t monad_js_ws_read(int64_t id, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("ws_info")))
extern int64_t monad_js_ws_info(int64_t id, int64_t which);

__attribute__((import_module("monad"), import_name("ws_text")))
extern int64_t monad_js_ws_text(int64_t id, int64_t which, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("ws_send")))
extern int64_t monad_js_ws_send(int64_t id, int64_t ptr, int64_t len, int64_t is_binary);

__attribute__((import_module("monad"), import_name("ws_close")))
extern int64_t monad_js_ws_close(int64_t id, int64_t code, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("ws_watch")))
extern int64_t monad_js_ws_watch(int64_t id, int64_t handler);

__attribute__((import_module("monad"), import_name("ws_unwatch")))
extern int64_t monad_js_ws_unwatch(int64_t id);

__attribute__((import_module("monad"), import_name("ws_buffered")))
extern int64_t monad_js_ws_buffered(int64_t id);

__attribute__((import_module("monad"), import_name("ws_free")))
extern int64_t monad_js_ws_free(int64_t id);

/* The current-event getters. The JS host keeps the live `Event` in a slot for
   the duration of the synchronous export call; strings are written into the
   shared scratch buffer like `dom_tag_name`. `event_f64` returns a plain
   double: the Monad extern wrapper bitcasts it to the F64 word. */
__attribute__((import_module("monad"), import_name("event_i64")))
extern int64_t monad_js_event_i64(int64_t which);

__attribute__((import_module("monad"), import_name("event_f64")))
extern double monad_js_event_f64(int64_t which);

__attribute__((import_module("monad"), import_name("event_str")))
extern int64_t monad_js_event_str(int64_t which, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("event_data")))
extern int64_t monad_js_event_data(int64_t mptr, int64_t mlen, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("event_types")))
extern int64_t monad_js_event_types(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("event_files_count")))
extern int64_t monad_js_event_files_count(void);

__attribute__((import_module("monad"), import_name("event_file_i64")))
extern int64_t monad_js_event_file_i64(int64_t index, int64_t which);

__attribute__((import_module("monad"), import_name("event_file_str")))
extern int64_t monad_js_event_file_str(int64_t index, int64_t which, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("event_prevent_default")))
extern int64_t monad_js_event_prevent_default(void);

__attribute__((import_module("monad"), import_name("event_stop_propagation")))
extern int64_t monad_js_event_stop_propagation(void);

__attribute__((import_module("monad"), import_name("dom_add_listener_global")))
extern int64_t monad_js_dom_add_listener_global(int64_t target, int64_t eptr, int64_t elen,
                                                int64_t sptr, int64_t slen);

__attribute__((import_module("monad"), import_name("dom_remove_listener_global")))
extern int64_t monad_js_dom_remove_listener_global(int64_t target, int64_t eptr,
                                                   int64_t elen);

__attribute__((import_module("monad"), import_name("dom_child")))
extern int64_t monad_js_dom_child(int64_t node, int64_t index);

__attribute__((import_module("monad"), import_name("dom_child_count")))
extern int64_t monad_js_dom_child_count(int64_t node);

__attribute__((import_module("monad"), import_name("dom_node_type")))
extern int64_t monad_js_dom_node_type(int64_t node);

__attribute__((import_module("monad"), import_name("dom_in_svg")))
extern int64_t monad_js_dom_in_svg(int64_t node);

__attribute__((import_module("monad"), import_name("dom_tag_name")))
extern int64_t monad_js_dom_tag_name(int64_t node, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("dom_value")))
extern int64_t monad_js_dom_value(int64_t node, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("dom_query")))
extern int64_t monad_js_dom_query(int64_t ptr, int64_t len);

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

__attribute__((import_module("monad"), import_name("storage_has")))
extern int64_t monad_js_storage_has(int64_t kptr, int64_t klen);

__attribute__((import_module("monad"), import_name("storage_remove")))
extern int64_t monad_js_storage_remove(int64_t kptr, int64_t klen);

__attribute__((import_module("monad"), import_name("storage_clear")))
extern int64_t monad_js_storage_clear(void);

__attribute__((import_module("monad"), import_name("monotonic_ms")))
extern int64_t monad_js_monotonic_ms(void);

__attribute__((import_module("monad"), import_name("media_matches")))
extern int64_t monad_js_media_matches(int64_t qptr, int64_t qlen);

__attribute__((import_module("monad"), import_name("media_watch")))
extern int64_t monad_js_media_watch(int64_t qptr, int64_t qlen, int64_t sptr, int64_t slen);

__attribute__((import_module("monad"), import_name("media_unwatch")))
extern int64_t monad_js_media_unwatch(int64_t qptr, int64_t qlen);

__attribute__((import_module("monad"), import_name("dom_element_at")))
extern int64_t monad_js_dom_element_at(double x, double y);

__attribute__((import_module("monad"), import_name("dom_attr")))
extern int64_t monad_js_dom_attr(int64_t node, int64_t kptr, int64_t klen,
                                 int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("dom_focus")))
extern int64_t monad_js_dom_focus(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("timer_after")))
extern int64_t monad_js_timer_after(int64_t ms);

__attribute__((import_module("monad"), import_name("fetch_begin_headers")))
extern int64_t monad_js_fetch_begin_headers(int64_t uptr, int64_t ulen, int64_t method,
                                            int64_t bptr, int64_t blen,
                                            int64_t hptr, int64_t hlen);

__attribute__((import_module("monad"), import_name("fetch_headers")))
extern int64_t monad_js_fetch_headers(int64_t request, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("crypto_random_fill")))
extern int64_t monad_js_crypto_random_fill(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("crypto_sha256_begin")))
extern int64_t monad_js_crypto_sha256_begin(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("crypto_poll")))
extern int64_t monad_js_crypto_poll(int64_t op);

__attribute__((import_module("monad"), import_name("crypto_result_hex")))
extern int64_t monad_js_crypto_result_hex(int64_t op, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("window_reload")))
extern int64_t monad_js_window_reload(void);

__attribute__((import_module("monad"), import_name("window_navigate")))
extern int64_t monad_js_window_navigate(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("window_replace")))
extern int64_t monad_js_window_replace(int64_t ptr, int64_t len);

/* `location` reads: each writes into the scratch buffer and returns the byte
   count, the `storage_get_raw` convention, so no address crosses Monad code.
   `search_param` is the percent-decoding accessor an OAuth callback needs. */
__attribute__((import_module("monad"), import_name("location_origin")))
extern int64_t monad_js_location_origin(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("location_href")))
extern int64_t monad_js_location_href(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("location_pathname")))
extern int64_t monad_js_location_pathname(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("location_search")))
extern int64_t monad_js_location_search(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("location_search_param")))
extern int64_t monad_js_location_search_param(int64_t nptr, int64_t nlen,
                                              int64_t ptr, int64_t max);

/* The error name of a failed WebCrypto op, and the ECDSA keypair handle a
   generate/get produced. The key is a host-side id: the private key never
   enters wasm memory, so there is nothing here for Monad code to leak. */
__attribute__((import_module("monad"), import_name("crypto_error")))
extern int64_t monad_js_crypto_error(int64_t op, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("crypto_op_key")))
extern int64_t monad_js_crypto_op_key(int64_t op);

__attribute__((import_module("monad"), import_name("ecdsa_generate_begin")))
extern int64_t monad_js_ecdsa_generate_begin(void);

__attribute__((import_module("monad"), import_name("ecdsa_export_jwk_begin")))
extern int64_t monad_js_ecdsa_export_jwk_begin(int64_t key);

__attribute__((import_module("monad"), import_name("ecdsa_export_raw_begin")))
extern int64_t monad_js_ecdsa_export_raw_begin(int64_t key);

__attribute__((import_module("monad"), import_name("ecdsa_sign_begin")))
extern int64_t monad_js_ecdsa_sign_begin(int64_t key, int64_t ptr, int64_t len);

/* IndexedDB over a non-extractable CryptoKey. */
__attribute__((import_module("monad"), import_name("keystore_put_begin")))
extern int64_t monad_js_keystore_put_begin(int64_t sptr, int64_t slen, int64_t key);

__attribute__((import_module("monad"), import_name("keystore_get_begin")))
extern int64_t monad_js_keystore_get_begin(int64_t sptr, int64_t slen);

__attribute__((import_module("monad"), import_name("keystore_delete_begin")))
extern int64_t monad_js_keystore_delete_begin(int64_t sptr, int64_t slen);

__attribute__((import_module("monad"), import_name("console_log")))
extern int64_t monad_js_console_log(int64_t ptr, int64_t len);

/* The /try engine's result push (`motes/web_wasm/src/try_bridge.mo`):
   status plus four (ptr,len) strings. The JS host copies every string
   immediately, so the engine may drop them as soon as the call returns. */
__attribute__((import_module("monad"), import_name("try_result")))
extern int64_t monad_js_try_result(int64_t status,
                                   int64_t vp, int64_t vl,
                                   int64_t tp, int64_t tl,
                                   int64_t ep, int64_t el,
                                   int64_t np, int64_t nl);

/* The UI half of the /try worker channel (`motes/web_wasm/src/worker.mo`). */
__attribute__((import_module("monad"), import_name("worker_run")))
extern int64_t monad_js_worker_run(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("worker_poll")))
extern int64_t monad_js_worker_poll(void);

__attribute__((import_module("monad"), import_name("worker_status")))
extern int64_t monad_js_worker_status(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("worker_value")))
extern int64_t monad_js_worker_value(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("worker_type")))
extern int64_t monad_js_worker_type(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("worker_error")))
extern int64_t monad_js_worker_error(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("worker_notes")))
extern int64_t monad_js_worker_notes(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("worker_cancel")))
extern int64_t monad_js_worker_cancel(void);

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

int64_t web_dom_create_svg(const char* tag) {
    return monad_js_dom_create_svg(web_str_ptr(tag), web_str_len(tag));
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

int64_t web_dom_add_listener(int64_t node, const char* event, const char* spec) {
    return monad_js_dom_add_listener(node, web_str_ptr(event), web_str_len(event),
                                     web_str_ptr(spec), web_str_len(spec));
}

int64_t web_dom_add_listener_global(int64_t target, const char* event, const char* spec) {
    return monad_js_dom_add_listener_global(target, web_str_ptr(event), web_str_len(event),
                                            web_str_ptr(spec), web_str_len(spec));
}

int64_t web_dom_remove_listener_global(int64_t target, const char* event) {
    return monad_js_dom_remove_listener_global(target, web_str_ptr(event), web_str_len(event));
}

int64_t web_dom_child(int64_t node, int64_t index) {
    return monad_js_dom_child(node, index);
}

int64_t web_dom_child_count(int64_t node) {
    return monad_js_dom_child_count(node);
}

int64_t web_dom_node_type(int64_t node) {
    return monad_js_dom_node_type(node);
}

int64_t web_dom_in_svg(int64_t node) {
    return monad_js_dom_in_svg(node);
}

/* The host writes the tag/value UTF-8 into the shared scratch buffer and
   returns the byte count; copy out into a fresh Monad string (see
   `web_take_str`). */
char* web_dom_tag_name(int64_t node) {
    int64_t n = monad_js_dom_tag_name(node, (int64_t)(intptr_t)web_scratch,
                                      WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_dom_value(int64_t node) {
    int64_t n = monad_js_dom_value(node, (int64_t)(intptr_t)web_scratch,
                                   WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_dom_query(const char* selector) {
    return monad_js_dom_query(web_str_ptr(selector), web_str_len(selector));
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

int64_t web_storage_has(const char* key) {
    return monad_js_storage_has(web_str_ptr(key), web_str_len(key));
}

int64_t web_storage_remove(const char* key) {
    return monad_js_storage_remove(web_str_ptr(key), web_str_len(key));
}

int64_t web_storage_clear(void) {
    return monad_js_storage_clear();
}

int64_t web_monotonic_ms(void) {
    return monad_js_monotonic_ms();
}

int64_t web_media_matches(const char* query) {
    return monad_js_media_matches(web_str_ptr(query), web_str_len(query));
}

int64_t web_media_watch(const char* query, const char* spec) {
    return monad_js_media_watch(web_str_ptr(query), web_str_len(query),
                                web_str_ptr(spec), web_str_len(spec));
}

int64_t web_media_unwatch(const char* query) {
    return monad_js_media_unwatch(web_str_ptr(query), web_str_len(query));
}

int64_t web_dom_element_at(double x, double y) {
    return monad_js_dom_element_at(x, y);
}

char* web_dom_attr(int64_t node, const char* name) {
    int64_t n = monad_js_dom_attr(node, web_str_ptr(name), web_str_len(name),
                                  (int64_t)(intptr_t)web_scratch,
                                  WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_dom_focus(const char* selector) {
    return monad_js_dom_focus(web_str_ptr(selector), web_str_len(selector));
}

int64_t web_timer_after(int64_t ms) {
    return monad_js_timer_after(ms);
}

int64_t web_fetch_begin_headers(const char* url, int64_t method, const char* body,
                                const char* headers) {
    return monad_js_fetch_begin_headers(web_str_ptr(url), web_str_len(url), method,
                                        web_str_ptr(body), web_str_len(body),
                                        web_str_ptr(headers), web_str_len(headers));
}

char* web_fetch_headers(int64_t request) {
    int64_t n = monad_js_fetch_headers(request, (int64_t)(intptr_t)web_scratch,
                                       WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

/* `crypto_random_fill` fills a caller-owned `ByteBuf` in place: the typed
   buffer is the only channel, so no address-producing primitive appears on
   the Monad side. Returns 1 when random bytes were written, 0 when the host
   has no `crypto.getRandomValues`. */
int64_t web_crypto_random_fill(int64_t buf) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    if (!obj || obj->len <= 0) return 1;
    return monad_js_crypto_random_fill((int64_t)(intptr_t)obj->payload, obj->len);
}

int64_t web_crypto_sha256_begin(int64_t buf) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t len = obj ? obj->len : 0;
    const char* data = obj ? (const char*)obj->payload : "";
    return monad_js_crypto_sha256_begin((int64_t)(intptr_t)data, len);
}

int64_t web_crypto_poll(int64_t op) {
    return monad_js_crypto_poll(op);
}

char* web_crypto_result_hex(int64_t op) {
    int64_t n = monad_js_crypto_result_hex(op, (int64_t)(intptr_t)web_scratch,
                                           WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

/* ── WebSocket wrappers ────────────────────────────────────────────────── */

int64_t web_ws_open(const char* url, const char* protocols) {
    return monad_js_ws_open(web_str_ptr(url), web_str_len(url), web_str_ptr(protocols),
                            web_str_len(protocols));
}

int64_t web_ws_state(int64_t id) {
    return monad_js_ws_state(id);
}

int64_t web_ws_peek(int64_t id, int64_t which) {
    return monad_js_ws_peek(id, which);
}

/* Copies the head entry's payload into a caller-owned ByteBuf and pops it.
   Returns the entry's kind (1 open, 2 text, 3 binary, 4 close, 5 error,
   0 empty) — the same numbers `ws_peek`'s kind answers. */
int64_t web_ws_read(int64_t id, int64_t buf) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t cap = obj ? obj->len : 0;
    int64_t n = monad_js_ws_read(id, obj ? (int64_t)(intptr_t)obj->payload : 0, cap);
    return n;
}

int64_t web_ws_info(int64_t id, int64_t which) {
    return monad_js_ws_info(id, which);
}

char* web_ws_text(int64_t id, int64_t which) {
    int64_t n = monad_js_ws_text(id, which, (int64_t)(intptr_t)web_scratch,
                                 WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_ws_send(int64_t id, int64_t buf, int64_t is_binary) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t len = obj ? obj->len : 0;
    const char* data = obj ? (const char*)obj->payload : "";
    return monad_js_ws_send(id, (int64_t)(intptr_t)data, len, is_binary);
}

int64_t web_ws_close(int64_t id, int64_t code, const char* reason) {
    return monad_js_ws_close(id, code, web_str_ptr(reason), web_str_len(reason));
}

int64_t web_ws_watch(int64_t id, int64_t handler) {
    return monad_js_ws_watch(id, handler);
}

int64_t web_ws_unwatch(int64_t id) {
    return monad_js_ws_unwatch(id);
}

int64_t web_ws_buffered(int64_t id) {
    return monad_js_ws_buffered(id);
}

int64_t web_ws_free(int64_t id) {
    return monad_js_ws_free(id);
}

int64_t web_window_reload(void) {
    return monad_js_window_reload();
}

int64_t web_window_navigate(const char* url) {
    return monad_js_window_navigate(web_str_ptr(url), web_str_len(url));
}

int64_t web_window_replace(const char* url) {
    return monad_js_window_replace(web_str_ptr(url), web_str_len(url));
}

/* The four whole-string `location` reads share one shape: the host writes the
   UTF-8 into `web_scratch` and answers the byte count, which `web_take_str`
   turns into a Monad string. */
char* web_location_origin(void) {
    int64_t n = monad_js_location_origin((int64_t)(intptr_t)web_scratch,
                                         WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_location_href(void) {
    int64_t n = monad_js_location_href((int64_t)(intptr_t)web_scratch,
                                       WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_location_pathname(void) {
    int64_t n = monad_js_location_pathname((int64_t)(intptr_t)web_scratch,
                                           WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_location_search(void) {
    int64_t n = monad_js_location_search((int64_t)(intptr_t)web_scratch,
                                         WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

/* `""` (a zero-length answer) is how the Monad side reads "absent", so a
   parameter that is present but empty is indistinguishable from one that is
   not there. OAuth parameters are never legitimately empty, and `location_search`
   is available to a caller that must tell them apart. */
char* web_location_search_param(const char* name) {
    int64_t n = monad_js_location_search_param(web_str_ptr(name), web_str_len(name),
                                               (int64_t)(intptr_t)web_scratch,
                                               WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_crypto_error(int64_t op) {
    int64_t n = monad_js_crypto_error(op, (int64_t)(intptr_t)web_scratch,
                                      WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_crypto_op_key(int64_t op) {
    return monad_js_crypto_op_key(op);
}

int64_t web_ecdsa_generate_begin(void) {
    return monad_js_ecdsa_generate_begin();
}

int64_t web_ecdsa_export_jwk_begin(int64_t key) {
    return monad_js_ecdsa_export_jwk_begin(key);
}

int64_t web_ecdsa_export_raw_begin(int64_t key) {
    return monad_js_ecdsa_export_raw_begin(key);
}

/* The signing input crosses as a caller-owned `ByteBuf`, the same typed
   boundary `crypto_sha256_begin` uses: the buffer is the only channel, so no
   address-producing primitive appears on the Monad side. */
int64_t web_ecdsa_sign_begin(int64_t key, int64_t buf) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t len = obj ? obj->len : 0;
    const char* data = obj ? (const char*)obj->payload : "";
    return monad_js_ecdsa_sign_begin(key, (int64_t)(intptr_t)data, len);
}

int64_t web_keystore_put_begin(const char* slot, int64_t key) {
    return monad_js_keystore_put_begin(web_str_ptr(slot), web_str_len(slot), key);
}

int64_t web_keystore_get_begin(const char* slot) {
    return monad_js_keystore_get_begin(web_str_ptr(slot), web_str_len(slot));
}

int64_t web_keystore_delete_begin(const char* slot) {
    return monad_js_keystore_delete_begin(web_str_ptr(slot), web_str_len(slot));
}

int64_t web_console_log(const char* s) {
    return monad_js_console_log(web_str_ptr(s), web_str_len(s));
}

int64_t web_try_result(int64_t status, const char* value, const char* typ,
                       const char* error, const char* notes) {
    return monad_js_try_result(status,
                               web_str_ptr(value), web_str_len(value),
                               web_str_ptr(typ), web_str_len(typ),
                               web_str_ptr(error), web_str_len(error),
                               web_str_ptr(notes), web_str_len(notes));
}

int64_t web_worker_run(const char* source) {
    return monad_js_worker_run(web_str_ptr(source), web_str_len(source));
}

int64_t web_worker_poll(void) {
    return monad_js_worker_poll();
}

static char* web_worker_str(int64_t (*read)(int64_t, int64_t)) {
    int64_t n = read((int64_t)(intptr_t)web_scratch, WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_worker_status(void) { return web_worker_str(monad_js_worker_status); }
char* web_worker_value(void) { return web_worker_str(monad_js_worker_value); }
char* web_worker_type(void) { return web_worker_str(monad_js_worker_type); }
char* web_worker_error(void) { return web_worker_str(monad_js_worker_error); }
char* web_worker_notes(void) { return web_worker_str(monad_js_worker_notes); }

int64_t web_worker_cancel(void) {
    return monad_js_worker_cancel();
}

/* The export-call state slot (`motes/web_wasm/src/keep.mo`): one opaque
   word kept between export calls. It lives in .bss, not in the JS host,
   so the collector sees it as a root. */
static int64_t web_keep_slot = 0;

int64_t web_keep_set(int64_t value) {
    web_keep_slot = value;
    return 0;
}

int64_t web_keep_get(void) {
    return web_keep_slot;
}

/* ── async clipboard (motes/web_wasm/src/clipboard.mo) ─────────────────── */

int64_t web_clipboard_available(void) {
    return monad_js_clipboard_available();
}

int64_t web_clipboard_read_begin(void) {
    return monad_js_clipboard_read_begin();
}

int64_t web_clipboard_write_begin(const char* text) {
    return monad_js_clipboard_write_begin(web_str_ptr(text), web_str_len(text));
}

int64_t web_clipboard_poll(int64_t op) {
    return monad_js_clipboard_poll(op);
}

char* web_clipboard_read(int64_t op) {
    int64_t n = monad_js_clipboard_read(op, (int64_t)(intptr_t)web_scratch,
                                         WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_clipboard_error(int64_t op) {
    int64_t n = monad_js_clipboard_error(op, (int64_t)(intptr_t)web_scratch,
                                         WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

/* ── WebRTC and getUserMedia (motes/web_wasm/src/rtc.mo, media_stream.mo) ── */
__attribute__((import_module("monad"), import_name("rtc_open")))
extern int64_t monad_js_rtc_open(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("rtc_peek")))
extern int64_t monad_js_rtc_peek(int64_t id, int64_t which);

__attribute__((import_module("monad"), import_name("rtc_read")))
extern int64_t monad_js_rtc_read(int64_t id, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("rtc_info")))
extern int64_t monad_js_rtc_info(int64_t id, int64_t which);

__attribute__((import_module("monad"), import_name("rtc_set_local")))
extern int64_t monad_js_rtc_set_local(int64_t id, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("rtc_set_remote")))
extern int64_t monad_js_rtc_set_remote(int64_t id, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("rtc_add_ice")))
extern int64_t monad_js_rtc_add_ice(int64_t id, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("rtc_open_channel")))
extern int64_t monad_js_rtc_open_channel(int64_t id, int64_t ptr, int64_t len, int64_t num);

__attribute__((import_module("monad"), import_name("rtc_send")))
extern int64_t monad_js_rtc_send(int64_t id, int64_t lptr, int64_t llen,
                                 int64_t ptr, int64_t len, int64_t is_binary);

__attribute__((import_module("monad"), import_name("rtc_add_stream")))
extern int64_t monad_js_rtc_add_stream(int64_t id, int64_t stream);

__attribute__((import_module("monad"), import_name("rtc_close")))
extern int64_t monad_js_rtc_close(int64_t id);

__attribute__((import_module("monad"), import_name("rtc_watch")))
extern int64_t monad_js_rtc_watch(int64_t id, int64_t handler);

__attribute__((import_module("monad"), import_name("rtc_unwatch")))
extern int64_t monad_js_rtc_unwatch(int64_t id);

__attribute__((import_module("monad"), import_name("rtc_free")))
extern int64_t monad_js_rtc_free(int64_t id);

__attribute__((import_module("monad"), import_name("media_get_begin")))
extern int64_t monad_js_media_get_begin(int64_t ptr, int64_t len, int64_t display);

__attribute__((import_module("monad"), import_name("media_poll")))
extern int64_t monad_js_media_poll(int64_t op);

__attribute__((import_module("monad"), import_name("media_stream")))
extern int64_t monad_js_media_stream(int64_t op);

__attribute__((import_module("monad"), import_name("media_error")))
extern int64_t monad_js_media_error(int64_t op, int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("media_free")))
extern int64_t monad_js_media_free(int64_t stream);
extern int64_t monad_js_media_free_op(int64_t op);
extern int64_t monad_js_media_stream_of(int64_t id);

__attribute__((import_module("monad"), import_name("dom_set_src_object")))
extern int64_t monad_js_dom_set_src_object(int64_t node, int64_t stream);


/* ── WebRTC and media wrappers ─────────────────────────────────────────
 *
 * `getUserMedia` is the only promise-based operation here, so it is
 * two-phase like fetch/clipboard/crypto: `web_media_get_begin` starts the
 * request and `web_media_poll` reports 0 pending / 1 done / 2 failed.
 *
 * `web_rtc_read` is the POP of a peer's queue: it copies the head entry's
 * payload into a caller-owned ByteBuf and removes the entry, answering the
 * entry's kind. The Monad side reads the head's kind and columns through
 * `web_rtc_peek`/`web_rtc_info` FIRST, then calls this exactly once.
 */

int64_t web_rtc_open(const char* servers) {
    return monad_js_rtc_open(web_str_ptr(servers), web_str_len(servers));
}

/* which 0 -> head kind (0 empty), 1 -> live connection state, 2 -> head
   payload length. */
int64_t web_rtc_peek(int64_t id, int64_t which) {
    return monad_js_rtc_peek(id, which);
}

int64_t web_rtc_read(int64_t id, int64_t buf) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t cap = obj ? obj->len : 0;
    return monad_js_rtc_read(id, obj ? (int64_t)(intptr_t)obj->payload : 0, cap);
}

int64_t web_rtc_info(int64_t id, int64_t which) {
    return monad_js_rtc_info(id, which);
}

int64_t web_rtc_set_local(int64_t id, const char* blob) {
    return monad_js_rtc_set_local(id, web_str_ptr(blob), web_str_len(blob));
}

int64_t web_rtc_set_remote(int64_t id, const char* blob) {
    return monad_js_rtc_set_remote(id, web_str_ptr(blob), web_str_len(blob));
}

int64_t web_rtc_add_ice(int64_t id, const char* blob) {
    return monad_js_rtc_add_ice(id, web_str_ptr(blob), web_str_len(blob));
}

int64_t web_rtc_open_channel(int64_t id, const char* label, int64_t num) {
    return monad_js_rtc_open_channel(id, web_str_ptr(label), web_str_len(label), num);
}

/* The message bytes travel as a caller-owned ByteBuf -- the typed boundary,
   so no address crosses Monad code. */
int64_t web_rtc_send(int64_t id, const char* label, int64_t buf, int64_t is_binary) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    int64_t len = obj ? obj->len : 0;
    const char* data = obj ? (const char*)obj->payload : "";
    return monad_js_rtc_send(id, web_str_ptr(label), web_str_len(label),
                             (int64_t)(intptr_t)data, len, is_binary);
}

int64_t web_rtc_add_stream(int64_t id, int64_t stream) {
    return monad_js_rtc_add_stream(id, stream);
}

int64_t web_rtc_close(int64_t id) {
    return monad_js_rtc_close(id);
}

int64_t web_rtc_watch(int64_t id, int64_t handler) {
    return monad_js_rtc_watch(id, handler);
}

int64_t web_rtc_unwatch(int64_t id) {
    return monad_js_rtc_unwatch(id);
}

int64_t web_rtc_free(int64_t id) {
    return monad_js_rtc_free(id);
}

int64_t web_media_get_begin(const char* constraints, int64_t display) {
    return monad_js_media_get_begin(web_str_ptr(constraints), web_str_len(constraints),
                                    display);
}

int64_t web_media_poll(int64_t op) {
    return monad_js_media_poll(op);
}

int64_t web_media_stream(int64_t op) {
    return monad_js_media_stream(op);
}

char* web_media_error(int64_t op) {
    int64_t n = monad_js_media_error(op, (int64_t)(intptr_t)web_scratch,
                                     WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_media_free(int64_t stream) {
    return monad_js_media_free(stream);
}

int64_t web_media_free_op(int64_t op) {
    return monad_js_media_free_op(op);
}

int64_t web_media_stream_of(int64_t id) {
    return monad_js_media_stream_of(id);
}

/* `video.srcObject = stream`. The ONE object-property write in this boundary,
   and typed on purpose: it takes a node and a stream, never a property name,
   so it cannot set an arbitrary JS property. */
int64_t web_dom_set_src_object(int64_t node, int64_t stream) {
    return monad_js_dom_set_src_object(node, stream);
}

/* ── current-event getters (motes/web_wasm/src/event.mo) ───────────────── */

int64_t web_event_i64(int64_t which) {
    return monad_js_event_i64(which);
}

double web_event_f64(int64_t which) {
    return monad_js_event_f64(which);
}

char* web_event_str(int64_t which) {
    int64_t n = monad_js_event_str(which, (int64_t)(intptr_t)web_scratch,
                                   WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_event_data(const char* mime) {
    int64_t n = monad_js_event_data(web_str_ptr(mime), web_str_len(mime),
                                    (int64_t)(intptr_t)web_scratch,
                                    WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

char* web_event_types(void) {
    int64_t n = monad_js_event_types((int64_t)(intptr_t)web_scratch,
                                     WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_event_files_count(void) {
    return monad_js_event_files_count();
}

int64_t web_event_file_i64(int64_t index, int64_t which) {
    return monad_js_event_file_i64(index, which);
}

char* web_event_file_str(int64_t index, int64_t which) {
    int64_t n = monad_js_event_file_str(index, which,
                                        (int64_t)(intptr_t)web_scratch,
                                        WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_event_prevent_default(void) {
    return monad_js_event_prevent_default();
}

int64_t web_event_stop_propagation(void) {
    return monad_js_event_stop_propagation();
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

/* `clock_now`: the page has one millisecond clock (`Date.now`) for both
   ids; any other id is -EINVAL (22), as on posix. */
int64_t monad_clock_now(int64_t clock) {
    if (clock != 0 && clock != 1) return -22;
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

/* The narrower signed siblings, same canonicalize-then-print shape. */
rt_str monad_i8_to_string(int64_t n) {
    return monad_i64_to_string((int64_t)(int8_t)n);
}

rt_str monad_i16_to_string(int64_t n) {
    return monad_i64_to_string((int64_t)(int16_t)n);
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

rt_str monad_f64_to_string(int64_t v) {
    char scratch[400];
    int64_t n = monad_js_f64_to_string(v, (int64_t)(intptr_t)scratch,
                                      (int64_t)sizeof(scratch));
    if (n < 0 || n >= (int64_t)sizeof(scratch)) {
        /* A host that cannot render a number still owes the caller a
           String. "NaN" is the one spelling every target shares for a
           value we could not format. */
        scratch[0] = 'N';
        scratch[1] = 'a';
        scratch[2] = 'N';
        n = 3;
    }
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)(n + 1)));
    if (!out) return 0;
    for (int64_t i = 0; i < n; i++) out[i] = scratch[i];
    out[n] = '\0';
    return RT_WORD(out);
}

/* `F32.to_string` on the web target. The JS host's formatter (the
   `monad_js_f64_to_string` import) only speaks double, and this
   platform has no libc for the native target's `strtof`-based
   shortest-f32 search, so the payload -- already an f32-ROUNDED
   double by the storage invariant -- goes to the double formatter
   as-is. That prints the shortest DOUBLE spelling of the f32 value
   ("0.10000000149011612" for the f32 0.1) where Rust's `f32` Display
   prints "0.1": a formatting-only divergence, web only, and
   the same looseness the f64 web spelling already carries (JS writes
   "1e+20" where Rust writes "100000000000000000000"). */
rt_str monad_f32_to_string(int64_t v) {
    return monad_f64_to_string(v);
}

/* ── canvas + WebGL (`motes/web_wasm/src/{canvas,gl}.mo`) ───────────────
   Contexts and GL objects are ids into the JS host's tables. Every GL enum
   value is chosen by `gl.mo`; these wrappers only forward words, strings as
   (ptr, len), and doubles. The info log comes back through the scratch
   buffer like `dom_tag_name`. */

__attribute__((import_module("monad"), import_name("canvas_get_context")))
extern int64_t monad_js_canvas_get_context(int64_t node, int64_t flags);

__attribute__((import_module("monad"), import_name("canvas_fit")))
extern int64_t monad_js_canvas_fit(int64_t node);

__attribute__((import_module("monad"), import_name("dom_metric")))
extern double monad_js_dom_metric(int64_t node, int64_t which);

__attribute__((import_module("monad"), import_name("gl_info")))
extern int64_t monad_js_gl_info(int64_t ctx, int64_t which);

__attribute__((import_module("monad"), import_name("gl_create")))
extern int64_t monad_js_gl_create(int64_t ctx, int64_t kind);

__attribute__((import_module("monad"), import_name("gl_delete")))
extern int64_t monad_js_gl_delete(int64_t ctx, int64_t kind, int64_t id);

__attribute__((import_module("monad"), import_name("gl_bind")))
extern int64_t monad_js_gl_bind(int64_t ctx, int64_t kind, int64_t target, int64_t id);

__attribute__((import_module("monad"), import_name("gl_shader")))
extern int64_t monad_js_gl_shader(int64_t ctx, int64_t stage, int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("gl_link")))
extern int64_t monad_js_gl_link(int64_t ctx, int64_t program, int64_t vs, int64_t fs);

__attribute__((import_module("monad"), import_name("gl_log")))
extern int64_t monad_js_gl_log(int64_t ptr, int64_t max);

__attribute__((import_module("monad"), import_name("gl_location")))
extern int64_t monad_js_gl_location(int64_t ctx, int64_t program, int64_t kind,
                                    int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("gl_vertex_attrib")))
extern int64_t monad_js_gl_vertex_attrib(int64_t ctx, int64_t index, int64_t size,
                                         int64_t type, int64_t normalized,
                                         int64_t stride, int64_t offset);

__attribute__((import_module("monad"), import_name("gl_uniform_f")))
extern int64_t monad_js_gl_uniform_f(int64_t ctx, int64_t loc, int64_t n,
                                     double x, double y, double z, double w);

__attribute__((import_module("monad"), import_name("gl_clear_color")))
extern int64_t monad_js_gl_clear_color(int64_t ctx, double r, double g, double b, double a);

__attribute__((import_module("monad"), import_name("gl_state")))
extern int64_t monad_js_gl_state(int64_t ctx, int64_t which, int64_t a, int64_t b,
                                 int64_t c, int64_t d);

__attribute__((import_module("monad"), import_name("gl_draw")))
extern int64_t monad_js_gl_draw(int64_t ctx, int64_t indexed, int64_t mode,
                                int64_t a, int64_t b);

__attribute__((import_module("monad"), import_name("gl_tex_image_from_image")))
extern int64_t monad_js_gl_tex_image_from_image(int64_t ctx, int64_t target, int64_t image);

__attribute__((import_module("monad"), import_name("gl_state_f")))
extern int64_t monad_js_gl_state_f(int64_t ctx, int64_t which, double a, double b,
                                   double c, double d);

__attribute__((import_module("monad"), import_name("gl_tex_image_depth")))
extern int64_t monad_js_gl_tex_image_depth(int64_t ctx, int64_t w, int64_t h);

__attribute__((import_module("monad"), import_name("gl_framebuffer_texture")))
extern int64_t monad_js_gl_framebuffer_texture(int64_t ctx, int64_t attachment, int64_t texture);

__attribute__((import_module("monad"), import_name("image_load_begin")))
extern int64_t monad_js_image_load_begin(int64_t ptr, int64_t len);

__attribute__((import_module("monad"), import_name("image_info")))
extern int64_t monad_js_image_info(int64_t image, int64_t which);

int64_t web_canvas_get_context(int64_t node, int64_t flags) {
    return monad_js_canvas_get_context(node, flags);
}

int64_t web_canvas_fit(int64_t node) {
    return monad_js_canvas_fit(node);
}

double web_dom_metric(int64_t node, int64_t which) {
    return monad_js_dom_metric(node, which);
}

int64_t web_gl_info(int64_t ctx, int64_t which) {
    return monad_js_gl_info(ctx, which);
}

int64_t web_gl_create(int64_t ctx, int64_t kind) {
    return monad_js_gl_create(ctx, kind);
}

int64_t web_gl_delete(int64_t ctx, int64_t kind, int64_t id) {
    return monad_js_gl_delete(ctx, kind, id);
}

int64_t web_gl_bind(int64_t ctx, int64_t kind, int64_t target, int64_t id) {
    return monad_js_gl_bind(ctx, kind, target, id);
}

int64_t web_gl_shader(int64_t ctx, int64_t stage, const char* source) {
    return monad_js_gl_shader(ctx, stage, web_str_ptr(source), web_str_len(source));
}

int64_t web_gl_link(int64_t ctx, int64_t program, int64_t vs, int64_t fs) {
    return monad_js_gl_link(ctx, program, vs, fs);
}

char* web_gl_log(void) {
    int64_t n = monad_js_gl_log((int64_t)(intptr_t)web_scratch, WEB_SCRATCH_BYTES - 1);
    return web_take_str(web_scratch, n);
}

int64_t web_gl_location(int64_t ctx, int64_t program, int64_t kind, const char* name) {
    return monad_js_gl_location(ctx, program, kind, web_str_ptr(name), web_str_len(name));
}

int64_t web_gl_vertex_attrib(int64_t ctx, int64_t index, int64_t size, int64_t type,
                             int64_t normalized, int64_t stride, int64_t offset) {
    return monad_js_gl_vertex_attrib(ctx, index, size, type, normalized, stride, offset);
}

int64_t web_gl_uniform_f(int64_t ctx, int64_t loc, int64_t n,
                         double x, double y, double z, double w) {
    return monad_js_gl_uniform_f(ctx, loc, n, x, y, z, w);
}

int64_t web_gl_clear_color(int64_t ctx, double r, double g, double b, double a) {
    return monad_js_gl_clear_color(ctx, r, g, b, a);
}

int64_t web_gl_state(int64_t ctx, int64_t which, int64_t a, int64_t b, int64_t c, int64_t d) {
    return monad_js_gl_state(ctx, which, a, b, c, d);
}

int64_t web_gl_draw(int64_t ctx, int64_t indexed, int64_t mode, int64_t a, int64_t b) {
    return monad_js_gl_draw(ctx, indexed, mode, a, b);
}

int64_t web_gl_tex_image_from_image(int64_t ctx, int64_t target, int64_t image) {
    return monad_js_gl_tex_image_from_image(ctx, target, image);
}

int64_t web_gl_state_f(int64_t ctx, int64_t which, double a, double b, double c, double d) {
    return monad_js_gl_state_f(ctx, which, a, b, c, d);
}

int64_t web_gl_tex_image_depth(int64_t ctx, int64_t w, int64_t h) {
    /* The same bound as `web_gl_tex_image_pixels`. */
    if (w <= 0 || h <= 0 || w > 16384 || h > 16384) return 0;
    return monad_js_gl_tex_image_depth(ctx, w, h);
}

int64_t web_gl_framebuffer_texture(int64_t ctx, int64_t attachment, int64_t texture) {
    return monad_js_gl_framebuffer_texture(ctx, attachment, texture);
}

int64_t web_image_load_begin(const char* url) {
    return monad_js_image_load_begin(web_str_ptr(url), web_str_len(url));
}

int64_t web_image_info(int64_t image, int64_t which) {
    return monad_js_image_info(image, which);
}

__attribute__((import_module("monad"), import_name("gl_buffer_data")))
extern int64_t monad_js_gl_buffer_data(int64_t ctx, int64_t target, int64_t sub, int64_t a,
                                       int64_t kind, int64_t ptr, int64_t count);

__attribute__((import_module("monad"), import_name("gl_uniform_matrix")))
extern int64_t monad_js_gl_uniform_matrix(int64_t ctx, int64_t loc, int64_t n, int64_t ptr);

__attribute__((import_module("monad"), import_name("gl_tex_image_pixels")))
extern int64_t monad_js_gl_tex_image_pixels(int64_t ctx, int64_t target, int64_t w, int64_t h,
                                            int64_t ptr);

/* The `Buf` behind an upload, or NULL when the word is not a buffer of
   `kind` holding at least `min_len` elements. The JS side views exactly
   `len` (or the requested prefix) elements at the payload, so the byte
   range always comes from the buffer's own recorded count and kind. */
static BufObj* web_gl_buf_obj(int64_t word) {
    BufObj* obj = (BufObj*)RT_PTR(word);
    return (obj && obj->header.tag == MONAD_BUF_TAG) ? obj : NULL;
}

static BufObj* web_gl_buf(int64_t word, int64_t kind, int64_t min_len) {
    BufObj* obj = web_gl_buf_obj(word);
    if (!obj || obj->elem_kind != kind || obj->len < min_len) return NULL;
    return obj;
}

int64_t web_gl_buffer_data(int64_t ctx, int64_t target, int64_t sub, int64_t a, int64_t data) {
    BufObj* obj = web_gl_buf_obj(data);
    if (!obj) return 0;
    int64_t kind = obj->elem_kind;
    if (kind != MONAD_ELEM_F32 && kind != MONAD_ELEM_I32 && kind != MONAD_ELEM_U8) return 0;
    return monad_js_gl_buffer_data(ctx, target, sub, a, kind, (int64_t)(intptr_t)obj->payload,
                                   obj->len);
}

int64_t web_gl_uniform_matrix(int64_t ctx, int64_t loc, int64_t n, int64_t m) {
    if (n < 2 || n > 4) return 0;
    BufObj* obj = web_gl_buf(m, MONAD_ELEM_F32, n * n);
    if (!obj) return 0;
    return monad_js_gl_uniform_matrix(ctx, loc, n, (int64_t)(intptr_t)obj->payload);
}

int64_t web_gl_tex_image_pixels(int64_t ctx, int64_t target, int64_t w, int64_t h,
                                int64_t pixels) {
    /* 16384 is above every WebGL MAX_TEXTURE_SIZE; it keeps w*h*4 far from
       overflowing an int64. */
    if (w <= 0 || h <= 0 || w > 16384 || h > 16384) return 0;
    BufObj* obj = web_gl_buf(pixels, MONAD_ELEM_U8, w * h * 4);
    if (!obj) return 0;
    return monad_js_gl_tex_image_pixels(ctx, target, w, h, (int64_t)(intptr_t)obj->payload);
}

/* ── entry point ────────────────────────────────────────────────────── */

__attribute__((export_name("monad_main")))
int64_t monad_web_entry(int64_t args) {
    /* Exports-only module: no `def main` was compiled, so the weak
       reference is 0 and there is nothing to run. */
    if (!main_monad) return 0;
    monad_export_enter();
    rt_word list = args ? (rt_word)args : alloc_constructor(5, 0);
    return monad_export_leave((int64_t)(intptr_t)main_monad(list));
}
