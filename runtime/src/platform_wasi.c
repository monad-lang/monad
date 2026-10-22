/* WASI platform (wasm32-unknown-wasip1).
 *
 * No Boehm GC, no pthreads, no processes or sockets: the heap is wasi-libc
 * malloc with no free (codegen never emits monad_release, so this is the
 * same leaky discipline the native Boehm build already has), and every
 * IR-facing function uses the i64 word ABI from runtime_abi.h.
 *
 * v0 enables console I/O, time and the command-line entry point. File,
 * stream, process, fiber, socket and terminal natives are deliberately
 * unavailable (see lang/src/codegen/natives.mo); their C functions are not
 * defined here, so a reachable call is caught by the target gate rather
 * than becoming a link error.
 */
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

rt_word monad_alloc(rt_size size) {
    void* ptr = malloc((size_t)size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return RT_WORD(ptr);
}

rt_word monad_alloc_atomic(rt_size size) {
    return RT_WORD(malloc((size_t)size));
}

void monad_retain(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    h->refcount += 1;
}

void monad_release(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    /* No free: the block is malloc'd and nothing reclaims it, matching the
       native build's GC-owned blocks. */
    h->refcount -= 1;
}

/* `IO.println`'s bootstrap shim. WASI stdout is line-buffered, so the
   newline flushes the line; `main`'s exit flushes the rest. */
rt_void monad_print_str(rt_str s) {
    const char* str = RT_STR(s);
    if (str) printf("%s\n", str);
    RT_VOID_RETURN;
}

int64_t monad_current_time(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + (int64_t)ts.tv_nsec / 1000000;
}

int64_t monad_current_time_nano(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000 + (int64_t)ts.tv_nsec;
}

rt_str monad_read_stdin_exact(int64_t n) {
    if (n <= 0) {
        char* empty = (char*)RT_PTR(monad_alloc_atomic(1));
        if (empty) empty[0] = '\0';
        return RT_WORD(empty);
    }
    size_t want = (size_t)n;
    char* buf = (char*)RT_PTR(monad_alloc_atomic((rt_size)(want + 1)));
    if (!buf) {
        char* empty = (char*)RT_PTR(monad_alloc_atomic(1));
        if (empty) empty[0] = '\0';
        return RT_WORD(empty);
    }
    size_t got = 0;
    while (got < want) {
        ssize_t r = read(0, buf + got, want - got);
        if (r < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (r == 0) break;
        got += (size_t)r;
    }
    buf[got] = '\0';
    return RT_WORD(buf);
}

rt_word monad_flush_stdout(void) {
    fflush(stdout);
    return alloc_constructor(0, 0);
}

/* ── byte streams over fds 0/1/2 ──────────────────────────────────────
   `IO.println`/`IO.write_stdout`/`IO.read_line` are ordinary Monad over
   `std/stream.mo`, so the three stdio descriptors need these even though
   file streams (`stream_open`) stay unavailable in v0. Failures are
   reported as an empty success: the caller's line reader already treats a
   zero-length read as EOF, and console writes have no recovery path. */
static rt_word wasm_ok(rt_word payload) {
    Constructor* ok = (Constructor*)RT_PTR(alloc_constructor(10, 1));
    if (ok) ok->fields[0] = RT_FIELD(payload);
    return RT_WORD(ok);
}

rt_word monad_stream_write(int64_t fd, rt_word bufw) {
    BufObj* obj = (BufObj*)RT_PTR(bufw);
    int64_t n = obj ? obj->len : 0;
    int64_t done = 0;
    while (done < n) {
        ssize_t w = write((int)fd, obj->payload + done, (size_t)(n - done));
        if (w < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (w == 0) break;
        done += w;
    }
    return wasm_ok((rt_word)done);
}

rt_word monad_stream_read(int64_t fd, int64_t max_bytes) {
    if (max_bytes <= 0) return wasm_ok(RT_WORD(bytebuf_new(0)));
    BufObj* obj = bytebuf_new(max_bytes);
    if (!obj) return wasm_ok(0);
    ssize_t got;
    do {
        got = read((int)fd, obj->payload, (size_t)max_bytes);
    } while (got < 0 && errno == EINTR);
    if (got < 0) got = 0;
    obj->len = (int64_t)got;
    return wasm_ok(RT_WORD(obj));
}

/* `stream_read_line : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) (Option String))` -- one line WITHOUT its newline, or
   `Option.none` at end of stream and for a discarded partial line. A C
   loop, so no stack growth; byte-at-a-time because these profiles have
   only the console descriptors and no cross-call carry to keep. A read
   error reads as end of stream, the convention the natives above set. */
rt_word monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard) {
    size_t cap = 256, len = 0;
    char* buf = (char*)malloc(cap);
    if (!buf) return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    int eof = 0;
    for (;;) {
        char c;
        ssize_t r = read((int)fd, &c, 1);
        if (r < 0) {
            if (errno == EINTR) continue;
            eof = 1;
            break;
        }
        if (r == 0) { eof = 1; break; }
        if (c == '\n') break;
        if (max_len > 0 && (int64_t)len >= max_len) {
            free(buf);
            return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
        }
        if (len + 1 >= cap) {
            size_t want = cap * 2;
            char* grown = (char*)realloc(buf, want);
            if (!grown) {
                free(buf);
                return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
            }
            buf = grown;
            cap = want;
        }
        buf[len++] = c;
    }
    if (eof && (discard || len == 0)) {
        free(buf);
        return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    }
    char* copy = (char*)RT_PTR(monad_alloc_atomic((rt_size)(len + 1)));
    if (!copy) {
        free(buf);
        return wasm_ok(RT_WORD(alloc_constructor(3, 0)));
    }
    memcpy(copy, buf, len);
    copy[len] = '\0';
    free(buf);
    Constructor* some = (Constructor*)RT_PTR(alloc_constructor(4, 1));
    if (some) some->fields[0] = RT_FIELD(RT_WORD(copy));
    return wasm_ok(RT_WORD(some));
}

rt_word monad_stream_close(int64_t fd) {
    if (fd > 2) close((int)fd);
    return alloc_constructor(0, 0);
}

int64_t monad_stream_fd(int64_t fd) {
    return fd;
}

int64_t monad_std_fd(int64_t which) {
    return which;
}

int main(int argc, char** argv) {
    rt_word args = monad_build_args(argc - 1, argv + 1);
    return (int)(intptr_t)main_monad(args);
}
