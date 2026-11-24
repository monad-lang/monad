/* Win32 platform: Boehm allocator, stdio on the CRT descriptors, a clock, the
   sys floor, and the native entry point. Compiled for the Windows target only
   (`-DMONAD_TARGET_WINDOWS`, from `llvm/src/target.mo`'s `windows_plan`).

   This is the EXPERIMENTAL leg: Monad programs cross-compiled HERE to run
   THERE. Compiling ON Windows is deliberately out of scope, so nothing here
   tries to be a port of the compiler -- only of the runtime a compiled
   program links against.

   WHAT THIS FILE DELIBERATELY DOES NOT HAVE, and what that costs. The
   compiler's target gate (`codegen/src/natives.mo`'s
   `windows_os_only_natives`) refuses every native whose C body would need one
   of these, so a call is a named COMPILE error rather than a link error or a
   runtime crash:

     * pthreads. There are no fibers, so no fork_io/await/poll/cancel, no
       scopes and no channels. Every one of those is an OS thread on POSIX
       and there is no honest single-threaded substitute: `await` has to
       block and a channel has to park. That also means this file needs no
       locks anywhere, and the Boehm build here is single-threaded (see
       runtime_windows_prelude.h on GC_THREADS).
     * processes. No fork/execvp is even close to translatable -- CreateProcess
       is not a drop-in and the child's inherited-stdio contract would have to
       be rebuilt from handles.
     * sockets. Winsock is a separate DLL with its own startup
       (WSAStartup), its own error space and its own handle type; TCP is a
       project, not a translation.
     * file streams. `stream_open` is refused because mingw's CRT descriptor
       is an int with a per-process table the runtime cannot reason about, and
       because the POSIX carry table's locking has no meaning here. The three
       stdio descriptors DO work -- see the byte-stream section below.
     * the terminal, inotify, `stream_poll`/`seek`/`set_timeout`, and
       `read_line`'s chunked reader (which is built on `stream_poll`'s
       readiness contract).

   So a compiled Windows binary can print, read stdin, tell the time, sleep,
   ask for its pid, and use the sys floor (env, stat, dir listing, existence).
   That is the whole of `examples/hello.mo` and of a `#[test]`-driven
   smoke test, which is what makes it a proof rather than a claim.
 */

/* ── Allocator ─────────────────────────────────────────────────────────
   Boehm, exactly as the POSIX block does, because the collector is the same
   library: `-lgc` against the mingw build of boehm-gc. The two wrappers are
   duplicated from platform_posix.c rather than shared because the POSIX file
   also defines its own `monad_alloc_stats_*` and the two must not both be
   compiled; the bodies are four lines and keeping them visible here is worth
   more than a shared header would save. */
rt_word monad_alloc(rt_size size) {
    MONAD_STAT(MONAD_STAT_SCANNED, size);
    void* ptr = GC_malloc((size_t)size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return RT_WORD(ptr);
}

rt_word monad_alloc_atomic(rt_size size) {
    MONAD_STAT(MONAD_STAT_ATOMIC, size);
    return RT_WORD(GC_malloc_atomic((size_t)size));
}

void monad_retain(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    atomic_fetch_add(&h->refcount, 1);
}

/* Ownership mode has no Windows story yet (there is no `MONAD_OWNERSHIP`
   arm in the windows plan), so both halves forward exactly as the default
   native build does: the block is GC-owned and freeing it would corrupt the
   collector's heap. */
rt_word monad_owned_alloc(rt_size size) { return monad_alloc(size); }
rt_void monad_owned_free(rt_word ptr) { (void)ptr; RT_VOID_RETURN; }

void monad_release(rt_word ptr) {
    if (!ptr) return;
    Header* h = (Header*)RT_PTR(ptr);
    atomic_fetch_sub(&h->refcount, 1);
}

/* ── Allocation stats ──────────────────────────────────────────────────
   `MONAD_ALLOC_STATS=1` works here too, and that is not decoration: it is
   how a Windows run reports whether the collector is actually collecting,
   which is the one memory question this leg cannot answer by `ps`.
   `__atomic_fetch_add` is the same builtin the POSIX block uses and needs no
   <stdatomic.h> for the counters; single-threaded here, so relaxed ordering
   is not an optimisation but a statement of fact. */
static unsigned long long monad_stat_counts[MONAD_STAT_KIND_COUNT];
static unsigned long long monad_stat_bytes[MONAD_STAT_KIND_COUNT];
static int monad_stats_on = 0;

void monad_alloc_stats_note(int kind, rt_size bytes) {
    if (!monad_stats_on) return;
    if (kind < 0 || kind >= MONAD_STAT_KIND_COUNT) return;
    __atomic_fetch_add(&monad_stat_counts[kind], 1ULL, __ATOMIC_RELAXED);
    __atomic_fetch_add(&monad_stat_bytes[kind], (unsigned long long)bytes, __ATOMIC_RELAXED);
}

static const char* monad_stat_label(int kind) {
    switch (kind) {
        case MONAD_STAT_CTOR: return "constructor";
        case MONAD_STAT_CLOSURE: return "closure";
        case MONAD_STAT_ARRAY: return "array";
        case MONAD_STAT_REF: return "ref";
        case MONAD_STAT_BYTEBUF: return "bytebuf";
        case MONAD_STAT_ATOMIC: return "atomic";
        case MONAD_STAT_SCANNED: return "scanned";
        case MONAD_STAT_OWNED_CTOR: return "owned-constructors";
        case MONAD_STAT_OWNED_FREE: return "owned-frees";
        default: return "?";
    }
}

/* The POSIX block installs this through `atexit`; here it runs at the end
   of `main`, which is simpler and strictly ordered -- `atexit` handlers on
   mingw run after the CRT has torn down more than this needs.
   `GetEnvironmentVariableA` rather than `getenv` only because this is the
   one place the value is read before `main`'s own arguments are touched;
   `getenv` would do and is what the POSIX side uses. */
static int monad_stats_requested(void) {
    char v[16];
    DWORD n = GetEnvironmentVariableA("MONAD_ALLOC_STATS", v, (DWORD)sizeof v);
    if (n == 0 || n >= (DWORD)sizeof v) return 0;
    return !(v[0] == '0' || v[0] == '\0');
}

static void monad_alloc_stats_print(void) {
    unsigned long long total_bytes = 0, total_count = 0;
    for (int k = 0; k < MONAD_STAT_KIND_COUNT; k++) {
        total_bytes += monad_stat_bytes[k];
        total_count += monad_stat_counts[k];
        if (monad_stat_counts[k] || monad_stat_bytes[k]) {
            fprintf(stderr, "monad alloc %-18s %10llu  %12llu bytes\n",
                    monad_stat_label(k), monad_stat_counts[k], monad_stat_bytes[k]);
        }
    }
    fprintf(stderr, "monad alloc %-18s %10llu  %12llu bytes\n",
            "TOTAL", total_count, total_bytes);
}

/* ── Value constructors ────────────────────────────────────────────────
   The runtime's own fixed tags, duplicated from platform_posix.c's `tcp_ok`
   family because those are `static` there. 0 is `Unit`, 10 is `Result.ok`,
   11 is `Result.err`, 6 is `List.cons`, 15 is `Pair`, 3 is `Option.none`,
   4 is `Option.some` -- all fixed by the prelude, the same numbers the wasm
   blocks use. */
static void* win_unit(void) {
    return alloc_constructor_impl(0, 0);
}

static void* win_ok(void* payload) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = payload;
    return ok;
}

/* ── errno mapping ─────────────────────────────────────────────────────
   The CRT's errno values are NOT Linux's: mingw numbers its own, and
   `ENOTEMPTY`/`ENAMETOOLONG`/`ETIMEDOUT` in particular share numbers with
   unrelated POSIX codes. Reporting a raw CRT errno as `StreamErrorKind`
   would therefore be actively wrong -- so this switch names the CRT symbols
   and maps them, rather than the numbers. Same shape and same declaration
   order as `stream_error_kind_of_errno` in platform_posix.c
   (std/src/stream.mo's `StreamErrorKind`). */
static int64_t win_error_kind_of_errno(int errnum) {
    switch (errnum) {
        case ENOENT: return 0;                                  /* not_found */
        case EACCES: case EPERM: return 1;                      /* permission_denied */
        case ECONNREFUSED: return 2;                            /* connection_refused */
        case ECONNRESET: return 3;                              /* connection_reset */
        case EPIPE: return 4;                                   /* broken_pipe */
        case EINVAL: case ENOTSOCK: return 5;                   /* invalid_input */
        case ETIMEDOUT: return 6;                               /* timed_out */
        case EADDRINUSE: return 7;                              /* address_in_use */
        default: return 9;                                      /* other */
    }
}

/* `Result.err` around an already-built payload (tag 11). */
static void* win_err(void* payload) {
    Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
    if (err) err->fields[0] = payload;
    return err;
}

/* `Result.err (Pair.pair <kind> "<op>: <strerror> (os error <n>)")`, the
   exact message shape platform_posix.c's `stream_err` produces, so
   `StreamError.message` is the same text on both platforms. */
static void* win_stream_err(int64_t kind, const char* a, const char* b, int errnum) {
    char buf[512];
    if (errnum != 0) {
        snprintf(buf, sizeof buf, "%s: %s (os error %d)", a, b, errnum);
    } else {
        snprintf(buf, sizeof buf, "%s: %s", a, b);
    }
    size_t len = strlen(buf);
    char* copy = (char*)RT_PTR(monad_alloc_atomic((rt_size)(len + 1)));
    if (copy) memcpy(copy, buf, len + 1);
    Constructor* pair = (Constructor*)alloc_constructor_impl(15, 2);
    if (pair) {
        pair->fields[0] = (void*)(intptr_t)kind;
        pair->fields[1] = copy;
    }
    return win_err(pair);
}

static void* win_stream_os_err(const char* op, int errnum) {
    return win_stream_err(win_error_kind_of_errno(errnum), op, strerror(errnum), errnum);
}

/* ── stdio ─────────────────────────────────────────────────────────────
   `IO.println`'s bootstrap shim. `printf` on mingw writes to the CRT
   descriptor in text mode, which translates `\n` to `\r\n` -- correct for a
   console and for a redirected file, and the reason this is not `fwrite` of a
   pre-built buffer (that would need the translation done by hand). */
rt_void monad_print_str(rt_str s) {
    char* str = RT_STR(s);
    if (str) printf("%s\n", str);
    RT_VOID_RETURN;
}

/* `flush_stdout : RawIO Unit` -- stdout is block-buffered when it is a pipe,
   exactly as on POSIX. */
rt_word monad_flush_stdout(void) {
    fflush(stdout);
    return RT_WORD(win_unit());
}

/* Read up to `n` bytes from the standard input, as a NUL-terminated GC
   string. The CRT's `_read` is used rather than `fread` because stdin is put
   in BINARY mode by `main` (see there): a line-oriented text-mode read would
   turn the first Ctrl-Z into an end-of-file and mangle a `\r\n` into `\n`,
   both of which would corrupt a framed protocol read. */
rt_str monad_read_stdin_exact(int64_t n) {
    if (n <= 0) {
        char* empty = (char*)RT_PTR(monad_alloc_atomic(1));
        if (empty) empty[0] = '\0';
        return RT_STR_WORD(empty);
    }
    size_t want = (size_t)n;
    char* buf = (char*)RT_PTR(monad_alloc_atomic((rt_size)(want + 1)));
    if (!buf) {
        char* empty = (char*)RT_PTR(monad_alloc_atomic(1));
        if (empty) empty[0] = '\0';
        return RT_STR_WORD(empty);
    }
    size_t got = 0;
    while (got < want) {
        int r = _read(0, buf + got, (unsigned)(want - got));
        if (r < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (r == 0) break;            /* EOF */
        got += (size_t)r;
    }
    buf[got] = '\0';
    return RT_STR_WORD(buf);
}

/* ── byte streams over descriptors 0/1/2 ───────────────────────────────
   `IO.println`/`IO.write_stdout`/`IO.read_line` are ordinary Monad over
   `std/stream.mo`, so the three stdio descriptors need these even though
   `stream_open` is unavailable. Only 0/1/2 are served: any other descriptor
   came from a native this target refuses, so a call with one is unreachable
   and answers `invalid_input` rather than guessing at a handle table.

   There is no carry table here (unlike platform_posix.c), because the only
   reader is the console's and the only line reader is the one below, which
   does its own byte-at-a-time loop. Mixing `read_line` with `read` on stdin
   therefore loses bytes on this target -- acceptable for the experimental
   leg, and the reason `read_line` stays in the refused list for anything but
   the console path `IO.read_line` uses. */
rt_word monad_stream_write(int64_t fd, rt_word bufw) {
    BufObj* obj = (BufObj*)RT_PTR(bufw);
    int64_t n = obj ? obj->len : 0;
    if (fd < 0 || fd > 2) return RT_WORD(win_stream_err(5, "stream_write", "unknown descriptor", 0));
    if (n == 0) return RT_WORD(win_ok((void*)(intptr_t)0));
    if (fd == 1 || fd == 2) {
        FILE* f = fd == 1 ? stdout : stderr;
        errno = 0;
        int failed = fwrite(obj->payload, 1, (size_t)n, f) != (size_t)n;
        failed = fflush(f) == EOF || failed;
        if (failed) return RT_WORD(win_stream_os_err("stream_write", errno ? errno : EIO));
        return RT_WORD(win_ok((void*)(intptr_t)n));
    }
    /* stdin is not writable. */
    return RT_WORD(win_stream_err(5, "stream_write", "stdin is not writable", 0));
}

rt_word monad_stream_read(int64_t fd, int64_t max_bytes) {
    if (fd < 0 || fd > 2) return RT_WORD(win_stream_err(5, "stream_read", "unknown descriptor", 0));
    if (fd != 0) return RT_WORD(win_stream_err(5, "stream_read", "not readable", 0));
    if (max_bytes <= 0) return RT_WORD(win_ok(bytebuf_new(0)));
    BufObj* obj = bytebuf_new(max_bytes);
    if (!obj) return RT_WORD(win_stream_err(9, "stream_read", "out of memory", 0));
    int n;
    do {
        n = _read(0, obj->payload, (unsigned)max_bytes);
    } while (n < 0 && errno == EINTR);
    if (n < 0) {
        int e = errno;
        return RT_WORD(win_stream_os_err("stream_read", e));
    }
    obj->len = (int64_t)n;
    return RT_WORD(win_ok(obj));
}

/* One line from stdin, without its terminator: `Option.some` at a line, and
   `Option.none` at end of stream (and for a `max_len`-truncated line, the
   `discard` convention platform_posix.c documents). `\r` is dropped at the
   end of a line so a CRLF file reads as the same text as on POSIX -- which
   matters because a Windows-hosted editor is exactly where these files come
   from. */
rt_word monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard) {
    if (fd != 0) return RT_WORD(win_stream_err(5, "stream_read_line", "only stdin can be read a line", 0));
    size_t cap = 256, len = 0;
    char* buf = (char*)malloc(cap);
    if (!buf) return RT_WORD(win_stream_err(9, "stream_read_line", "out of memory", 0));
    int eof = 0, too_long = 0;
    for (;;) {
        char c;
        int r;
        do {
            r = _read(0, &c, 1);
        } while (r < 0 && errno == EINTR);
        if (r < 0) { eof = 1; break; }
        if (r == 0) { eof = 1; break; }
        if (c == '\n') break;
        if (max_len > 0 && (int64_t)len >= max_len) { too_long = 1; break; }
        if (len + 1 >= cap) {
            size_t want = cap * 2;
            char* grown = (char*)realloc(buf, want);
            if (!grown) {
                free(buf);
                return RT_WORD(win_stream_err(9, "stream_read_line", "out of memory", 0));
            }
            buf = grown;
            cap = want;
        }
        buf[len++] = c;
    }
    if (too_long || (eof && (discard || len == 0))) {
        free(buf);
        return RT_WORD(win_ok(alloc_constructor_impl(3, 0)));   /* Option.none */
    }
    if (len > 0 && buf[len - 1] == '\r') len--;
    char* copy = (char*)RT_PTR(monad_alloc_atomic((rt_size)(len + 1)));
    if (!copy) {
        free(buf);
        return RT_WORD(win_stream_err(9, "stream_read_line", "out of memory", 0));
    }
    if (len) memcpy(copy, buf, len);
    copy[len] = '\0';
    free(buf);
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);  /* Option.some */
    if (some) some->fields[0] = copy;
    return RT_WORD(win_ok(some));
}

/* Never closes a standard descriptor: closing one would let the CRT hand
   0/1/2 to the next open. */
rt_word monad_stream_close(int64_t fd) {
    if (fd > 2) _close((int)fd);
    return RT_WORD(win_unit());
}

/* The value already IS the descriptor, so both of these are the identity --
   the CRT's descriptor numbers are the same 0/1/2 `std_fd` promises. */
int64_t monad_stream_fd(int64_t fd) {
    return fd;
}

int64_t monad_std_fd(int64_t which) {
    return which;
}

/* ── Time ──────────────────────────────────────────────────────────────
   One 100 ns monotonic tick source for the whole file.
   `QueryPerformanceCounter` is the only monotonic clock here: mingw has
   neither `clock_gettime(CLOCK_MONOTONIC)` nor `timespec_get`/`TIME_UTC`,
   and `GetTickCount64` only has 10-15 ms resolution, which would make
   `IO.now` useless for anything that measures work. The frequency is queried
   once -- it is a constant of the machine, and re-querying it per call would
   be the only cost of this function. */
static LARGE_INTEGER win_perf_freq(void) {
    static LARGE_INTEGER freq;
    static int have = 0;
    if (!have) {
        QueryPerformanceFrequency(&freq);
        if (freq.QuadPart == 0) freq.QuadPart = 1;
        have = 1;
    }
    return freq;
}

/* Whole 100 ns units since an arbitrary origin. 128-bit intermediate so an
   uptime of months cannot overflow the 64-bit result: 2^64 * 100 ns is
   ~58 000 years. */
static int64_t win_perf_ticks_100ns(void) {
    LARGE_INTEGER now, freq;
    QueryPerformanceCounter(&now);
    freq = win_perf_freq();
    return (int64_t)((now.QuadPart / freq.QuadPart) * 10000000ULL
                     + ((now.QuadPart % freq.QuadPart) * 10000000ULL) / freq.QuadPart);
}

int64_t monad_current_time(void) {
    return win_perf_ticks_100ns() / 10000;              /* ms */
}

int64_t monad_current_time_nano(void) {
    return win_perf_ticks_100ns() * 100;                /* ns */
}

/* `#[native "clock_now"]`: 0 is wall-clock, 1 is monotonic, in ns; -errno on
   failure, the floor's convention. The wall clock comes from
   `GetSystemTimeAsFileTime` (100 ns intervals since 1601) rebased onto the
   Unix epoch by the 11644473600 s between them. */
int64_t monad_clock_now(int64_t clock) {
    if (clock == 1) return win_perf_ticks_100ns() * 100;
    if (clock == 0) {
        FILETIME ft;
        GetSystemTimeAsFileTime(&ft);
        ULARGE_INTEGER u;
        u.LowPart = ft.dwLowDateTime;
        u.HighPart = ft.dwHighDateTime;
        /* 116444736000000000 = the 1601->1970 offset in 100 ns units. */
        if (u.QuadPart < 116444736000000000ULL) return 0;
        return (int64_t)((u.QuadPart - 116444736000000000ULL) * 100ULL);
    }
    return -(int64_t)EINVAL;
}

/* `sleep_io : I64 -> RawIO Unit`. `Sleep` takes milliseconds and a negative
   interval means "forever", so a non-positive `ms` must return immediately:
   passing it through would hang the process instead of sleeping not at all. */
rt_word monad_sleep_io(int64_t ms) {
    if (ms > 0) {
        while (ms > 0) {
            DWORD chunk = ms > 0x7FFFFFFF ? 0x7FFFFFFF : (DWORD)ms;
            Sleep(chunk);
            ms -= (int64_t)chunk;
        }
    }
    return RT_WORD(win_unit());
}

int64_t monad_process_id(void) {
    return (int64_t)_getpid();
}

/* ── The sys floor ─────────────────────────────────────────────────────
   `sys/src/raw.mo`'s `sys_int`/`sys_str`/`sys_stat`/`sys_dir_*`, the same
   op numbers and the same `-errno` / `Result.err <errno>` conventions as
   platform_posix.c, because the Monad side above them is shared and cannot
   tell the platforms apart. What differs is which calls EXIST:

     * `sys_int` 0 pid, 1 ppid, 2/3 uid/euid (Windows has no uids: a
       non-elevated process reports 0, and this answers 0 rather than
       failing, which is what the floor's callers do with it), 4 kill
       (TerminateProcess), 5/6 no priority (EINVAL), 7 sysconf: mingw has
       `_SC_PAGESIZE` and nothing else comparable, so 0/2 answer EINVAL.
     * `sys_str` 0 readlink and 1 uname have NO equivalent and answer
       EINVAL; 2 getenv and 3 read_small work.
     * `sys_stat` 0/1 work through `_stat`/`_stat64`; 2 statvfs does not
       exist, so it answers EINVAL rather than inventing numbers.
     * `sys_dir_open`/`next`/`close` work over `FindFirstFile`. */

/* `Result.ok <string>` for the floor. */
static void* win_sys_ok_str(char* s) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = s;
    return ok;
}

static void* win_sys_err(int64_t e) {
    Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
    if (err) err->fields[0] = (void*)(intptr_t)e;
    return err;
}

static void* win_sys_ok_word(int64_t w) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = (void*)(intptr_t)w;
    return ok;
}

/* A GC-owned copy of `len` bytes plus a terminator. */
static char* win_sys_copy_bytes(const char* src, size_t len) {
    char* copy = (char*)RT_PTR(monad_alloc_atomic((rt_size)(len + 1)));
    if (!copy) return NULL;
    if (len) memcpy(copy, src, len);
    copy[len] = '\0';
    return copy;
}

int64_t monad_sys_int(int64_t op, int64_t a, int64_t b) {
    switch (op) {
        case 0: return (int64_t)_getpid();
        case 1: {
            /* No getppid. The CRT keeps the parent's pid nowhere, so this
               asks the toolhelp snapshot for our own entry's parent. */
            HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
            if (snap == INVALID_HANDLE_VALUE) return -(int64_t)EINVAL;
            PROCESSENTRY32 pe;
            pe.dwSize = sizeof pe;
            DWORD self = (DWORD)_getpid();
            int64_t parent = -(int64_t)ENOENT;
            if (Process32First(snap, &pe)) {
                do {
                    if (pe.th32ProcessID == self) { parent = (int64_t)pe.th32ParentProcessID; break; }
                } while (Process32Next(snap, &pe));
            }
            CloseHandle(snap);
            return parent;
        }
        case 2: case 3: return 0;         /* no uids/effective uids */
        case 4: {
            HANDLE h = OpenProcess(PROCESS_TERMINATE, FALSE, (DWORD)a);
            if (!h) return -(int64_t)EACCES;
            BOOL ok = TerminateProcess(h, (UINT)(b & 0xFF));
            CloseHandle(h);
            return ok ? 0 : -(int64_t)EINVAL;
        }
        case 5: case 6: return -(int64_t)EINVAL;   /* no get/setpriority */
        case 7:
            switch (a) {
                case 1: {
                    SYSTEM_INFO si;
                    GetSystemInfo(&si);
                    return (int64_t)si.dwPageSize;
                }
                case 2: {
                    SYSTEM_INFO si;
                    GetSystemInfo(&si);
                    return (int64_t)si.dwNumberOfProcessors;
                }
                default: return -(int64_t)EINVAL;   /* _SC_CLK_TCK has no analogue */
            }
        default: return -(int64_t)EINVAL;
    }
}

void* monad_sys_str(int64_t op, char* arg) {
    switch (op) {
        case 0: return win_sys_err(EINVAL);   /* readlink: no symlinks to read */
        case 1: return win_sys_err(EINVAL);   /* uname: no equivalent */
        case 2: {
            const char* val = arg ? getenv(arg) : NULL;
            if (!val) return win_sys_err(ENOENT);
            char* copy = win_sys_copy_bytes(val, strlen(val));
            return copy ? win_sys_ok_str(copy) : win_sys_err(ENOMEM);
        }
        case 3: {
            FILE* f = arg ? fopen(arg, "rb") : NULL;
            if (!f) return win_sys_err(errno ? errno : ENOENT);
            size_t cap = 4096, len = 0;
            char* buf = (char*)malloc(cap);
            if (!buf) { fclose(f); return win_sys_err(ENOMEM); }
            for (;;) {
                if (len == cap) {
                    char* grown = (char*)realloc(buf, cap * 2);
                    if (!grown) { free(buf); fclose(f); return win_sys_err(ENOMEM); }
                    buf = grown;
                    cap *= 2;
                    if (cap > (1u << 20)) { free(buf); fclose(f); return win_sys_err(ENAMETOOLONG); }
                }
                size_t got = fread(buf + len, 1, cap - len, f);
                len += got;
                if (got == 0) break;
            }
            int bad = ferror(f);
            fclose(f);
            if (bad) { free(buf); return win_sys_err(EIO); }
            char* copy = win_sys_copy_bytes(buf, len);
            free(buf);
            return copy ? win_sys_ok_str(copy) : win_sys_err(ENOMEM);
        }
        default: return win_sys_err(EINVAL);
    }
}

/* `stat`'s three packed fields. mingw's `_stat64` has `st_mode`, `st_size`
   and `st_mtime`, and a path with a trailing backslash or a drive-relative
   spelling is normalised by the CRT itself, so this is a genuine
   implementation rather than a shim. `lstat` (op 1) does not exist: there
   are no symlinks the CRT reports separately, so op 1 is `_stat64` too. */
void* monad_sys_stat(int64_t op, char* path) {
    if (!path) return win_sys_err(EINVAL);
    if (op == 2) return win_sys_err(EINVAL);   /* no statvfs */
    if (op != 0 && op != 1) return win_sys_err(EINVAL);
    struct _stat64 st;
    if (_stat64(path, &st) != 0) return win_sys_err(errno ? errno : ENOENT);
    char out[256];
    snprintf(out, sizeof out, "%llu %lld %lld",
             (unsigned long long)st.st_mode, (long long)st.st_size,
             (long long)st.st_mtime);
    char* copy = win_sys_copy_bytes(out, strlen(out));
    return copy ? win_sys_ok_str(copy) : win_sys_err(ENOMEM);
}

/* A `Dir` handle is a heap `WIN32_FIND_DATAA` plus the search handle: the
   Monad side only round-trips it, so the shape is private. `FindFirstFile`
   yields "." and ".." like `readdir`, and `sys_dir_next` skips them exactly
   as the POSIX one does, so a listing matches byte for byte.
 *
 * `have` is what makes `next` a CONSUMING read. `FindFirstFile` pre-loads the
 * first entry, so between calls `data` holds an entry that has already been
 * seen but not yet handed out; without this flag the second call re-reads it
 * and the listing repeats its first name forever. (`data` is not cleared on
 * exhaustion either: a failed `FindNextFileA` leaves the LAST name in place,
 * so the flag is the only thing that can say "there is nothing left".)
 *
 * The allocation is `monad_alloc` (a scanned block) rather than
 * `monad_alloc_atomic`, which is safe here because `cFileName` holds no
 * Monad values -- a `HANDLE` and a `WIN32_FIND_DATAA` are opaque to the
 * collector, and the block itself is what keeps the search handle alive. */
typedef struct WinDir {
    HANDLE handle;
    /* `have` is what makes `next` a CONSUMING read: `FindFirstFile` pre-loads
       the first entry, so between calls `data` holds one that has been seen
       but not handed out. Without it the second call re-reads that entry and
       the listing repeats its first name forever. */
    int have;
    /* A `FindNextFileA` failure that happened AFTER a name was already read.
       Held until the next call so that name is not lost, and reported then. */
    int pending_err;
    WIN32_FIND_DATAA data;
} WinDir;

void* monad_sys_dir_open(char* path) {
    if (!path) return win_sys_err(EINVAL);
    size_t n = strlen(path);
    /* "dir" -> "dir\*". A trailing separator would make it "dir\\*", which
       FindFirstFile accepts but is worth avoiding: it also accepts "dir/*"
       and normalising here keeps one spelling. */
    size_t need = n + 3;
    char* pattern = (char*)malloc(need);
    if (!pattern) return win_sys_err(ENOMEM);
    memcpy(pattern, path, n);
    if (n > 0 && (path[n - 1] == '\\' || path[n - 1] == '/')) {
        snprintf(pattern + n, need - n, "%s", "*");
    } else {
        snprintf(pattern + n, need - n, "%s", "\\*");
    }
    WinDir* d = (WinDir*)RT_PTR(monad_alloc((rt_size)sizeof(WinDir)));
    if (!d) { free(pattern); return win_sys_err(ENOMEM); }
    d->handle = FindFirstFileA(pattern, &d->data);
    d->have = (d->handle != INVALID_HANDLE_VALUE);
    d->pending_err = 0;
    free(pattern);
    if (d->handle == INVALID_HANDLE_VALUE) {
        int e = (GetLastError() == ERROR_FILE_NOT_FOUND) ? ENOENT : EACCES;
        return win_sys_err(e);
    }
    return win_sys_ok_word((int64_t)(intptr_t)d);
}

/* One bare name per call, and `""` (the empty OK payload) at the end --
   `Sys.list_dir`'s loop stops on an empty name because POSIX `readdir` never
   yields one. `.` and `..` are skipped for the same reason the POSIX native
   skips them, but the skip must ADVANCE FIRST: returning "" while positioned
   on `.` would end the listing immediately, and `Sys.list_dir` would report an
   empty directory. (Measured: that is exactly what this function did before,
   and under wine `IO.list_dir "."` printed nothing and then spun.) */
void* monad_sys_dir_next(void* handle) {
    WinDir* d = (WinDir*)handle;
    if (!d || d->handle == INVALID_HANDLE_VALUE) return win_sys_err(EBADF);
    if (d->pending_err != 0) {
        int e = d->pending_err;
        d->pending_err = 0;
        return win_sys_err(e);
    }
    for (;;) {
        if (!d->have) {
            /* Nothing left: the empty OK payload, which is the end-of-stream
               signal `Sys.list_dir`'s loop stops on (POSIX `readdir` never
               yields an empty name). */
            char* empty = win_sys_copy_bytes("", 0);
            return empty ? win_sys_ok_str(empty) : win_sys_err(ENOMEM);
        }
        /* CONSUME the entry before returning it: `data` always describes the
           entry the next `FindNextFileA` has not yet replaced, so the advance
           belongs to this call. */
        const char* name = d->data.cFileName;
        int skip = strcmp(name, ".") == 0 || strcmp(name, "..") == 0;
        char* copy = NULL;
        if (!skip) {
            copy = win_sys_copy_bytes(name, strlen(name));
            if (!copy) return win_sys_err(ENOMEM);
        }
        if (!FindNextFileA(d->handle, &d->data)) {
            DWORD e = GetLastError();
            d->have = 0;
            /* ERROR_NO_MORE_FILES is a clean end, not a failure. Anything else
               makes the listing untrustworthy, so it is reported -- on the next
               call when this one is already returning a real name. */
            if (e != ERROR_NO_MORE_FILES) {
                d->pending_err = (e == ERROR_ACCESS_DENIED) ? EACCES : EIO;
            }
        }
        if (!skip) return win_sys_ok_str(copy);
    }
}

void* monad_sys_dir_close(void* handle) {
    WinDir* d = (WinDir*)handle;
    if (!d) return (void*)(intptr_t)(-(int64_t)EBADF);
    if (d->handle != INVALID_HANDLE_VALUE) FindClose(d->handle);
    d->handle = INVALID_HANDLE_VALUE;
    return (void*)0;
}

/* ── existence / kind ──────────────────────────────────────────────────
   The truthy-pointer convention `monad_file_exists` and `monad_is_dir`
   document on the POSIX side: a non-NULL return is true, NULL is false. */
char* monad_file_exists(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (f) { fclose(f); return (char*)"1"; }
    return NULL;
}

char* monad_is_dir(char* path) {
    if (!path) return NULL;
    struct _stat64 st;
    if (_stat64(path, &st) != 0) return NULL;
    return ((st.st_mode & _S_IFDIR) != 0) ? (char*)"1" : NULL;
}

/* ── entry point ───────────────────────────────────────────────────────
   No fiber trampoline: `main_monad` runs on the process's own stack, which
   the linker sized with `-Wl,--stack=33554432` (llvm/src/target.mo's
   windows_plan). That is the whole substitute for platform_posix.c's
   `raise_stack_limit`, and it is a better one -- the reserve is in the image
   header rather than a limit raised at startup.

   stdin/stdout/stderr are put in BINARY mode so the runtime's byte counts
   are real: in text mode the CRT would translate `\n` to `\r\n` on the way
   out (double-counting, since `monad_print_str` already lets `printf` do the
   translation it wants) and swallow a Ctrl-Z on the way in.
   `O_BINARY` on stdin only, then: stdout/stderr stay in text mode because
   that IS the right translation for a console, and `monad_print_str`
   depends on it. */
int main(int argc, char** argv) {
    _setmode(0, _O_BINARY);
    if (monad_stats_requested()) monad_stats_on = 1;
    GC_INIT();
    /* Exclude argv[0], matching the interpreter's `run <file> <args...>` and
       the POSIX runtime: a compiled program's `main` gets only its own extra
       arguments. */
    rt_word args = monad_build_args(argc - 1, argv + 1);
    int rc = (int)(intptr_t)main_monad(args);
    if (monad_stats_on) monad_alloc_stats_print();
    fflush(stdout);
    fflush(stderr);
    return rc;
}
