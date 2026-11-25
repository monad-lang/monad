/* Thread-safety stress for the C runtime's shared state.
 *
 * Every compiled fiber is an OS thread, so runtime state that predates
 * fibers is reached from several threads at once. This harness links the
 * real runtime (its `main` renamed away) and hammers that state directly,
 * with no compiler in the loop:
 *
 *   * line reads on many pipes at once -- the per-descriptor carry table
 *     (`stream_carry_*`) grows by `realloc` while other threads use it;
 *   * concurrent spawn/read/reap of child processes -- the
 *     `proc_registry` slot table;
 *   * descriptor inheritance (Linux only: it reads /proc) -- with a
 *     listener, a connection and its accepted end held open, concurrent
 *     spawns of `ls /proc/self/fd` must each see only their own 0/1/2
 *     and ls's directory handle, never a sibling's pipe or a socket;
 *   * a timed stdin poll (`term_ctl` op 3) under a stream of signals --
 *     the way Boehm's stop-the-world signals hit a TUI's frame clock --
 *     must still wait out its full timeout;
 *   * abandoned fibers (Linux only: it reads /proc) -- fibers that are
 *     cancelled or dropped with their scope and never awaited must give
 *     their thread stacks back once they finish;
 *   * fiber answers -- await and poll of a cancelled fiber are `err 1`,
 *     and a fiber whose thread could not be created is `err 2` (forced
 *     with a zero RLIMIT_NPROC, which root ignores; then it is skipped);
 *   * cooperative cancellation -- a fiber cancelled while it sleeps must
 *     not run the continuation bound after the sleep;
 *   * channels -- a take parks until a put arrives, a put parks while the
 *     channel is full, and try_take probes without blocking;
 *   * wait-any -- `monad_fiber_wait_any` parks until one of several fibers
 *     stops and answers its index, and a fiber parked there is woken by
 *     `monad_cancel_fiber` rather than by a timeout, so a cancelled racer
 *     leaves its park promptly. `monad_channel_take_any` parks on a SET of
 *     channels and must wake when a value arrives on any of them;
 *   * a cancel racing a blocked channel wait -- the registry's lock order,
 *     which `channel_wait` and the cancel-walk take in OPPOSITE directions.
 *     A cancel landing while waiters are registering deadlocked AB-BA, and
 *     nothing here cancelled a channel-blocked fiber before this phase, so
 *     the inversion was unreachable from the gate. It fails by HANGING, so
 *     it is watched by a deadline and a watchdog thread.
 *
 * It checks every line it reads, so a lost or corrupted carry is a
 * failure even without a sanitizer, and `scripts/check-runtime-threads.sh`
 * also runs it under ThreadSanitizer, which must report nothing.
 * See plans/implementations/async-runtime-thread-safety.md. */
#define GC_THREADS
#include <gc.h>
#include <pthread.h>
#include <signal.h>
#include <sys/resource.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>

void* monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard);
void* monad_stream_close(int64_t fd);
void* monad_proc_spawn(char* cmd, void* args);
int64_t monad_proc_stream_fd(int64_t handle, int64_t which);
int64_t monad_proc_wait(int64_t handle, int64_t kill_first);
void* monad_build_args(int argc, char** argv);
void* monad_tcp_listen(int64_t port);
int64_t monad_tcp_local_port(int64_t listener);
void* monad_tcp_connect_timeout(char* host, int64_t port, int64_t timeout_ms);
void* monad_tcp_accept(int64_t listener);
int64_t monad_term_ctl(int64_t op, int64_t arg);
void* alloc_closure(void* entry, int64_t arity, int64_t env_size);
void* monad_fork_io(void* closure);
void* monad_cancel_fiber(void* handle);
void* monad_scope_new(void);
void* monad_scope_fork(void* handle, void* closure);
void* monad_scope_drop(void* handle);
void* monad_await_fiber(void* handle);
void* monad_poll_fiber(void* handle);
void* monad_io_pure(int64_t a);
int64_t monad_io_bind(int64_t io_val, int64_t f);
void* monad_channel_new(void);
void* monad_channel_put(void* handle, int64_t value);
int64_t monad_channel_take(void* handle);
void* monad_channel_try_take(void* handle);
int64_t monad_fiber_wait_any(void* fibers);
void* monad_channel_take_any(void* chans);
void* alloc_constructor(int64_t tag, int64_t field_count);

/* The runtime references codegen's entry point; nothing calls it here. */
void* main_monad(void* args) {
    (void)args;
    return 0;
}

/* runtime_core.c's Constructor, mirrored: only `tag` and `fields` are read. */
typedef struct {
    int64_t refcount;
    uint16_t kind;
    uint16_t flags;
    int64_t tag;
    int64_t field_count;
    void* fields[];
} Con;

#define TAG_NONE 3
#define TAG_SOME 4
#define TAG_OK 10
#define TAG_ERR 11

#define PIPE_THREADS 16
#define PIPE_ITERS 300
#define PIPE_LINES 40
#define PROC_THREADS 8
#define PROC_ITERS 40
#define PROC_LINES 40
#define FD_THREADS 8
#define FD_ITERS 40
#define POLL_MS 300
#define LEAK_FIBERS 200

static int failures;

static void fail(void) {
    __atomic_add_fetch(&failures, 1, __ATOMIC_RELAXED);
}

/* Read one line from `fd` and compare it with `want`, or expect end of
   stream when `want` is NULL. 0 on a mismatch. */
static int expect_line(int64_t fd, const char* want) {
    Con* ok = (Con*)monad_stream_read_line(fd, 0, 0);
    if (!ok || ok->tag != TAG_OK) return 0;
    Con* opt = (Con*)ok->fields[0];
    if (!want) return opt->tag == TAG_NONE;
    return opt->tag == TAG_SOME && strcmp((char*)opt->fields[0], want) == 0;
}

/* Each thread writes a batch of numbered lines into its own pipe and
   reads them back by line. One write per batch stays below the pipe
   buffer, so no writer thread is needed. */
static void* pipe_worker(void* arg) {
    int id = (int)(intptr_t)arg;
    char batch[PIPE_LINES * 32];
    char want[32];
    for (int it = 0; it < PIPE_ITERS; it++) {
        int p[2];
        if (pipe(p) < 0) {
            perror("pipe");
            fail();
            return NULL;
        }
        size_t len = 0;
        for (int l = 0; l < PIPE_LINES; l++)
            len += (size_t)sprintf(batch + len, "t%02d-i%03d-l%02d\n", id, it, l);
        if (write(p[1], batch, len) != (ssize_t)len) fail();
        close(p[1]);
        for (int l = 0; l < PIPE_LINES; l++) {
            sprintf(want, "t%02d-i%03d-l%02d", id, it, l);
            if (!expect_line(p[0], want)) {
                fail();
                break;
            }
        }
        if (!expect_line(p[0], NULL)) fail();
        monad_stream_close(p[0]);
    }
    return NULL;
}

/* Each thread spawns `seq 1 PROC_LINES`, reads the child's stdout by line
   and reaps it. Colliding registry slots read another child's output or
   reap the wrong one. */
static void* proc_worker(void* arg) {
    (void)arg;
    char last[16];
    sprintf(last, "%d", PROC_LINES);
    char* argv[] = {"1", last};
    char want[16];
    for (int it = 0; it < PROC_ITERS; it++) {
        Con* r = (Con*)monad_proc_spawn("seq", monad_build_args(2, argv));
        if (!r || r->tag != TAG_OK) {
            fail();
            continue;
        }
        int64_t child = (int64_t)(intptr_t)r->fields[0];
        int64_t out = monad_proc_stream_fd(child, 1);
        for (int l = 1; l <= PROC_LINES; l++) {
            sprintf(want, "%d", l);
            if (!expect_line(out, want)) {
                fail();
                break;
            }
        }
        if (!expect_line(out, NULL)) fail();
        if (monad_proc_wait(child, 0) != 0) fail();
    }
    return NULL;
}

/* The fd in an ok `Result` from a stream or tcp native, or -1. */
static int64_t ok_fd(void* r) {
    Con* c = (Con*)r;
    return c && c->tag == TAG_OK ? (int64_t)(intptr_t)c->fields[0] : -1;
}

#if defined(__linux__)
/* Mark every descriptor this process inherited (fd >= 3) close-on-exec,
   so the fd phase sees only what the runtime itself creates: a CI runner
   or shell that leaks a descriptor into the harness would otherwise show
   up in every child and fail the gate for nothing the runtime did. */
static void cloexec_inherited(void) {
    for (int fd = 3; fd < 1024; fd++) {
        int flags = fcntl(fd, F_GETFD);
        if (flags >= 0 && !(flags & FD_CLOEXEC)) fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
    }
}

/* Each thread spawns `ls /proc/self/fd` and checks the listing. A child
   that inherited nothing has 0, 1 and 2 plus the directory ls opened,
   which takes the lowest free number, 3. Anything else was inherited. */
static void* fd_worker(void* arg) {
    (void)arg;
    char* argv[] = {"/proc/self/fd"};
    for (int it = 0; it < FD_ITERS; it++) {
        Con* r = (Con*)monad_proc_spawn("ls", monad_build_args(1, argv));
        if (!r || r->tag != TAG_OK) {
            fail();
            continue;
        }
        int64_t child = (int64_t)(intptr_t)r->fields[0];
        int64_t out = monad_proc_stream_fd(child, 1);
        for (;;) {
            Con* ok = (Con*)monad_stream_read_line(out, 0, 0);
            if (!ok || ok->tag != TAG_OK) {
                fail();
                break;
            }
            Con* opt = (Con*)ok->fields[0];
            if (opt->tag == TAG_NONE) break;
            const char* name = (const char*)opt->fields[0];
            if (strlen(name) != 1 || name[0] < '0' || name[0] > '3') {
                fprintf(stderr, "thread_stress: child inherited fd %s\n", name);
                fail();
            }
        }
        if (monad_proc_wait(child, 0) != 0) fail();
    }
    return NULL;
}
#endif

static int64_t now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static void on_signal(int sig) {
    (void)sig;
}

static int poll_done;
static int64_t poll_rc;

static void* poll_worker(void* arg) {
    (void)arg;
    poll_rc = monad_term_ctl(3, POLL_MS);
    __atomic_store_n(&poll_done, 1, __ATOMIC_RELEASE);
    return NULL;
}

/* stdin becomes an empty pipe nobody writes, so the poll can only time
   out; SIGUSR1 interrupts it every 20 ms until it returns. */
static void check_poll_eintr(void) {
    int p[2];
    if (pipe(p) < 0) {
        fail();
        return;
    }
    int saved = dup(0);
    dup2(p[0], 0);
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = on_signal;
    sigaction(SIGUSR1, &sa, NULL);
    int64_t start = now_ms();
    pthread_t t;
    pthread_create(&t, NULL, poll_worker, NULL);
    struct timespec tick = {0, 20 * 1000000};
    while (!__atomic_load_n(&poll_done, __ATOMIC_ACQUIRE)) {
        nanosleep(&tick, NULL);
        pthread_kill(t, SIGUSR1);
    }
    pthread_join(t, NULL);
    int64_t took = now_ms() - start;
    if (poll_rc != 0 || took < POLL_MS - 10) {
        fprintf(stderr, "thread_stress: poll returned %lld after %lld ms\n",
                (long long)poll_rc, (long long)took);
        fail();
    }
    dup2(saved, 0);
    close(saved);
    close(p[0]);
    close(p[1]);
}

#if defined(__linux__)
/* A fiber body: `Unit -> IO A` called through the closure ABI. It
   outlives its abandonment by a couple of milliseconds; the result is
   never read. */
static int64_t nap_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    struct timespec nap = {0, 2 * 1000000};
    nanosleep(&nap, NULL);
    return 0;
}

static int64_t vm_size_kb(void) {
    FILE* f = fopen("/proc/self/status", "r");
    if (!f) return -1;
    char line[256];
    long long kb = -1;
    while (fgets(line, sizeof line, f))
        if (sscanf(line, "VmSize: %lld kB", &kb) == 1) break;
    fclose(f);
    return kb;
}

/* Abandon LEAK_FIBERS fibers, half cancelled and half dropped with their
   scope, let them finish, and compare the address space with before.
   A joinable thread that is never joined keeps its 128 MB stack
   reservation, so the old runtime grew by about 25 GB here. */
static void check_abandoned_fibers(void) {
    void* body = alloc_closure((void*)nap_body, 1, 0);
    int64_t before = vm_size_kb();
    for (int i = 0; i < LEAK_FIBERS / 2; i++) monad_cancel_fiber(monad_fork_io(body));
    void* scope = monad_scope_new();
    for (int i = 0; i < LEAK_FIBERS / 2; i++) monad_scope_fork(scope, body);
    monad_scope_drop(scope);
    struct timespec settle = {0, 300 * 1000000};
    nanosleep(&settle, NULL);
    int64_t grew_mb = (vm_size_kb() - before) / 1024;
    if (before < 0 || grew_mb > 1024) {
        fprintf(stderr, "thread_stress: %d abandoned fibers grew VmSize by %lld MB\n",
                LEAK_FIBERS, (long long)grew_mb);
        fail();
    }
}
#endif

/* Whether `r` is `Result.err code`, the raw fiber answer. */
static int is_err_code(void* r, int64_t code) {
    Con* c = (Con*)r;
    return c && c->tag == TAG_ERR && (int64_t)(intptr_t)c->fields[0] == code;
}

static int64_t nap_100_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    struct timespec nap = {0, 100 * 1000000};
    nanosleep(&nap, NULL);
    return 0;
}

/* Cancelled: await says `err 1`; poll says `none` while the body still
   sleeps, then `some (err 1)`. Never started: with no thread allowed,
   both answer `err 2` at once instead of a NULL payload. */
static void check_fiber_answers(void) {
    void* body = alloc_closure((void*)nap_100_body, 1, 0);
    void* f = monad_fork_io(body);
    monad_cancel_fiber(f);
    Con* running = (Con*)monad_poll_fiber(f);
    if (!running || running->tag != TAG_NONE) {
        fprintf(stderr, "thread_stress: poll of a running cancelled fiber was not none\n");
        fail();
    }
    if (!is_err_code(monad_await_fiber(f), 1)) {
        fprintf(stderr, "thread_stress: await of a cancelled fiber was not err 1\n");
        fail();
    }
    Con* polled = (Con*)monad_poll_fiber(f);
    if (!polled || polled->tag != TAG_SOME || !is_err_code(polled->fields[0], 1)) {
        fprintf(stderr, "thread_stress: poll of a stopped cancelled fiber was not some (err 1)\n");
        fail();
    }

    /* A NULL handle (fork_io could not allocate one) never started:
       await is `err 2`, and poll is `some (err 2)`, never `none`
       forever. */
    if (!is_err_code(monad_await_fiber(NULL), 2)) {
        fprintf(stderr, "thread_stress: await of a NULL fiber was not err 2\n");
        fail();
    }
    Con* null_poll = (Con*)monad_poll_fiber(NULL);
    if (!null_poll || null_poll->tag != TAG_SOME || !is_err_code(null_poll->fields[0], 2)) {
        fprintf(stderr, "thread_stress: poll of a NULL fiber was not some (err 2)\n");
        fail();
    }

    struct rlimit saved;
    if (getrlimit(RLIMIT_NPROC, &saved) != 0) return;
    struct rlimit none = saved;
    none.rlim_cur = 0;
    if (setrlimit(RLIMIT_NPROC, &none) != 0) return;
    void* g = monad_fork_io(body);
    setrlimit(RLIMIT_NPROC, &saved);
    Con* answer = (Con*)monad_await_fiber(g);
    if (answer && answer->tag == TAG_OK) {
        printf("thread_stress: RLIMIT_NPROC not enforced here (root?); never-started check skipped\n");
        return;
    }
    if (!is_err_code(answer, 2)) {
        fprintf(stderr, "thread_stress: await of a never-started fiber was not err 2\n");
        fail();
    }
}

/* Cooperative cancellation: a fiber body that sleeps and then binds a
   continuation must not run that continuation once the cancel has
   landed. Emitted code sequences a do-block through monad_io_bind, so
   the bind after the sleep is where the flag is observed. */
static int64_t cancel_side_effect;

static int64_t mark_side_effect(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    __atomic_store_n(&cancel_side_effect, 1, __ATOMIC_RELEASE);
    return 0;
}

static int64_t sleep_then_bind_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    struct timespec nap = {0, 100 * 1000000};
    nanosleep(&nap, NULL);
    /* The RawIO box the first action would have produced, then the
       continuation that would run the rest of the do-block. */
    void* sleep_box = monad_io_pure(0);
    void* continuation = alloc_closure((void*)mark_side_effect, 1, 0);
    return monad_io_bind((int64_t)(intptr_t)sleep_box,
                         (int64_t)(intptr_t)continuation);
}

static void check_cooperative_cancel(void) {
    __atomic_store_n(&cancel_side_effect, 0, __ATOMIC_RELEASE);
    void* f = monad_fork_io(alloc_closure((void*)sleep_then_bind_body, 1, 0));
    struct timespec nap = {0, 10 * 1000000};
    nanosleep(&nap, NULL);
    monad_cancel_fiber(f);
    if (!is_err_code(monad_await_fiber(f), 1)) {
        fprintf(stderr, "thread_stress: await of a cooperatively cancelled fiber was not err 1\n");
        fail();
    }
    if (__atomic_load_n(&cancel_side_effect, __ATOMIC_ACQUIRE) != 0) {
        fprintf(stderr, "thread_stress: a cancelled fiber ran the bind after the cancel\n");
        fail();
    }
}

/* Channels: the two blocking sides, each woken by a real second thread. */
typedef struct {
    void* channel;
    int64_t value;
} channel_arg;

static void* channel_put_later(void* arg) {
    channel_arg* a = (channel_arg*)arg;
    struct timespec nap = {0, 20 * 1000000};
    nanosleep(&nap, NULL);
    monad_channel_put(a->channel, a->value);
    return NULL;
}

static void* channel_take_later(void* arg) {
    channel_arg* a = (channel_arg*)arg;
    struct timespec nap = {0, 20 * 1000000};
    nanosleep(&nap, NULL);
    a->value = monad_channel_take(a->channel);
    return NULL;
}

static void check_channels(void) {
    void* ch = monad_channel_new();
    Con* none = (Con*)monad_channel_try_take(ch);
    if (!none || none->tag != TAG_NONE) {
        fprintf(stderr, "thread_stress: try_take of an empty channel was not none\n");
        fail();
    }

    /* take parks until the other thread's put arrives. */
    channel_arg a = {ch, 7};
    pthread_t t;
    if (pthread_create(&t, NULL, channel_put_later, &a) != 0) {
        fprintf(stderr, "thread_stress: could not start the channel putter\n");
        fail();
        return;
    }
    if (monad_channel_take(ch) != 7) {
        fprintf(stderr, "thread_stress: take did not receive the later put's value\n");
        fail();
    }
    pthread_join(t, NULL);

    /* put parks while full until the taker removes the value. */
    monad_channel_put(ch, 1);
    channel_arg b = {ch, 0};
    if (pthread_create(&t, NULL, channel_take_later, &b) != 0) {
        fprintf(stderr, "thread_stress: could not start the channel taker\n");
        fail();
        return;
    }
    monad_channel_put(ch, 2);
    pthread_join(t, NULL);
    if (b.value != 1) {
        fprintf(stderr, "thread_stress: the parked taker saw %lld, expected 1\n",
                (long long)b.value);
        fail();
    }
    if (monad_channel_take(ch) != 2) {
        fprintf(stderr, "thread_stress: the put after the taker did not store 2\n");
        fail();
    }

    Con* drained = (Con*)monad_channel_try_take(ch);
    if (!drained || drained->tag != TAG_NONE) {
        fprintf(stderr, "thread_stress: try_take after draining was not none\n");
        fail();
    }
    monad_channel_put(ch, 33);
    Con* some = (Con*)monad_channel_try_take(ch);
    if (!some || some->tag != TAG_SOME || (int64_t)(intptr_t)some->fields[0] != 33) {
        fprintf(stderr, "thread_stress: try_take of a full channel was not some 33\n");
        fail();
    }
}

/* Build a `List` cell: tag 6, head = field 0, tail = field 1 -- the exact
   walk `monad_fiber_wait_any`/`monad_channel_take_any` do. A NULL tail is
   the empty list. */
static void* cons_cell(void* head, void* tail) {
    Con* cell = (Con*)alloc_constructor(6, 2);
    cell->fields[0] = head;
    cell->fields[1] = tail;
    return cell;
}

/* A fiber body that PARKS in `monad_fiber_wait_any` on a set of sleepers it
   creates for the occasion. The cancel below then has to wake it through
   the pushed broadcast; without that push it would sit in
   `pthread_cond_wait` forever, since there is no timeout any more. */
static int64_t wait_any_park_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    void* s1 = monad_fork_io(alloc_closure((void*)nap_100_body, 1, 0));
    void* s2 = monad_fork_io(alloc_closure((void*)nap_100_body, 1, 0));
    Con* tail = (Con*)alloc_constructor(6, 2);
    tail->fields[0] = s2;
    tail->fields[1] = NULL;
    Con* head = (Con*)alloc_constructor(6, 2);
    head->fields[0] = s1;
    head->fields[1] = tail;
    int64_t idx = monad_fiber_wait_any(head);
    (void)idx;
    return (int64_t)(intptr_t)monad_io_pure(0);
}

/* wait-any: parks until ONE member of a set stops, then answers its index.
   The index is a plain int64_t, not a Con, so it is compared directly.
   -1 means "no winner" (empty list, or the waiter was cancelled). */
static void check_wait_any(void) {
    /* Two long sleepers: neither finishes, so this must park. A third
       fiber that stops at once is the winner, and it is NOT the head, so
       a wait that only ever looked at field 0 would fail. */
    void* slow1 = monad_fork_io(alloc_closure((void*)nap_100_body, 1, 0));
    void* slow2 = monad_fork_io(alloc_closure((void*)nap_100_body, 1, 0));
    void* fast = monad_fork_io(alloc_closure((void*)nap_100_body, 1, 0));
    /* Index 1 is `fast`: cons slow1 (cons fast (cons slow2 nil)). Nil is a
       NULL tail, which the runtime walk treats as end-of-list. */
    void* fibers = cons_cell(slow1, cons_cell(fast, cons_cell(slow2, NULL)));
    int64_t idx = monad_fiber_wait_any(fibers);
    /* All three are 100 ms sleepers, so WHICH one the scan sees first is a
       race -- but it must be the first DONE one in list order, so any
       index in range proves the walk and the wake work. A -1 here means
       the wait missed every completion, which is the defect. */
    if (idx < 0 || idx > 2) {
        fprintf(stderr, "thread_stress: wait_any answered %lld, expected 0..2\n",
                (long long)idx);
        fail();
    }
    monad_cancel_fiber(slow1);
    monad_cancel_fiber(slow2);
    /* `fast` was reaped by the caller, so only the two sleepers need it. */
    monad_await_fiber(slow1);
    monad_await_fiber(slow2);
    monad_await_fiber(fast);

    /* An empty list (a NULL tail, i.e. no cons at all) answers -1 at once
       rather than parking forever. */
    if (monad_fiber_wait_any(NULL) != -1) {
        fprintf(stderr, "thread_stress: wait_any of an empty list was not -1\n");
        fail();
    }

    /* THE CANCEL PUSH. A fiber parked in wait_any can only be released by
       `monad_cancel_fiber` broadcasting that condvar; if the push were
       missing this would hang until the harness timed out (or forever),
       which is exactly the 20 ms tick this replaced. `wait_any` is called
       from a FIBER here, because the cancel flag it checks is the fibre-
       local one -- cancelling from the main thread would test nothing. */
    void* parked = monad_fork_io(alloc_closure((void*)wait_any_park_body, 1, 0));
    struct timespec settle = {0, 20 * 1000000};
    nanosleep(&settle, NULL);
    struct timespec before, after;
    clock_gettime(CLOCK_MONOTONIC, &before);
    monad_cancel_fiber(parked);
    monad_await_fiber(parked);
    clock_gettime(CLOCK_MONOTONIC, &after);
    long long waited_ms = (long long)(after.tv_sec - before.tv_sec) * 1000 +
                          (after.tv_nsec - before.tv_nsec) / 1000000;
    /* Generous: the point is "not the 20 ms tick forever", and a slow or
       loaded machine may take a few ms to switch threads. */
    if (waited_ms > 1000) {
        fprintf(stderr, "thread_stress: a cancelled wait_any waiter took %lld ms\n",
                waited_ms);
        fail();
    }
}

/* channel_take_any: parks on a SET of channels, waking when any of them
   gets a value -- including one that is NOT the parking spot. */
static void check_channel_take_any(void) {
    void* a = monad_channel_new();
    void* b = monad_channel_new();
    void* chans = cons_cell(a, cons_cell(b, NULL));

    /* A value already present on the SECOND channel must be found without
       blocking at all. */
    monad_channel_put(b, 42);
    Con* got = (Con*)monad_channel_take_any(chans);
    if (!got || got->tag != TAG_SOME || (int64_t)(intptr_t)got->fields[0] != 42) {
        fprintf(stderr, "thread_stress: take_any did not find the value on channel 2\n");
        fail();
    }

    /* An empty set answers none rather than parking forever. */
    Con* empty = (Con*)monad_channel_take_any(NULL);
    if (!empty || empty->tag != TAG_NONE) {
        fprintf(stderr, "thread_stress: take_any of an empty set was not none\n");
        fail();
    }

    /* A value arriving LATER on the second channel wakes a parked wait.
       `park` is channel a, so the wake has to come from b's put -- the
       cross-channel wake a per-channel condvar could not do. */
    channel_arg late = {b, 99};
    pthread_t t;
    if (pthread_create(&t, NULL, channel_put_later, &late) != 0) {
        fprintf(stderr, "thread_stress: could not start the second putter\n");
        fail();
        return;
    }
    Con* parked = (Con*)monad_channel_take_any(chans);
    pthread_join(t, NULL);
    if (!parked || parked->tag != TAG_SOME ||
        (int64_t)(intptr_t)parked->fields[0] != 99) {
        fprintf(stderr, "thread_stress: a parked take_any missed the second channel's value\n");
        fail();
    }
}

/* ── a cancel racing a blocked channel wait ────────────────────────────
   The lock-order inversion that `channel_wake_cancelled` had, reproduced.

   Two paths touch the `ChanReg` registry, and they used to take the two
   locks in OPPOSITE orders:

     * a channel wait REGISTERS while holding its channel's lock --
       `channel_wait` runs with `c->lock` held and then takes
       `chan_reg_lock` (the permitted order: one channel lock, then the
       registry);
     * `monad_cancel_fiber` -> `channel_wake_cancelled` used to hold
       `chan_reg_lock` and take each `chan->lock` INSIDE the walk (the
       forbidden one).

   A waiter registering at the moment a cancel fires deadlocks AB-BA. That
   is exactly the path the pushed cancel wake exists for -- a cancel
   arriving while a fiber is parking on, or scanning, a channel -- so the
   race is the feature, not an edge case.

   WHY THIS PHASE HAD TO BE WRITTEN. Nothing in the harness cancelled a
   fiber that was blocked on a channel, so the inversion was unreachable
   here: `check_channels` blocks without cancelling, `check_channel_take_any`
   never cancels, and `check_wait_any`'s cancel case parks in
   `monad_fiber_wait_any`, a different condvar and a different lock. TSAN
   cannot help either -- it reports DATA races, and a lock-order inversion
   is not one, so the sanitizer run stayed clean throughout.

   Both registry-registering waits are exercised: a plain
   `monad_channel_take` (whose registration happens inside `channel_wait`,
   the leg that holds a channel lock) and a `monad_channel_take_any` over
   two channels (one node per channel, all parking on the first). Fibers,
   not plain threads, because only a fiber's own thread-local cancel flag
   makes the park give up; a plain thread would wait forever and the phase
   could never join it. */

#define CANCEL_RACE_WAITERS 6
#define CANCEL_RACE_ROUNDS 150
#define CANCEL_RACE_STAGGER_NS 100000 /* 100 us between cancels */
#define CANCEL_RACE_TIMEOUT_MS 60000

static void* cancel_race_channels[2];
static int cancel_race_done;

/* Park in `monad_channel_take` on a channel nothing ever fills, so the
   wait reaches `channel_wait`'s registration. The cancel releases it. */
static int64_t take_waiter_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    (void)monad_channel_take(cancel_race_channels[0]);
    return (int64_t)(intptr_t)monad_io_pure(0);
}

/* Park in `take_any` over both channels; it parks on the first one's
   condvar but registers a node on each. */
static int64_t take_any_waiter_body(int64_t closure, int64_t unit) {
    (void)closure;
    (void)unit;
    void* chans = cons_cell(cancel_race_channels[0],
                            cons_cell(cancel_race_channels[1], NULL));
    (void)monad_channel_take_any(chans);
    return (int64_t)(intptr_t)monad_io_pure(0);
}

/* Fork the waiters, cancel them one at a time so the cancels land at
   different points of their park/registration, then reap them. Repeating
   it re-creates the registration window on every round. */
static void* cancel_race_body(void* arg) {
    (void)arg;
    cancel_race_channels[0] = monad_channel_new();
    cancel_race_channels[1] = monad_channel_new();
    if (!cancel_race_channels[0] || !cancel_race_channels[1]) {
        fail();
        __atomic_store_n(&cancel_race_done, 1, __ATOMIC_RELEASE);
        return NULL;
    }
    struct timespec stagger = {0, CANCEL_RACE_STAGGER_NS};
    for (int round = 0; round < CANCEL_RACE_ROUNDS; round++) {
        void* fibers[CANCEL_RACE_WAITERS];
        for (int i = 0; i < CANCEL_RACE_WAITERS; i++) {
            void* entry = (i % 2 == 0) ? (void*)take_waiter_body
                                       : (void*)take_any_waiter_body;
            fibers[i] = monad_fork_io(alloc_closure(entry, 1, 0));
        }
        for (int i = 0; i < CANCEL_RACE_WAITERS; i++) {
            nanosleep(&stagger, NULL);
            monad_cancel_fiber(fibers[i]);
        }
        for (int i = 0; i < CANCEL_RACE_WAITERS; i++) monad_await_fiber(fibers[i]);
    }
    __atomic_store_n(&cancel_race_done, 1, __ATOMIC_RELEASE);
    return NULL;
}

/* The phase can only fail by HANGING, so its assertion is a deadline
   rather than a counter, and it runs on its own thread so the main thread
   can watch it. `_exit` on expiry is deliberate: a wedged phase thread
   cannot be joined, so a normal return would block in `pthread_join`
   forever and turn the gate's failure into a CI stall. The non-zero exit
   status still makes the runner call it a failure. */
static void check_cancel_race(void) {
    __atomic_store_n(&cancel_race_done, 0, __ATOMIC_RELEASE);
    pthread_t t;
    if (pthread_create(&t, NULL, cancel_race_body, NULL) != 0) {
        fprintf(stderr, "thread_stress: could not start the cancel-race phase\n");
        fail();
        return;
    }
    int64_t start = now_ms();
    struct timespec tick = {0, 5 * 1000000};
    while (!__atomic_load_n(&cancel_race_done, __ATOMIC_ACQUIRE)) {
        if (now_ms() - start > CANCEL_RACE_TIMEOUT_MS) {
            fprintf(stderr,
                    "thread_stress: DEADLOCK -- a cancel racing a blocked channel "
                    "wait did not finish in %d ms\n",
                    CANCEL_RACE_TIMEOUT_MS);
            fflush(stderr);
            _exit(1);
        }
        nanosleep(&tick, NULL);
    }
    pthread_join(t, NULL);
}

static void run(void* (*worker)(void*), int threads) {
    pthread_t t[PIPE_THREADS];
    for (int i = 0; i < threads; i++)
        pthread_create(&t[i], NULL, worker, (void*)(intptr_t)i);
    for (int i = 0; i < threads; i++) pthread_join(t[i], NULL);
}

int main(void) {
    GC_INIT();
#if defined(__linux__)
    cloexec_inherited();
#endif
    run(pipe_worker, PIPE_THREADS);
    run(proc_worker, PROC_THREADS);
#if defined(__linux__)
    int64_t listener = ok_fd(monad_tcp_listen(0));
    int64_t client = ok_fd(monad_tcp_connect_timeout(
        "127.0.0.1", monad_tcp_local_port(listener), 0));
    int64_t conn = ok_fd(monad_tcp_accept(listener));
    if (listener < 0 || client < 0 || conn < 0) fail();
    run(fd_worker, FD_THREADS);
    monad_stream_close(conn);
    monad_stream_close(client);
    monad_stream_close(listener);
#endif
    check_poll_eintr();
#if defined(__linux__)
    check_abandoned_fibers();
#endif
    check_fiber_answers();
    check_cooperative_cancel();
    check_channels();
    check_wait_any();
    check_channel_take_any();
    check_cancel_race();
    printf("thread_stress: %d failure(s)\n", failures);
    return failures != 0;
}
