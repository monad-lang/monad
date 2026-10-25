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
 *     must still wait out its full timeout.
 *
 * It checks every line it reads, so a lost or corrupted carry is a
 * failure even without a sanitizer, and `scripts/check-runtime-threads.sh`
 * also runs it under ThreadSanitizer, which must report nothing.
 * See plans/implementations/async-runtime-thread-safety.md. */
#define GC_THREADS
#include <gc.h>
#include <pthread.h>
#include <signal.h>
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

#define PIPE_THREADS 16
#define PIPE_ITERS 300
#define PIPE_LINES 40
#define PROC_THREADS 8
#define PROC_ITERS 40
#define PROC_LINES 40
#define FD_THREADS 8
#define FD_ITERS 40
#define POLL_MS 300

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
    printf("thread_stress: %d failure(s)\n", failures);
    return failures != 0;
}
