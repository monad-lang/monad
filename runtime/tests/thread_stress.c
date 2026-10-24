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
 *     `proc_registry` slot table.
 *
 * It checks every line it reads, so a lost or corrupted carry is a
 * failure even without a sanitizer, and `scripts/check-runtime-threads.sh`
 * also runs it under ThreadSanitizer, which must report nothing.
 * See plans/implementations/async-runtime-thread-safety.md. */
#define GC_THREADS
#include <gc.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

void* monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard);
void* monad_stream_close(int64_t fd);
void* monad_proc_spawn(char* cmd, void* args);
int64_t monad_proc_stream_fd(int64_t handle, int64_t which);
int64_t monad_proc_wait(int64_t handle, int64_t kill_first);
void* monad_build_args(int argc, char** argv);

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

static void run(void* (*worker)(void*), int threads) {
    pthread_t t[PIPE_THREADS > PROC_THREADS ? PIPE_THREADS : PROC_THREADS];
    for (int i = 0; i < threads; i++)
        pthread_create(&t[i], NULL, worker, (void*)(intptr_t)i);
    for (int i = 0; i < threads; i++) pthread_join(t[i], NULL);
}

int main(void) {
    GC_INIT();
    run(pipe_worker, PIPE_THREADS);
    run(proc_worker, PROC_THREADS);
    printf("thread_stress: %d failure(s)\n", failures);
    return failures != 0;
}
