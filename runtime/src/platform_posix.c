/* POSIX platform: Boehm allocator, pthread fibers, processes, sockets,
   files, streams and the native entry point. Compiled for native only. */

/* All Monad heap objects come from here (and `monad_alloc_atomic` just
   below for pointer-free payloads). Those two functions are the ENTIRE
   extent of the garbage collector in this runtime, deliberately: the GC
   is a stopgap until the compiler tracks ownership through the linear/
   affine multiplicities the language already has, at which point these
   two bodies get real frees and the dependency goes away. See
   plans/bootstrapping/linear-types-memory.md.

   Why a collector is here at all: codegen never emits `monad_release`,
   so nothing was ever freed. Measured on `check lang/main.mo`, that
   meant 5.99 GiB allocated of which 98.24% was garbage, and `compile
   lang/main.mo` was OOM-killed at 29.7 GB. */
void* monad_alloc(size_t size) {
    void* ptr = GC_malloc(size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return ptr;
}

/* Pointer-free payloads -- string buffers. Allocated `atomic` so the
   collector does not scan their contents: it is faster, and it stops
   arbitrary text bytes from being mistaken for heap addresses and
   pinning garbage alive. */
void* monad_alloc_atomic(size_t size) {
    return GC_malloc_atomic(size);
}

void monad_retain(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    atomic_fetch_add(&h->refcount, 1);
}

void monad_release(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    /* Deliberately does NOT free: the block is GC-owned, and calling
       free() on it would corrupt the collector's heap. The refcount is
       still maintained so that the eventual linear-types work has a
       correct starting point -- at that point this regains its free. */
    atomic_fetch_sub(&h->refcount, 1);
}

/* --- Fibers and scopes (`std/concurrent/{fiber,combine}.mo`) --------

   MODEL: one OS thread per fiber, with the handle's lifetime carried by
   the `_Atomic(int64_t) refcount` every `monad_alloc`'d block already
   has. This is the explicit INTERIM the language's own ownership work
   replaces (plans/type-system/quantitative-types.md, Design B milestone
   M4: the linear `Fiber`/`Scope`) -- which is why the count is
   maintained here even though nothing reads it yet. It is deliberately
   not a scheduler: it does not scale to 100k fibers, and it needs no
   compiler-inserted yield points, the hard half of
   plans/implementations/async-threading.md's Phase 7c.

   What it buys immediately is REAL concurrency, which the Rust host's
   lazy/cooperative model cannot express at all: the host defers `forkIO`
   to `await_fiber` (core/src/core_native.rs's own "Rust Host Status"
   note), so nothing there can ever interleave. Two visible consequences,
   both deliberate:

   * `forkIO` starts the thread at fork time (eager), and `await_fiber`
     waits for it. The corpus is indifferent to the difference -- every
     `forkIO` in it is awaited, or cancelled-and-discarded -- but a test
     that *requires* interleaving can only pass here.
   * Cancellation cannot abort a running thread. `pthread_cancel` would
     leave Boehm's allocator lock held and the thread unregistered, so
     `monad_cancel_fiber` records the cancellation instead (which
     `await_fiber` then refuses to hand a result for, matching the host's
     error) and does not preempt the body. The host can only ever cancel
     a fiber it has NOT started, so this is the same observable behaviour
     on everything the language can currently express.

   HANDLES ARE NOT CONSTRUCTORS, deliberately. A `Fiber`/`Scope` value is
   the raw struct pointer, marked `MONAD_FIBER_TAG`/`MONAD_SCOPE_TAG` in
   `Header.tag` -- the allocation-KIND slot at offset 8, as for every other
   allocation here (1 Closure, 2 Constructor, 3 String). A Constructor's
   own tag is a DIFFERENT slot, offset 16, and that is the one
   `monad_get_tag` must not read blindly for a handle: at offset 16 a
   `Fiber` holds its `action` pointer, so the read would hand match
   dispatch the low half of a heap address. `monad_get_tag` therefore
   consults the kind slot first and reports 17/18 for a handle -- a value
   no constructor tag can collide with, so a `match` on a handle fails
   loudly instead of taking an arbitrary arm. The Rust host takes the same
   route for these exact two types: its
   `handle_value`/`extract_handle_id` are a non-`Con` representation
   precisely so a handle is never mistaken for a constructor.

   THREADS AND BOEHM: see the GC_THREADS comment at the head of this
   file. Every thread here is created via `pthread_create`, which under
   GC_THREADS IS `GC_pthread_create`, and is joined exactly once by
   whoever reaps it (`GC_pthread_join`, which also drops the collector's
   per-thread bookkeeping). A fiber nobody ever awaits or cancels keeps
   its thread entry until the process exits; that is a few hundred bytes
   per abandoned fiber, and reclaiming it would mean joining threads
   whose result nobody wants, i.e. blocking `scope_drop` on work the
   program has explicitly walked away from. */

/* MONAD_FIBER_TAG / MONAD_SCOPE_TAG are defined with the other `Header.tag`
   kind values at the head of this file; `monad_get_tag` needs them before
   the fiber code does. */
/* The stack every thread that runs compiled Monad code is created with,
   `main` included -- see its trampoline below. A fiber body can recurse
   exactly as deeply as `main` can, so the plan doc's original 8 KB
   ucontext stack would overflow on the first recursive helper. The
   reservation is ADDRESS space, committed on demand, so a thread that
   does not recurse deeply never pays for it in RSS -- and an awaited
   fiber's stack is unmapped again by the join. */
#define MONAD_DEEP_STACK_BYTES ((size_t)128 * 1024 * 1024)

typedef struct {
    Header header;
    void* action;      /* the `Unit -> IO A` closure, until the thread runs */
    int64_t state;     /* 0 while the thread runs, 1 once it has stopped */
    int64_t cancelled; /* set by monad_cancel_fiber; see this section's own
                          doc comment for why it cannot preempt */
    int64_t io_box;    /* the action's own result: an `IO A`, i.e. a complete
                          `IO.mk (RawIO.io _)` box */
    int64_t reaped;    /* 1 once the thread has been joined */
    int64_t started;   /* 1 once a thread exists TO join: a refused
                          pthread_create leaves `thread` unwritten, and
                          pthread_join faults on that value, so the join is
                          guarded on this rather than on the handle being
                          non-NULL */
    int64_t released;  /* 1 once the WORKER's retain (monad_fork_io) has been
                          released. Held apart from `reaped` on purpose:
                          monad_cancel_fiber consumes the reference without
                          reaping, and a later `await` must still join the
                          thread the cancel left running. The scope's own
                          reference (monad_scope_fork) is a different one,
                          released unconditionally by monad_scope_drop. */
    pthread_t thread;
    pthread_mutex_t lock;
    pthread_cond_t finished;
} Fiber;

typedef struct ScopeNode {
    struct ScopeNode* next;
    void* fiber; /* retained -- see monad_scope_fork */
} ScopeNode;

typedef struct {
    Header header;
    /* Guards `fibers`. A scope can be forked from inside a fiber (that is
       what `scoped`'s own callback does), so this is real concurrency and
       not just cross-test bookkeeping. */
    pthread_mutex_t lock;
    ScopeNode* fibers;
} Scope;

/* Everything a fiber does to its own handle goes through `lock`, so
   `state`/`cancelled`/`io_box` need no atomics of their own: the mutex's
   release/acquire pair is the happens-before edge, and it is a stronger
   one than a bare atomic store. The genuinely atomic thing here is the
   Header's refcount, which monad_retain/monad_release already maintain
   with atomic_fetch_add/sub. */
static void fiber_mark_cancelled(Fiber* f) {
    pthread_mutex_lock(&f->lock);
    /* Only a fiber that has NOT finished. The host's `Fiber::cancel`
       transitions Pending -> Cancelled and is a no-op otherwise, so
       cancelling a completed fiber must not throw away a result that was
       already in hand. `state` is published under this same lock by
       fiber_main, so the test cannot race the completion it is testing
       for. */
    if (!f->state) f->cancelled = 1;
    pthread_mutex_unlock(&f->lock);
}

/* Runs the fiber's action, then publishes its result. `arg` is the fiber
   itself. Not detached: monad_await_fiber is what joins it. */
static void* fiber_main(void* arg) {
    Fiber* f = (Fiber*)arg;
    /* Unit.unit is tag 0, arity 0 -- `builtin_ctor_tags`
       (lang/src/codegen/ctors.mo) pins it, and it is the same value
       monad_array_set_in_place returns for its own `IO Unit`. */
    void* unit = alloc_constructor_impl(0, 0);
    int64_t box = apply_closure1_impl(f->action, (int64_t)(intptr_t)unit);
    pthread_mutex_lock(&f->lock);
    f->io_box = box;
    f->state = 1;
    pthread_cond_broadcast(&f->finished);
    pthread_mutex_unlock(&f->lock);
    return NULL;
}

void* monad_fork_io(void* closure) {
    Fiber* f = (Fiber*)monad_alloc(sizeof(Fiber));
    if (!f) return NULL;
    f->header.tag = MONAD_FIBER_TAG;
    f->action = closure;
    f->state = 0;
    f->cancelled = 0;
    f->io_box = 0;
    f->reaped = 0;
    f->started = 0;
    f->released = 0;
    pthread_mutex_init(&f->lock, NULL);
    pthread_cond_init(&f->finished, NULL);
    /* The worker's own reference, released by whoever consumes the
       handle (await or cancel). Boehm's reachability is what actually
       keeps the block alive today -- the caller holds the pointer too --
       so this is the ownership handoff M4's linear `Fiber` needs, not a
       liveness guard. */
    monad_retain(f);
    pthread_attr_t attr;
    int rc = pthread_attr_init(&attr);
    if (rc == 0) {
        pthread_attr_setstacksize(&attr, MONAD_DEEP_STACK_BYTES);
        rc = pthread_create(&f->thread, &attr, fiber_main, f);
        if (rc != 0) {
            /* The 128 MB reservation can be refused (thread-count or
               address-space limits). Retry on the default stack: a fiber
               on a small stack beats no fiber. */
            pthread_attr_destroy(&attr);
            pthread_attr_init(&attr);
            rc = pthread_create(&f->thread, &attr, fiber_main, f);
        }
        pthread_attr_destroy(&attr);
    }
    if (rc != 0) {
        /* No thread at all. Publish an already-finished state rather than
           leaving a handle that can never become ready: a hang is
           strictly worse than a NULL payload, because nothing in this
           backend can raise an error out of a native. `started` stays 0,
           so the await does not try to join the thread that was never
           created -- pthread_join faults on that value (it dereferences
           the thread descriptor), which would turn this deliberately
           degraded path into a crash of the whole process instead. */
        f->state = 1;
        f->io_box = 0;
    } else {
        f->started = 1;
    }
    return f;
}

void* monad_await_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    if (!f) return NULL;
    pthread_mutex_lock(&f->lock);
    while (!f->state) pthread_cond_wait(&f->finished, &f->lock);
    int64_t cancelled = f->cancelled;
    int64_t box = f->io_box;
    int reap = !f->reaped;
    f->reaped = 1;
    int release = !f->released;
    f->released = 1;
    pthread_mutex_unlock(&f->lock);
    /* Exactly one awaiter joins, and only when fork_io actually created a
       thread. A second `await` on the same handle still reads the stored
       result rather than joining an already-joined thread (pthread_join
       twice is undefined). */
    if (reap && f->started) pthread_join(f->thread, NULL);
    /* The worker's reference is released exactly once, by whichever of
       await/cancel consumes the handle first: releasing once per await
       would drive the count negative on a repeated await, which is
       precisely the ownership the count exists to hand to M4. */
    if (release) monad_release(f);
    if (cancelled) {
        /* The host's `await_fiber` is an eval ERROR here ("fiber {id} was
           cancelled"). This backend has no error channel out of a native,
           so the closest honest thing is a diagnostic plus a well-formed
           box around a NULL payload: the value is wrong, and it is wrong
           out loud. Nothing in the corpus can reach it -- `race` cancels
           every fiber it does NOT then await. The box is built out in full
           here rather than left to the codegen, because this native is
           `passthrough` now (see below) and the backend adds no layer. */
        fprintf(stderr, "monad: await_fiber on a cancelled fiber\n");
        void* raw_io = alloc_constructor_impl(7, 1);
        monad_set_field_impl(raw_io, 0, NULL);
        void* io_mk = alloc_constructor_impl(MONAD_IO_MK_TAG, 1);
        monad_set_field_impl(io_mk, 0, raw_io);
        return io_mk;
    }
    /* `f->io_box` holds the ACTION's own result, which is typed `IO A`
       (`std/src/concurrent/fiber.mo`) and is therefore already a complete
       `IO.mk (RawIO.io _)` box -- see that field's own comment. Return it
       unchanged: this native is `NativeWrapKind.passthrough` in
       `lang/src/codegen/natives.mo`, so the backend wraps nothing, exactly
       like the Rust host's `await_fiber` (`core/src/core_native.rs`).
       Peeling field 0 here was right for the single-layer
       `type IO A { io A }` and became wrong the moment `IO` gained its
       `RawIO` wrapper: one peel of a two-layer box left the inner
       `RawIO.io A` and, once the wrapper re-wrapped it, made this return
       `IO (RawIO A)`. */
    return (void*)(intptr_t)box;
}

/* `#[native "poll_fiber"]` (std/concurrent/fiber.mo's pollFiber) --
   `Fiber A -> IO (Option A)`, await's non-blocking sibling: `none` while
   the fiber still runs, `some a` exactly once once it has stopped, wired
   `io_passthrough` in natives.mo like `monad_get_env` (the raw result is
   already a valid backend value -- a real `Option` Constructor,
   some=4/none=3 -- so the emitted wrapper only IO.io-wraps it).

   The state check comes FIRST, before the cancelled flag: cancellation
   cannot preempt (`fiber_mark_cancelled`'s comment), so a cancelled
   fiber may still be RUNNING -- and poll's contract for a running fiber
   is `none`, not await's tail (running the tail here would pthread_join
   a live thread, which blocks). The loud cancellation answer comes when
   the fiber has actually stopped -- the same point await answers, so a
   poll loop on an abandoned fiber still terminates. A fork-failure
   fiber (`state = 1, io_box = 0, started = 0`, monad_fork_io's refusal
   path) is answerable the same way: loud, never silent.

   Everything after the lock/unlock is monad_await_fiber's tail verbatim:
   state is 1 at this point (checked under this same lock), so the
   condvar wait await needs is deliberately absent and the
   pthread_join -- guarded on `started` exactly as there -- is
   unconditionally safe. */
void* monad_poll_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    if (!f) return (void*)alloc_constructor_impl(3, 0);     /* Option.none */
    pthread_mutex_lock(&f->lock);
    if (!f->state) {
        pthread_mutex_unlock(&f->lock);
        return (void*)alloc_constructor_impl(3, 0);         /* Option.none */
    }
    int64_t cancelled = f->cancelled;
    int64_t box = f->io_box;
    int reap = !f->reaped;
    f->reaped = 1;
    int release = !f->released;
    f->released = 1;
    pthread_mutex_unlock(&f->lock);
    if (reap && f->started) pthread_join(f->thread, NULL);
    if (release) monad_release(f);
    /* await's cancelled branch, mirrored: no error channel out of a
       native, so the honest thing is the diagnostic plus a well-formed
       `some` around a payload that is NOT a real value. Destructuring it
       reads a NULL field; nothing in the corpus does (the host's
       `poll_fiber` raises the eval error this cannot). */
    if (cancelled) {
        fprintf(stderr, "monad: poll_fiber on a cancelled fiber\n");
        Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
        some->fields[0] = NULL;
        return some;
    }
    if (!box) {
        fprintf(stderr, "monad: poll_fiber on a fiber that never started (fork failure)\n");
        Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
        some->fields[0] = NULL;
        return some;
    }
    /* `box` is the action's own result, typed `IO A` -- a complete
       `IO.mk (RawIO.io a)` box. Peeling ONE layer of exactly this box
       was await's past bug (its own comment): the result would have read
       as `IO (RawIO A)`. poll's contract is `Option A`, so peel BOTH
       layers here to reach `a` before wrapping it in `Option.some`. */
    void* inner = monad_get_field_impl(monad_get_field_impl((void*)(intptr_t)box, 0), 0);
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
    some->fields[0] = inner;
    return some;
}

void* monad_cancel_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    if (f) {
        fiber_mark_cancelled(f);
        /* Consuming the handle releases the worker's reference -- but only
           once. A handle that was awaited before it was cancelled has
           already released it, and `monad_scope_drop`'s release is the
           scope's separate reference, not this one. */
        pthread_mutex_lock(&f->lock);
        int64_t consume = !f->released;
        f->released = 1;
        pthread_mutex_unlock(&f->lock);
        if (consume) monad_release(f);
    }
    return alloc_constructor_impl(0, 0);
}

void* monad_sleep_io(int64_t ms) {
    if (ms > 0) {
        struct timespec ts;
        ts.tv_sec = ms / 1000;
        ts.tv_nsec = (ms % 1000) * 1000000;
        /* nanosleep, not usleep: usleep is obsolete and rejects >= 1s.
           Resuming with the remainder on EINTR matches the host, which
           simply sleeps. A negative `ms` sleeps not at all -- the host's
           own `ms.max(0)`. The loop retries ONLY on EINTR: any other
           failure (EINVAL, a bad timespec) is permanent, and retrying it
           would turn a failed sleep into an unkillable spin. */
        while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {
        }
    }
    return alloc_constructor_impl(0, 0);
}

void* monad_scope_new(void) {
    Scope* s = (Scope*)monad_alloc(sizeof(Scope));
    if (!s) return NULL;
    s->header.tag = MONAD_SCOPE_TAG;
    pthread_mutex_init(&s->lock, NULL);
    s->fibers = NULL;
    return s;
}

void* monad_scope_fork(void* handle, void* closure) {
    Scope* s = (Scope*)handle;
    void* fiber = monad_fork_io(closure);
    if (!s || !fiber) return fiber;
    ScopeNode* node = (ScopeNode*)monad_alloc(sizeof(ScopeNode));
    if (!node) return fiber;
    node->fiber = fiber;
    monad_retain(fiber);
    pthread_mutex_lock(&s->lock);
    node->next = s->fibers;
    s->fibers = node;
    pthread_mutex_unlock(&s->lock);
    return fiber;
}

void* monad_scope_drop(void* handle) {
    Scope* s = (Scope*)handle;
    if (s) {
        pthread_mutex_lock(&s->lock);
        ScopeNode* node = s->fibers;
        s->fibers = NULL;
        pthread_mutex_unlock(&s->lock);
        /* Cancels, but does NOT wait: the host's `scope_drop` cancels
           outstanding fibers and returns, so a `scoped` block that walks
           away from a long-running fiber must not block here either. The
           fibers keep running to completion in the background; only the
           scope's claim on them is given up. */
        while (node) {
            ScopeNode* next = node->next;
            Fiber* f = (Fiber*)node->fiber;
            if (f) {
                fiber_mark_cancelled(f);
                monad_release(f);
            }
            node = next;
        }
    }
    return alloc_constructor_impl(0, 0);
}

/* SIGPIPE back to its default action. `sigaction` rather than `signal`
   because the fork children below call this between `fork` and `exec`,
   where a multithreaded process may only use async-signal-safe calls. */
static void sigpipe_default(void) {
    struct sigaction sa = {0};
    sa.sa_handler = SIG_DFL;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGPIPE, &sa, NULL);
}

/* `main` ignores SIGPIPE so a write to a vanished pipe or socket peer is
   an EPIPE the caller sees. For the process's OWN stdout/stderr that
   would be a regression: no stdio write here checks its result, so
   `prog | head` would keep producing output into nothing (an endless
   printer never stops) where it used to die of SIGPIPE. Every stdio
   writer therefore passes its result through this, and an EPIPE dies
   the way it always did -- by the signal, exit status 141. */
static void stdio_die_on_epipe(int failed) {
    if (failed && errno == EPIPE) {
        sigpipe_default();
        raise(SIGPIPE);
    }
}

/* BOOTSTRAP SHIM, not a native: nothing in this tree declares or calls
   it. `IO.println` is ordinary Monad over `std/stream.mo` now, but a
   host compiler built before that change (the published nightly, an
   older rung) still inlines every `println` call to this symbol through
   its `native_op_table` key, and links the CHECKOUT's runtime -- so
   without it such a host cannot build this tree. Delete it once a
   nightly without the key is the oldest host anyone builds with
   (io-streams plan, Phase 6). */
void monad_print_str(char* s) {
    if (s) {
        errno = 0;
        stdio_die_on_epipe(printf("%s\n", s) < 0);
    }
}
char* monad_file_exists(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (f) { fclose(f); return (char*)"1"; }
    return NULL;
}

/* Same truthy-pointer convention as monad_file_exists above (a non-NULL
   return means true, NULL means false) -- IO.is_dir (init/io.mo, moved
   to std/io.mo) needs the identical shape. */
char* monad_is_dir(char* path) {
    if (!path) return NULL;
    struct stat st;
    if (stat(path, &st) != 0) return NULL;
    return S_ISDIR(st.st_mode) ? (char*)"1" : NULL;
}


/* A NULL-terminated argv for `execvp(cmd, argv)`: argv[0] = cmd, then one
 * entry per `List String` cons cell (tag 6: head field 0, tail field 1),
 * then NULL. malloc'd, never GC'd -- the callers free it (or, in
 * `monad_proc_spawn`'s child half, the `_exit` makes that moot). Shared
 * by `monad_exec_cmd` and `monad_proc_spawn`, which used to carry two
 * verbatim copies of the same two-pass walk (count, then fill). Returns
 * NULL only on malloc failure. */
static char** monad_build_argv(char* cmd, void* args) {
    int64_t argc = 0;
    for (void* cur = args; cur && monad_get_tag_impl(cur) == 6; ) {
        argc++;
        cur = monad_get_field_impl(cur, 1);
    }
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) return NULL;
    argv[0] = cmd;
    int64_t i = 1;
    for (void* cur = args; cur && monad_get_tag_impl(cur) == 6; ) {
        argv[i++] = (char*)monad_get_field_impl(cur, 0);
        cur = monad_get_field_impl(cur, 1);
    }
    argv[i] = NULL;
    return argv;
}

/* `#[native "exec_cmd"]` (std/process.mo, `exec_cmd : String -> List
   String -> IO I64`). THE load-bearing native for the bootstrap ladder:
   lang/codegen/link.mo shells out to `llc` and `clang` through this, so
   without it a self-compiled compiler can never run its own `compile`
   command at all.

   Walks the `List String` cons chain into a NULL-terminated argv (with
   the command itself as argv[0], as execvp requires), then
   fork + execvp + waitpid. Returns the child's exit code, or -1 if the
   command could not be spawned or died on a signal -- matching the
   reference's `status.code().unwrap_or(-1)`. The wrapper
   (native_runtime_fn_name's io_passthrough kind) does the IO boxing. */
int64_t monad_exec_cmd(char* cmd, void* args) {
    char** argv = monad_build_argv(cmd, args);
    if (!argv) return -1;

    /* The child inherits this process's stdout. When that stdout is a
       pipe or a file rather than a terminal, libc block-buffers it, so
       anything this process has printed but not yet flushed would be
       written AFTER the child's own output -- which made `monad test`
       print each file's "[i/n] Testing ..." header below the results it
       introduces. Flush before forking so the interleaving matches the
       order the writes were made in. */
    fflush(NULL);

    pid_t pid = fork();
    if (pid < 0) { free(argv); return -1; }
    if (pid == 0) {
        sigpipe_default(); /* see `main`: SIG_IGN would survive exec */
        execvp(cmd, argv);
        _exit(127);            /* exec failed -- conventional shell code */
    }
    int status = 0;
    free(argv);
    if (waitpid(pid, &status, 0) < 0) return -1;
    return WIFEXITED(status) ? (int64_t)WEXITSTATUS(status) : -1;
}

/* The runtime's Result-value helpers, shared by the tcp section below
   and the byte streams -- the `tcp_` names predate the second user.
   `Result.ok` is tag 10 and `Unit.unit` tag 0 --
   `lang/src/codegen/ctors.mo`'s fixed prelude tags, the same table the
   generated `rt_tag_*` helpers mirror. The ok field holds a raw word,
   so one `tcp_ok` serves an fd, a byte count, a child slot and a
   `List U8` pointer alike. */
static void* tcp_ok(void* payload) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = payload;
    return ok;
}

/* `Unit.unit` (tag 0). The nullary cache makes this the same instance
   every call. */
static void* tcp_unit(void) {
    return alloc_constructor_impl(0, 0);
}

/* ── Piped subprocesses (std/process.mo, agent-skills.md Phase 4) ──────
 *
 * `monad_exec_cmd` waits and returns a status; the MCP client's stdio
 * transport needs a child that STAYS alive between native calls --
 * write its stdin, read its stdout a line at a time, keep stderr
 * separate, kill it. Each live child therefore lives in the registry
 * below and the `Child` value Monad holds is the 1-based slot index
 * (never a constructor -- `FdStream`'s own trick, in the same file).
 * The Rust host keeps its own registry in `core_native.rs`; the two
 * agree on the surface (`std/src/process.mo`), not on handle values,
 * which are opaque and never cross a process boundary.
 *
 * Three natives: spawn, wait, and `monad_proc_stream_fd`, which hands
 * out a pipe descriptor so `std/stream.mo`'s read/write do the rest.
 *
 * No lock: this registry is only ever touched from the one thread that
 * drives the interpreter loop, the same assumption `monad_exec_cmd`'s
 * own fork already makes. */
#define MONAD_PROC_MAX 64

typedef struct {
    pid_t pid;
    int in_fd;   /* parent's write end of the child's stdin */
    int out_fd;  /* parent's read end of the child's stdout */
    int err_fd;  /* parent's read end of the child's stderr */
    int live;
} ProcChild;

static ProcChild proc_registry[MONAD_PROC_MAX];

static ProcChild* proc_slot(int64_t handle) {
    if (handle < 1 || handle > MONAD_PROC_MAX) return NULL;
    ProcChild* pc = &proc_registry[handle - 1];
    return pc->live ? pc : NULL;
}

/* Defined with the byte streams further down; `monad_proc_spawn` reports
   `Result.err (Pair.pair <kind code> <message>)` like every other
   stream operation, which is what `std/src/process.mo`'s `stream_result`
   decodes. */
static void* stream_err(int64_t kind, const char* a, const char* b, int errnum);
static void* stream_os_err(const char* op, int errnum);
/* Defined with the line reader below: drops a closed descriptor's
   read-ahead so a reused fd cannot inherit it. */
static void stream_carry_clear(int fd);

/* `proc_spawn : String -> List String -> RawIO (Result (Pair I64 String)
 * Child)` -- argv via `monad_build_argv` (the same builder
 * `monad_exec_cmd` uses), then TWO pipes per stream direction: stdin's
 * parent end is a WRITE fd, stdout's and stderr's are READ fds, and
 * stdout/stderr never merge (the opposite of `Proc.capture`'s merged
 * `2>&1`, which is right for a toolchain probe and wrong for a protocol
 * stream -- a server's stderr log line must not land inside the
 * JSON-RPC framing).
 *
 * The natives in this section return the RAW payload (a `Result`/
 * `I64`); the `raw_io_passthrough` wrapper emitted by codegen wraps it
 * once as `RawIO.io`, and the `.mo` wrappers in std/process.mo build the
 * user-facing `IO` type on top. Reads and writes are not natives at all:
 * `monad_proc_stream_fd` hands out the descriptor and the byte-stream
 * natives do the work.
 *
 * EXEC FAILURE IS AN ERROR, not a child that exits 127: a fourth pipe,
 * both ends `O_CLOEXEC`, is the handshake. The child writes one errno
 * byte only if `execvp` fails and exits; a SUCCESSFUL exec closes the
 * write end automatically, so the parent's single `read` answers EOF
 * ("running") or one byte ("could not run, and why") -- the same
 * `Result.err` the Rust host's `Command::spawn` already reports, which
 * is the contract `std/src/process.mo` declares. */
void* monad_proc_spawn(char* cmd, void* args) {
    char** argv = monad_build_argv(cmd, args);
    if (!argv) return stream_err(9, "proc_spawn", "out of memory", 0);

    int in_pipe[2], out_pipe[2], err_pipe[2];
    if (pipe(in_pipe) < 0) {
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    if (pipe(out_pipe) < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    if (pipe(err_pipe) < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    int status_pipe[2];
    if (pipe(status_pipe) < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        close(err_pipe[0]); close(err_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    /* FD_CLOEXEC by hand rather than pipe2(2): this file defines no
     * _GNU_SOURCE, and both ends must close on a successful exec for
     * the one-read handshake below to work. */
    fcntl(status_pipe[0], F_SETFD, FD_CLOEXEC);
    fcntl(status_pipe[1], F_SETFD, FD_CLOEXEC);

    fflush(NULL); /* same ordering concern as `monad_exec_cmd` */

    pid_t pid = fork();
    if (pid < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        close(err_pipe[0]); close(err_pipe[1]);
        close(status_pipe[0]); close(status_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    if (pid == 0) {
        dup2(in_pipe[0], 0);
        dup2(out_pipe[1], 1);
        dup2(err_pipe[1], 2);
        close(in_pipe[0]); close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        close(err_pipe[0]); close(err_pipe[1]);
        close(status_pipe[0]);
        sigpipe_default(); /* see `main`: SIG_IGN would survive exec */
        execvp(cmd, argv);
        unsigned char exec_errno = (errno > 0 && errno < 256) ? (unsigned char)errno : 127;
        ssize_t ignored = write(status_pipe[1], &exec_errno, 1);
        (void)ignored;
        _exit(127); /* exec failed -- conventional shell code */
    }
    free(argv);
    close(in_pipe[0]);
    close(out_pipe[1]);
    close(err_pipe[1]);
    close(status_pipe[1]);

    /* The exec verdict: EOF is success (the CLOEXEC write end died with
     * the exec), one byte is the errno of a spawn that never happened.
     * A failed spawn leaves no registry entry and no fds -- the child
     * is reaped before the error is returned, so nothing leaks. */
    unsigned char exec_errno = 0;
    ssize_t n;
    do {
        n = read(status_pipe[0], &exec_errno, 1);
    } while (n < 0 && errno == EINTR);
    close(status_pipe[0]);
    if (n == 1) {
        close(in_pipe[1]); close(out_pipe[0]); close(err_pipe[0]);
        waitpid(pid, NULL, 0);
        return stream_os_err("proc_spawn", exec_errno);
    }

    int slot = -1;
    for (int k = 0; k < MONAD_PROC_MAX; k++) {
        if (!proc_registry[k].live) { slot = k; break; }
    }
    if (slot < 0) {
        /* Refuse rather than hand back a child nobody could ever reap:
         * the registry's size is the bound on leaked children, and a
         * spawn that cannot be recorded is torn down on the spot. */
        kill(pid, SIGKILL);
        close(in_pipe[1]); close(out_pipe[0]); close(err_pipe[0]);
        waitpid(pid, NULL, 0);
        return stream_err(9, "proc_spawn", "child registry full", 0);
    }
    proc_registry[slot].pid = pid;
    proc_registry[slot].in_fd = in_pipe[1];
    proc_registry[slot].out_fd = out_pipe[0];
    proc_registry[slot].err_fd = err_pipe[0];
    proc_registry[slot].live = 1;
    return tcp_ok((void*)(int64_t)(slot + 1));
}

/* `proc_stream_fd : Child -> I64 -> RawIO FdStream` -- the descriptor
 * of one of the child's pipes: 0 = stdin (the parent's write end),
 * 1 = stdout (read end), 2 = stderr (read end). Compiled, an `FdStream`
 * IS the fd, so no registry entry is involved: `monad_stream_read` /
 * `monad_stream_write` do the I/O, which is why the old
 * `monad_proc_write`/`monad_proc_read` loops are gone.
 *
 * -1 for a dead child or an out-of-range flag (the Rust host returns
 * the same, and the `.mo` side turns a read or write on it into the
 * `Bad file descriptor` `StreamError`).
 *
 * NEVER close this view: `monad_stream_close` would close the child's
 * pipe, and `monad_proc_wait` closes all three itself. `proc_stream_fd`
 * is private to `std/process.mo`, which never closes a view. */
int64_t monad_proc_stream_fd(int64_t handle, int64_t which) {
    ProcChild* pc = proc_slot(handle);
    if (!pc) return -1;
    if (which == 0) return pc->in_fd;
    if (which == 1) return pc->out_fd;
    if (which == 2) return pc->err_fd;
    return -1;
}

/* `proc_wait : Child -> I64 -> RawIO I64` -- close the pipes, free the
 * slot (the handle dies with the child; a stale handle may alias a later
 * child, so nothing may use one after `wait`), reap, and return
 * `WEXITSTATUS` or -1 on a signal -- `monad_exec_cmd`'s convention.
 * With `kill_first` set, SIGKILL the child FIRST, so one call is the
 * whole "kill, then reap" teardown a mounted server's disposer needs
 * (the former separate `proc_kill` never reaped, which left every
 * caller hand-rolling the same kill-then-wait pair). Killing an
 * already-exited child is not an error either way -- a disposer must
 * be idempotent -- and the child is reaped before the slot is freed, so
 * the pid cannot have been recycled. */
int64_t monad_proc_wait(int64_t handle, int64_t kill_first) {
    ProcChild* pc = proc_slot(handle);
    if (!pc) return -1;
    if (kill_first) kill(pc->pid, SIGKILL);
    stream_carry_clear(pc->in_fd);
    stream_carry_clear(pc->out_fd);
    stream_carry_clear(pc->err_fd);
    close(pc->in_fd);
    close(pc->out_fd);
    close(pc->err_fd);
    pc->live = 0;
    pid_t pid = pc->pid;
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    return WIFEXITED(status) ? (int64_t)WEXITSTATUS(status) : -1;
}

/* `term_ctl : I64 -> I64 -> RawIO I64` (motes/tui/src/terminal.mo) --
 * the tui mote's ONE terminal-control native, the same
 * one-entry-point-one-flag merge `monad_proc_wait`/`monad_proc_stream_fd`
 * set: op 0 enters cbreak on stdin (ICANON, ECHO and ISIG off -- ISIG
 * too, so Ctrl-C is delivered to the app as a \x03 byte for the tui
 * app's double-press exit instead of SIGINT-killing the process;
 * OPOST stays on so a plain "\n" still prints), op 1 restores the
 * mode op 0 saved, op 2 returns the
 * size packed as rows*65536+cols, op 3 polls stdin (the second
 * argument is the timeout; the mode/size ops ignore it).
 * The mode ops answer 1/0 rather than failing -- stdin away from a tty
 * (a test run, a pipe) degrades to 0, so nothing here ever needs a pty.
 * `raw_io_passthrough` types the call's result as i64 and wraps it once
 * as `RawIO.io`; the `Terminal.*` wrappers add the `IO.mk`. */
static struct termios g_term_ctl_saved;
static int g_term_ctl_saved_valid = 0;

static int64_t term_ctl_enter_raw(void) {
    struct termios t;
    if (tcgetattr(STDIN_FILENO, &t) != 0) return 0;
    /* First entry wins: a nested enter-leave-enter sequence must still
     * restore the ORIGINAL mode, not the intermediate one. */
    if (!g_term_ctl_saved_valid) {
        g_term_ctl_saved = t;
        g_term_ctl_saved_valid = 1;
    }
    t.c_lflag &= ~(tcflag_t)(ICANON | ECHO | ISIG);
    t.c_cc[VMIN] = 1;
    t.c_cc[VTIME] = 0;
    return tcsetattr(STDIN_FILENO, TCSAFLUSH, &t) == 0 ? 1 : 0;
}

static int64_t term_ctl_leave_raw(void) {
    if (!g_term_ctl_saved_valid) return 0;
    g_term_ctl_saved_valid = 0;
    return tcsetattr(STDIN_FILENO, TCSAFLUSH, &g_term_ctl_saved) == 0 ? 1 : 0;
}

static int term_ctl_size_fd(int fd, int64_t* packed) {
    struct winsize ws;
    if (ioctl(fd, TIOCGWINSZ, &ws) != 0) return 0;
    if (ws.ws_row == 0 || ws.ws_col == 0) return 0;
    *packed = (int64_t)ws.ws_row * 65536 + (int64_t)ws.ws_col;
    return 1;
}

static int64_t term_ctl_size(void) {
    int64_t packed = 0;
    /* stdin first, then stdout: a piped-stdin program still owns the
     * terminal its output goes to. */
    if (term_ctl_size_fd(STDIN_FILENO, &packed)) return packed;
    if (term_ctl_size_fd(STDOUT_FILENO, &packed)) return packed;
    const char* cols_env = getenv("COLUMNS");
    const char* rows_env = getenv("LINES");
    if (cols_env && rows_env) {
        int64_t cols = atol(cols_env);
        int64_t rows = atol(rows_env);
        if (cols > 0 && rows > 0) return rows * 65536 + cols;
    }
    return 24 * 65536 + 80;
}

/* `term_ctl` op 3 -- poll(2) stdin for up to `timeout_ms`: 1 readable
 * (EOF counts as readable; the READ is what reports closure), 0 timed
 * out, -1 the poll itself failed. The frame clock a TUI loop rides on:
 * there is no sleep-with-wakeup primitive, so "input timed out" IS the
 * tick. poll(2)'s own convention: a negative timeout blocks
 * indefinitely -- that is how an app opts out of ticks. Positive
 * waits are clamped into poll(2)'s int range, matching the Rust host. */
static int64_t term_ctl_poll(int64_t timeout_ms) {
    struct pollfd pfd;
    pfd.fd = STDIN_FILENO;
    pfd.events = POLLIN;
    int t;
    if (timeout_ms < 0) t = -1;
    else if (timeout_ms > INT_MAX) t = INT_MAX;
    else t = (int)timeout_ms;
    int rc = poll(&pfd, 1, t);
    if (rc < 0) return -1;
    return rc == 0 ? 0 : 1;
}

int64_t monad_term_ctl(int64_t op, int64_t arg) {
    if (op == 0) return term_ctl_enter_raw();
    if (op == 1) return term_ctl_leave_raw();
    if (op == 2) return term_ctl_size();
    if (op == 3) return term_ctl_poll(arg);
    return -1;
}

/* `#[native "current_time"]` (std/io.mo's `IO.current_time`, which
   std/bench.mo's `Bench.now` defers to) -- milliseconds from an
   arbitrary fixed origin. CLOCK_MONOTONIC, so a span is never negative
   across a wall-clock adjustment; only DIFFERENCES between two readings
   mean anything.

   Every `--verbose` timing a compiled binary prints comes from here.
   They used to read "0ms" throughout, when this was a generated stub
   that ignored its arguments and returned a constant. */
int64_t monad_current_time(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + (int64_t)ts.tv_nsec / 1000000;
}

/* `#[native current_time_nano]` (std/io.mo's `IO.current_time_nano`) --
   the same monotonic clock as `monad_current_time` above, read at full
   resolution and handed over RAW. No unit conversion happens here on
   purpose: the caller that needs it (the synthesized test driver, see
   `lang/codegen/test_driver.mo`) does all of its own ns/us/ms/s
   arithmetic in Monad.

   Per-test timings are almost all sub-millisecond, which `current_time`
   can only ever report as "0ms" -- that is what this exists to fix.

   i64 nanoseconds from a monotonic origin overflow after ~292 years of
   uptime, so the multiplication below needs no range check. */
int64_t monad_current_time_nano(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000 + (int64_t)ts.tv_nsec;
}

/* `#[native "process_id"]` (std/process.mo's `process_id : I64`) -- returns
   the OS process ID, used to build unique /tmp paths for parallel test
   isolation. Declared pure (no `IO`) on the Monad side, unlike
   `IO.current_time` just above; both are plain `int64_t` here, since the
   `IO` wrapping a native needs is emitted by its generated IR wrapper,
   not by the C function. */
int64_t monad_process_id(void) {
    return (int64_t)getpid();
}

/* `#[native "list_dir"]` (std/io.mo's IO.list_dir_native): bare entry
   names, one directory level, SORTED -- the sort is load-bearing, not
   cosmetic: readdir order is filesystem-dependent, and the reference
   sorts, so without it a compiled binary and the interpreter would
   disagree on any directory-walking output. Skips "." and "..".
   Returns a `List String`; NULL-tolerant, yielding List.empty for an
   unreadable path (the reference errors, but this runtime has no
   error channel -- an empty listing is the same shape a caller can
   already get from an empty directory). */
static int monad_cmp_strs(const void* a, const void* b) {
    return strcmp(*(const char* const*)a, *(const char* const*)b);
}

void* monad_list_dir(char* path) {
    DIR* d = path ? opendir(path) : NULL;
    if (!d) return (void*)alloc_constructor_impl(5, 0);   /* List.empty */

    size_t cap = 16, n = 0;
    char** names = (char**)GC_malloc(sizeof(char*) * cap);
    if (!names) { closedir(d); return (void*)alloc_constructor_impl(5, 0); }

    struct dirent* e;
    while ((e = readdir(d)) != NULL) {
        if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
        if (n == cap) {
            cap *= 2;
            char** grown = (char**)GC_realloc(names, sizeof(char*) * cap);
            if (!grown) break;
            names = grown;
        }
        size_t len = strlen(e->d_name);
        char* copy = (char*)monad_alloc_atomic(len + 1);
        if (!copy) break;
        memcpy(copy, e->d_name, len + 1);
        names[n++] = copy;
    }
    closedir(d);

    qsort(names, n, sizeof(char*), monad_cmp_strs);

    /* Build in reverse (cons prepends) so the list comes out sorted. */
    void* list = (void*)alloc_constructor_impl(5, 0);
    for (size_t i = n; i > 0; i--) {
        Constructor* cons = (Constructor*)alloc_constructor_impl(6, 2);
        cons->fields[0] = names[i - 1];
        cons->fields[1] = list;
        list = cons;
    }
    return list;
}

/* `#[native "get_env"]` (std/io.mo's IO.get_env): `IO (Option String)`.
   Returns a real `Option` Constructor -- `some` tag 4 with the value as
   its one field, `none` tag 3 -- the same fixed prelude-constructor tags
   runtime.mo's `rt_tag_some`/`rt_tag_none` mirror (see `monad_list_dir`
   above for the List equivalents of the same convention). Wired as
   `io_passthrough` in natives.mo: the raw result is already a valid
   backend value, so the emitted wrapper only IO.io-wraps it. The value
   is COPIED (like list_dir copies entry names): getenv's storage is
   owned by libc and can be invalidated by a later setenv/putenv, while
   every other `String` here is an owned, GC-visible char*. */
void* monad_get_env(char* name) {
    const char* val = name ? getenv(name) : NULL;
    if (!val) return (void*)alloc_constructor_impl(3, 0);   /* Option.none */
    size_t len = strlen(val);
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (!copy) return (void*)alloc_constructor_impl(3, 0);  /* OOM -> none */
    memcpy(copy, val, len + 1);
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
    some->fields[0] = copy;
    return some;
}

/* ─── TCP ────────────────────────────────────────────────────────────
   `std/io.mo`'s four `#[native "tcp_*"]` defs, reached by
   `motes/moon`'s server and `motes/moose`'s client. Reading, writing
   and closing a connection or listener is `std/stream.mo`'s
   `stream_read`/`stream_write`/`stream_close` below, so only the
   socket-specific setup lives here.

   This is TCP's ONLY implementation. The reference deliberately has
   none -- a second implementation was not worth its maintenance cost --
   so the behaviours recorded here ARE the contract, and
   `slow_tests/src/codegen_wired_natives_e2e_tests.mo` is what holds
   them to it. `std/io.mo`'s own declarations restate the same contract
   for a reader who starts from the source side.

   A connection or listener is an `FdStream`: the raw FILE DESCRIPTOR as
   an i64, not a constructor (see the byte-stream section). Errors are
   `stream_err`'s `Result.err (Pair.pair <kind> <message>)`, with the
   message prefixed by the operation (`tcp_connect: ...`).

   Divergences from the deleted Rust implementation, recorded rather
   than papered over:

     - A double `close` here closes a RECYCLED descriptor, where the
       Rust version's handle drop was a harmless no-op for an unknown
       id. Latent only (every test closes each descriptor at most
       once), and the trade is deliberate: a C-side handle table would
       buy nothing the fd does not already give, and would have to be
       kept in step with the collector.
     - `tcp_local_port` has no `Result` channel, so a failing
       `getsockname` returns 0 where the Rust version raised.
     - No poll loop anywhere: every motes test writes before it reads
       on a single thread, so a blocking read cannot deadlock. That is
       a property of the corpus rather than of these functions -- a
       test that reads before it writes WILL block on both sides.
     - SIGPIPE is ignored at startup (`main`), so a write to a peer that
       already closed is `stream_write`'s EPIPE -> `broken_pipe`, not a
       killed process.
*/

/* Deadline helpers shared by the connect and `stream_poll` waits: one
   absolute CLOCK_MONOTONIC deadline per wait, saturating instead of
   wrapping (an absurd timeout must mean "very long", not "already
   expired"). `timeout_ms <= 0` keeps its own meaning per caller (block
   or poll-once); `remaining_ms` answers -1 for it. */
static int64_t monotonic_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + (int64_t)(ts.tv_nsec / 1000000);
}

static int64_t deadline_after_ms(int64_t timeout_ms) {
    if (timeout_ms <= 0) return 0;
    int64_t now = monotonic_ms();
    if (timeout_ms > INT64_MAX - now) return INT64_MAX;
    return now + timeout_ms;
}

static int remaining_ms(int64_t deadline, int64_t timeout_ms) {
    if (timeout_ms <= 0) return -1;
    int64_t left = deadline - monotonic_ms();
    if (left < 0) left = 0;
    if (left > INT_MAX) left = INT_MAX;
    return (int)left;
}

/* TCP connect's ONE implementation. `timeout_ms <= 0` blocks on each
   address in turn -- the `IO.tcp_connect` contract; a positive one is an
   absolute deadline spanning every address tried, each attempt
   non-blocking and polled -- the `IO.tcp_connect_timeout` contract.
   `getaddrinfo` resolves the host the way the Rust version's
   `TcpStream::connect((host, port))` did, so `"127.0.0.1"`,
   `"localhost"` and a real name all work, and each address it returns
   is tried in turn (a v6 address that fails to connect must not stop a
   working v4 one from being tried). A resolution failure is kind 8,
   `host_unresolved`: EAI_* codes are not errno values. The DNS lookup
   itself is unbounded either way. */
static void* tcp_connect_deadline(char* host, int64_t port, int64_t timeout_ms) {
    struct addrinfo hints;
    struct addrinfo* res = NULL;
    char portbuf[16];
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    snprintf(portbuf, sizeof(portbuf), "%u", (unsigned)(uint16_t)port);
    int rc = getaddrinfo(host ? host : "", portbuf, &hints, &res);
    if (rc != 0) return stream_err(8, "tcp_connect", gai_strerror(rc), 0);
    int64_t deadline = deadline_after_ms(timeout_ms);
    int fd = -1;
    int last_errno = 0;
    int last_flags = 0;
    for (struct addrinfo* ai = res; ai != NULL; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) { last_errno = errno; continue; }
        if (timeout_ms <= 0) {
            if (connect(fd, ai->ai_addr, ai->ai_addrlen) == 0) break;
            last_errno = errno;
            close(fd);
            fd = -1;
            continue;
        }
        int flags = fcntl(fd, F_GETFL, 0);
        if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) != 0) {
            last_errno = errno;
            close(fd);
            fd = -1;
            continue;
        }
        if (connect(fd, ai->ai_addr, ai->ai_addrlen) == 0) {
            last_flags = flags;
            break;
        }
        if (errno != EINPROGRESS && errno != EINTR) {
            last_errno = errno;
            close(fd);
            fd = -1;
            continue;
        }
        struct pollfd pfd;
        pfd.fd = fd;
        pfd.events = POLLOUT;
        pfd.revents = 0;
        int ready;
        do {
            ready = poll(&pfd, 1, remaining_ms(deadline, timeout_ms));
        } while (ready < 0 && errno == EINTR);
        if (ready == 0) {
            last_errno = ETIMEDOUT;
            close(fd);
            fd = -1;
            continue;
        }
        if (ready < 0) {
            last_errno = errno;
            close(fd);
            fd = -1;
            continue;
        }
        int soerr = 0;
        socklen_t slen = sizeof(soerr);
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &soerr, &slen) != 0) soerr = errno;
        if (soerr == 0) {
            last_flags = flags;
            break;
        }
        last_errno = soerr;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) return stream_os_err("tcp_connect", last_errno);
    if (timeout_ms > 0) fcntl(fd, F_SETFL, last_flags);
    return tcp_ok((void*)(int64_t)fd);
}

/* `tcp_connect_timeout : String -> U16 -> I64 -> RawIO (Result (Pair I64
   String) FdStream)`. A zero or negative timeout blocks, which is how
   `std/io.mo` spells `IO.tcp_connect` -- one native, two contracts. */
void* monad_tcp_connect_timeout(char* host, int64_t port, int64_t timeout_ms) {
    return tcp_connect_deadline(host, port, timeout_ms);
}

/* `tcp_listen : U16 -> RawIO (Result (Pair I64 String) FdStream)` --
   binds `0.0.0.0:port`, with port 0 asking the OS for one (read it back
   with `tcp_local_port`). Deliberately NO `SO_REUSEADDR`: the Rust
   version set none, every test binds port 0, and setting it would let a
   second bind steal a port a lingering connection still owns. Backlog
   128 is Rust's own default for `TcpListener::bind`. */
void* monad_tcp_listen(int64_t port) {
    int fd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (fd < 0) return stream_os_err("tcp_listen", errno);
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons((uint16_t)port);
    if (bind(fd, (struct sockaddr*)&addr, sizeof(addr)) != 0) {
        int e = errno;
        close(fd);
        return stream_os_err("tcp_listen", e);
    }
    if (listen(fd, 128) != 0) {
        int e = errno;
        close(fd);
        return stream_os_err("tcp_listen", e);
    }
    return tcp_ok((void*)(int64_t)fd);
}

/* `tcp_listen_on : String -> U16 -> RawIO (Result (Pair I64 String)
   FdStream)` -- like `tcp_listen`, but binds a specific host address or
   name. `getaddrinfo` with `AI_PASSIVE` resolves `"127.0.0.1"`,
   `"localhost"` and an empty host (the wildcard) the same way
   `tcp_connect` resolves a peer. Each returned address is tried in turn,
   so a host that resolves to a v6 address first still binds on a v4
   machine. A resolution failure is kind 8, `host_unresolved`. */
void* monad_tcp_listen_on(char* host, int64_t port) {
    struct addrinfo hints;
    struct addrinfo* res = NULL;
    char portbuf[16];
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    hints.ai_flags = AI_PASSIVE;
    snprintf(portbuf, sizeof(portbuf), "%u", (unsigned)(uint16_t)port);
    const char* node = (host && host[0]) ? host : NULL;
    int rc = getaddrinfo(node, portbuf, &hints, &res);
    if (rc != 0) return stream_err(8, "tcp_listen_on", gai_strerror(rc), 0);
    int fd = -1;
    int last_errno = 0;
    for (struct addrinfo* ai = res; ai != NULL; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) { last_errno = errno; continue; }
        if (bind(fd, ai->ai_addr, ai->ai_addrlen) == 0
            && listen(fd, 128) == 0) {
            break;
        }
        last_errno = errno;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) return stream_os_err("tcp_listen_on", last_errno);
    return tcp_ok((void*)(int64_t)fd);
}

/* `tcp_accept : FdStream -> RawIO (Result (Pair I64 String) FdStream)`
   -- blocking accept, returning a new stream for the accepted
   connection. `EINTR` retries rather than surfacing: no signal handler
   in this file wants the caller to see a spurious failure. */
void* monad_tcp_accept(int64_t listener) {
    int fd;
    do {
        fd = accept((int)listener, NULL, NULL);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return stream_os_err("tcp_accept", errno);
    return tcp_ok((void*)(int64_t)fd);
}

/* `tcp_local_port : FdStream -> RawIO U16` -- the port the listener
   actually bound, which is the only way to learn the OS-assigned port
   after `tcp_listen 0u16`. Returns 0 if `getsockname` fails; see the
   divergence note above. */
int64_t monad_tcp_local_port(int64_t listener) {
    struct sockaddr_in addr;
    socklen_t len = sizeof(addr);
    if (getsockname((int)listener, (struct sockaddr*)&addr, &len) != 0) return 0;
    return (int64_t)ntohs(addr.sin_port);
}

/* ─── Byte streams (`std/stream.mo`) ─────────────────────────────────
   One read/write/close surface over a file descriptor, with a `ByteBuf`
   payload. An `FdStream` value IS the descriptor (`Child`'s
   opaque-word trick), so `std_fd`/`stream_fd` are identities.

   Errors are `Result.err (Pair.pair <kind> <message>)` -- `err` tag 11
   and `pair` tag 15, both fixed in `lang/src/codegen/ctors.mo`'s
   `builtin_ctor_tags`. The kind is a CODE, not a `StreamErrorKind`
   constructor: that type's tags are per-program, which a C function
   cannot know, so `std/stream.mo`'s `stream_result` decodes it.

   stdout and stderr are written through libc's stdio buffers, not with
   `write(2)`, so writes interleave in order with any remaining
   `printf`/`fprintf` user and are flushed by `IO.flush_stdout`; stderr
   is flushed after every write (a log line must not wait). */

/* errno -> `StreamErrorKind`'s declaration order (std/src/stream.mo).
   Code 8, `host_unresolved`, has no errno: `tcp_connect`'s getaddrinfo
   path passes it directly. */
static int64_t stream_error_kind_of_errno(int errnum) {
    switch (errnum) {
        case ENOENT: return 0;
        case EACCES: case EPERM: return 1;
        case ECONNREFUSED: return 2;
        case ECONNRESET: return 3;
        case EPIPE: return 4;
        case EINVAL: return 5;
        /* A socket operation on a non-socket (`set_timeout` on a file):
           an invalid input, which is `FdStream.set_timeout`'s contract. */
        case ENOTSOCK: return 5;
        case ETIMEDOUT: return 6;
        /* `SO_RCVTIMEO`/`SO_SNDTIMEO` surface as EAGAIN (or its alias). */
#if EAGAIN != EWOULDBLOCK
        case EWOULDBLOCK:
#endif
        case EAGAIN: return 6;
        case EADDRINUSE: return 7;
        default: return 9;
    }
}

/* `Result.err (Pair.pair kind "<a>: <b>[ (os error <n>)]")`, the message
   formatted and COPIED into a GC-visible buffer (`strerror`'s storage is
   libc's), the shape `std::io::Error`'s Display gives the Rust host. */
static void* stream_err(int64_t kind, const char* a, const char* b, int errnum) {
    char buf[512];
    if (errnum != 0) {
        snprintf(buf, sizeof(buf), "%s: %s (os error %d)", a, b, errnum);
    } else {
        snprintf(buf, sizeof(buf), "%s: %s", a, b);
    }
    size_t len = strlen(buf);
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (copy) memcpy(copy, buf, len + 1);
    Constructor* pair = (Constructor*)alloc_constructor_impl(15, 2);
    if (pair) {
        pair->fields[0] = (void*)kind;
        pair->fields[1] = copy;
    }
    Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
    if (err) err->fields[0] = pair;
    return err;
}

static void* stream_os_err(const char* op, int errnum) {
    return stream_err(stream_error_kind_of_errno(errnum), op, strerror(errnum), errnum);
}

/* ── Line reading (std/stream.mo's `stream_read_line`) ─────────────────
 *
 * A chunked reader pulls bytes past the newline off the descriptor. They
 * are kept in this small per-descriptor carry table, and both
 * `monad_stream_read` and `monad_read_stdin_exact` serve them first, so a
 * caller that mixes line reads with byte reads never loses a byte (the
 * LSP framing tests are the guard).
 *
 * A linear array, not a hash: a program has stdio plus a handful of open
 * streams, and lookups happen once per call, never per byte. Entries are
 * cleared when their descriptor is closed (`stream_close`, `proc_wait`)
 * or reused (`stream_open`), so a new stream never inherits an old carry.
 *
 * THREADS: every fiber is an OS thread, so two fibers reading two
 * different streams still share this table, and growing it `realloc`s
 * every entry out from under the other reader. `stream_carry_lock` guards
 * the table and the entries' bytes. Only `stream_carry_slot` hands out an
 * entry pointer, and only to code holding the lock. The helpers below
 * copy bytes in or out under it, and none holds it across a `read(2)`.
 */
#define MONAD_LINE_CHUNK 4096

typedef struct {
    int fd;
    char* data;
    size_t len;
    size_t cap;
} StreamCarry;

static StreamCarry* stream_carries;
static size_t stream_carry_count;
static size_t stream_carry_cap;
static pthread_mutex_t stream_carry_lock = PTHREAD_MUTEX_INITIALIZER;

/* Caller holds `stream_carry_lock`; the entry is valid only until it is
   released (the next slot creation may move the whole table). */
static StreamCarry* stream_carry_slot(int fd, int create) {
    for (size_t i = 0; i < stream_carry_count; i++) {
        if (stream_carries[i].fd == fd) return &stream_carries[i];
    }
    if (!create) return NULL;
    if (stream_carry_count == stream_carry_cap) {
        size_t cap = stream_carry_cap ? stream_carry_cap * 2 : 4;
        StreamCarry* grown =
            (StreamCarry*)realloc(stream_carries, cap * sizeof(StreamCarry));
        if (!grown) return NULL;
        stream_carries = grown;
        stream_carry_cap = cap;
    }
    StreamCarry* c = &stream_carries[stream_carry_count++];
    c->fd = fd;
    c->data = NULL;
    c->len = 0;
    c->cap = 0;
    return c;
}

static void stream_carry_clear(int fd) {
    pthread_mutex_lock(&stream_carry_lock);
    StreamCarry* c = stream_carry_slot(fd, 0);
    if (c) {
        free(c->data);
        c->data = NULL;
        c->len = 0;
        c->cap = 0;
    }
    pthread_mutex_unlock(&stream_carry_lock);
}

static int stream_carry_push(int fd, const char* bytes, size_t n) {
    if (n == 0) return 1;
    int ok = 0;
    pthread_mutex_lock(&stream_carry_lock);
    StreamCarry* c = stream_carry_slot(fd, 1);
    if (c && c->len + n > c->cap) {
        size_t cap = c->cap ? c->cap : MONAD_LINE_CHUNK;
        while (cap < c->len + n) cap *= 2;
        char* grown = (char*)realloc(c->data, cap);
        if (grown) {
            c->data = grown;
            c->cap = cap;
        } else {
            c = NULL;
        }
    }
    if (c) {
        memcpy(c->data + c->len, bytes, n);
        c->len += n;
        ok = 1;
    }
    pthread_mutex_unlock(&stream_carry_lock);
    return ok;
}

/* Move at most `max` carried bytes into `out`, dropping them from the
   carry. `-1` when there is nothing carried. */
static ssize_t stream_carry_take(int fd, char* out, size_t max) {
    ssize_t taken = -1;
    pthread_mutex_lock(&stream_carry_lock);
    StreamCarry* c = stream_carry_slot(fd, 0);
    if (c && c->len > 0) {
        size_t n = c->len < max ? c->len : max;
        memcpy(out, c->data, n);
        memmove(c->data, c->data + n, c->len - n);
        c->len -= n;
        taken = (ssize_t)n;
    }
    pthread_mutex_unlock(&stream_carry_lock);
    return taken;
}

/* Move ALL carried bytes into the malloc'd `*acc` (growing it, and
   `*cap`, to fit), setting `*len`. 0 only when that growth fails;
   nothing carried leaves `*len` at 0 and succeeds. */
static int stream_carry_take_all(int fd, char** acc, size_t* cap, size_t* len) {
    int ok = 1;
    *len = 0;
    pthread_mutex_lock(&stream_carry_lock);
    StreamCarry* c = stream_carry_slot(fd, 0);
    if (c && c->len > 0) {
        if (c->len + 1 > *cap) {
            char* grown = (char*)realloc(*acc, c->len + 1);
            if (grown) {
                *acc = grown;
                *cap = c->len + 1;
            } else {
                ok = 0;
            }
        }
        if (ok) {
            memcpy(*acc, c->data, c->len);
            *len = c->len;
            c->len = 0;
        }
    }
    pthread_mutex_unlock(&stream_carry_lock);
    return ok;
}

/* `stream_read`'s carry path: at most `max` carried bytes as a fresh
   ByteBuf in `*out`. -1 nothing carried, 0 out of memory, 1 served. */
static int stream_carry_take_buf(int fd, size_t max, BufObj** out) {
    int served = -1;
    pthread_mutex_lock(&stream_carry_lock);
    StreamCarry* c = stream_carry_slot(fd, 0);
    if (c && c->len > 0) {
        size_t n = c->len < max ? c->len : max;
        BufObj* obj = bytebuf_new((int64_t)n);
        if (obj) {
            memcpy(obj->payload, c->data, n);
            memmove(c->data, c->data + n, c->len - n);
            c->len -= n;
            *out = obj;
            served = 1;
        } else {
            served = 0;
        }
    }
    pthread_mutex_unlock(&stream_carry_lock);
    return served;
}

static void* stream_line_too_long(int64_t max_len) {
    char msg[64];
    snprintf(msg, sizeof(msg), "line longer than %lld bytes", (long long)max_len);
    return stream_err(5, "stream_read_line", msg, 0);
}

/* `Result.ok (Option.some <line>)` from an owned malloc buffer. */
static void* stream_line_some(char* buf, size_t len) {
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (!copy) {
        free(buf);
        return stream_err(9, "stream_read_line", "out of memory", 0);
    }
    memcpy(copy, buf, len);
    copy[len] = '\0';
    free(buf);
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
    if (some) some->fields[0] = copy;
    return tcp_ok(some);
}

static void* stream_line_none(void) {
    return tcp_ok(alloc_constructor_impl(3, 0));
}

/* stdin's line reader, ONE BYTE AT A TIME. Load-bearing, not an
 * oversight: `motes/tui/src/input.mo` reads a byte and then `poll(2)`s raw
 * fd 0, so bytes pulled into a userspace carry would be invisible to the
 * poll (the Phase 3 stdin tests pin this). The loop is a C loop, so its
 * depth is constant. */
static void* stream_read_line_stdin(int64_t max_len, int64_t discard) {
    size_t cap = 256, len = 0;
    char* acc = (char*)malloc(cap);
    if (!acc) return stream_err(9, "stream_read_line", "out of memory", 0);
    for (;;) {
        char c;
        ssize_t r = read(0, &c, 1);
        if (r < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            free(acc);
            return stream_os_err("stream_read_line", e);
        }
        if (r == 0) {
            if (discard || len == 0) { free(acc); return stream_line_none(); }
            return stream_line_some(acc, len);
        }
        if (c == '\n') return stream_line_some(acc, len);
        if (max_len > 0 && (int64_t)len >= max_len) {
            free(acc);
            return stream_line_too_long(max_len);
        }
        if (len + 2 > cap) {
            size_t want = cap * 2;
            char* grown = (char*)realloc(acc, want);
            if (!grown) { free(acc); return stream_err(9, "stream_read_line", "out of memory", 0); }
            acc = grown;
            cap = want;
        }
        acc[len++] = c;
    }
}

/* `stream_read_line : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) (Option String))` -- one line WITHOUT its newline (a `\r`
   stays), `Option.none` at end of stream or when `discard` drops a
   partial line, and `invalid_input` once the content exceeds `max_len`
   (`max_len <= 0` is unbounded).
 *
 * stdin goes through the byte-at-a-time loop above (poll contract);
 * files and child pipes are read in chunks, because nothing polls them
 * mid-line, and the bytes after the newline go into the carry so the next
 * call -- line or byte read -- continues exactly where this one stopped. */
void* monad_stream_read_line(int64_t fd, int64_t max_len, int64_t discard) {
    if (fd == 0) return stream_read_line_stdin(max_len, discard);
    size_t cap = 256, len = 0;
    char* acc = (char*)malloc(cap);
    if (!acc) return stream_err(9, "stream_read_line", "out of memory", 0);

    if (!stream_carry_take_all((int)fd, &acc, &cap, &len)) {
        free(acc);
        return stream_err(9, "stream_read_line", "out of memory", 0);
    }

    size_t scanned = 0;
    for (;;) {
        char* nl = (char*)memchr(acc + scanned, '\n', len - scanned);
        if (nl) {
            size_t i = (size_t)(nl - acc);
            if (max_len > 0 && (int64_t)i > max_len) {
                free(acc);
                stream_carry_clear((int)fd);
                return stream_line_too_long(max_len);
            }
            if (!stream_carry_push((int)fd, acc + i + 1, len - i - 1)) {
                free(acc);
                return stream_err(9, "stream_read_line", "out of memory", 0);
            }
            return stream_line_some(acc, i);
        }
        scanned = len;
        if (max_len > 0 && (int64_t)len > max_len) {
            free(acc);
            stream_carry_clear((int)fd);
            return stream_line_too_long(max_len);
        }
        if (len + MONAD_LINE_CHUNK > cap) {
            size_t want = cap;
            while (want < len + MONAD_LINE_CHUNK) want *= 2;
            char* grown = (char*)realloc(acc, want);
            if (!grown) { free(acc); return stream_err(9, "stream_read_line", "out of memory", 0); }
            acc = grown;
            cap = want;
        }
        ssize_t r;
        do {
            r = read((int)fd, acc + len, MONAD_LINE_CHUNK);
        } while (r < 0 && errno == EINTR);
        if (r < 0) {
            int e = errno;
            free(acc);
            return stream_os_err("stream_read_line", e);
        }
        if (r == 0) {
            if (discard || len == 0) { free(acc); return stream_line_none(); }
            return stream_line_some(acc, len);
        }
        len += (size_t)r;
    }
}

/* `stream_open : String -> I64 -> RawIO (Result (Pair I64 String)
   FdStream)` -- mode 0 reads, mode 1 creates-or-truncates for writing,
   mode 2 creates-or-appends (both 0644). `O_CLOEXEC` so a spawned child
   never inherits the descriptor. */
void* monad_stream_open(char* path, int64_t mode) {
    int flags;
    if (mode == 0) flags = O_RDONLY;
    else if (mode == 1) flags = O_WRONLY | O_CREAT | O_TRUNC;
    else if (mode == 2) flags = O_WRONLY | O_CREAT | O_APPEND;
    else return stream_err(5, "stream_open", "unknown mode", 0);
    int fd;
    do {
        fd = open(path ? path : "", flags | O_CLOEXEC, 0644);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return stream_os_err("stream_open", errno);
    stream_carry_clear(fd); /* a reused descriptor inherits nothing */
    return tcp_ok((void*)(int64_t)fd);
}

/* `stream_read : FdStream -> I64 -> RawIO (Result (Pair I64 String)
   ByteBuf)` -- ONE `read(2)` of at most `max_bytes`, copied into one
   buffer sized to what actually arrived. A zero-length buffer is end of
   stream; `max_bytes <= 0` reads nothing and returns one too. */
void* monad_stream_read(int64_t fd, int64_t max_bytes) {
    if (max_bytes <= 0) return tcp_ok(bytebuf_new(0));
    BufObj* carried = NULL;
    int served = stream_carry_take_buf((int)fd, (size_t)max_bytes, &carried);
    if (served == 0) return stream_err(9, "stream_read", "out of memory", 0);
    if (served == 1) return tcp_ok(carried);
    unsigned char small[4096];
    unsigned char* tmp = max_bytes <= (int64_t)sizeof(small)
        ? small : (unsigned char*)malloc((size_t)max_bytes);
    if (!tmp) return stream_err(9, "stream_read", "out of memory", 0);
    ssize_t n;
    do {
        n = read((int)fd, tmp, (size_t)max_bytes);
    } while (n < 0 && errno == EINTR);
    if (n < 0) {
        int e = errno;
        if (tmp != small) free(tmp);
        return stream_os_err("stream_read", e);
    }
    BufObj* obj = bytebuf_new((int64_t)n);
    if (obj && n > 0) memcpy(obj->payload, tmp, (size_t)n);
    if (tmp != small) free(tmp);
    if (!obj) return stream_err(9, "stream_read", "out of memory", 0);
    return tcp_ok(obj);
}

/* `stream_write : FdStream -> ByteBuf -> RawIO (Result (Pair I64 String)
   I64)` -- ALL of the buffer, ok payload its full length. fds 1/2 go
   through stdio (see the section comment); anything else is a `write`
   loop, since a pipe or socket may take less than asked. SIGPIPE is
   ignored (`main`), so a vanished reader is EPIPE -> `broken_pipe`. */
void* monad_stream_write(int64_t fd, void* buf) {
    BufObj* obj = (BufObj*)buf;
    int64_t n = obj ? obj->len : 0;
    if (n == 0) return tcp_ok((void*)(int64_t)0);
    if (fd == 1 || fd == 2) {
        FILE* f = fd == 1 ? stdout : stderr;
        errno = 0;
        int failed = fwrite(obj->payload, 1, (size_t)n, f) != (size_t)n;
        if (fd == 2) failed = fflush(f) == EOF || failed;
        /* The process's own stdout/stderr die of SIGPIPE like every other
           stdio writer here (`stdio_die_on_epipe`); any other failure is
           an ordinary `Result.err`. */
        stdio_die_on_epipe(failed);
        if (failed) return stream_os_err("stream_write", errno ? errno : EIO);
        return tcp_ok((void*)n);
    }
    int64_t done = 0;
    while (done < n) {
        ssize_t w = write((int)fd, obj->payload + done, (size_t)(n - done));
        if (w < 0) {
            if (errno == EINTR) continue;
            return stream_os_err("stream_write", errno);
        }
        done += w;
    }
    return tcp_ok((void*)n);
}

/* `stream_close : FdStream -> RawIO Unit` -- never fails. The three
   standard descriptors are left open: closing one would let the next
   `open` reuse fd 0/1/2 and silently receive the process's stdio. */
void* monad_stream_close(int64_t fd) {
    if (fd > 2) {
        stream_carry_clear((int)fd);
        /* A blocking `accept` does not wake on `close` alone; shutting the
           socket down first makes it return (and is harmless on a
           non-socket, where it fails with ENOTSOCK). That is what lets
           `Server.shutdown` unblock the accept loop. */
        shutdown((int)fd, SHUT_RDWR);
        close((int)fd);
    }
    return tcp_unit();
}

/* `stream_fd : FdStream -> RawIO I32` -- the value already is the fd. */
int64_t monad_stream_fd(int64_t fd) {
    return fd;
}

/* `stream_poll : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) I64)` -- `poll(2)` on an arbitrary descriptor, the general
   form of `term_ctl`'s stdin wait. Events: 1 readable, 2 writable.
   Result 1 ready, 0 timeout. */
void* monad_stream_poll(int64_t fd, int64_t events, int64_t timeout_ms) {
    struct pollfd pfd;
    pfd.fd = (int)fd;
    pfd.events = 0;
    if (events & 1) pfd.events |= POLLIN;
    if (events & 2) pfd.events |= POLLOUT;
    pfd.revents = 0;
    /* One deadline across EINTR retries, as the connect loop does: a
       signal must not hand the wait a fresh budget. */
    int64_t deadline = deadline_after_ms(timeout_ms);
    int rc;
    do {
        int t;
        if (timeout_ms > 0) t = remaining_ms(deadline, timeout_ms);
        else if (timeout_ms < 0) t = -1;
        else t = 0;
        rc = poll(&pfd, 1, t);
    } while (rc < 0 && errno == EINTR);
    if (rc < 0) return stream_os_err("stream_poll", errno);
    return tcp_ok((void*)(int64_t)(rc > 0 ? 1 : 0));
}

/* `stream_set_timeout : FdStream -> I64 -> I64 -> RawIO (Result (Pair
   I64 String) Unit)` -- SO_RCVTIMEO/SO_SNDTIMEO on a socket. A zero
   bound leaves that direction unchanged. */
void* monad_stream_set_timeout(int64_t fd, int64_t recv_ms, int64_t send_ms) {
    struct timeval tv;
    if (recv_ms > 0) {
        tv.tv_sec = (time_t)(recv_ms / 1000);
        tv.tv_usec = (suseconds_t)((recv_ms % 1000) * 1000);
        if (setsockopt((int)fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv)) != 0)
            return stream_os_err("stream_set_timeout", errno);
    }
    if (send_ms > 0) {
        tv.tv_sec = (time_t)(send_ms / 1000);
        tv.tv_usec = (suseconds_t)((send_ms % 1000) * 1000);
        if (setsockopt((int)fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv)) != 0)
            return stream_os_err("stream_set_timeout", errno);
    }
    return tcp_ok(tcp_unit());
}

/* `std_fd : I64 -> FdStream` -- pure; 0/1/2 name stdin/stdout/stderr. */
int64_t monad_std_fd(int64_t which) {
    return which;
}

/* ─── Raw stdio (`std/io.mo`'s raw-stdio group) ──────────────────────
   The two stdio operations the byte streams above cannot express:
   `read_stdin_exact`'s fill-to-n read and a real stdout flush. Writing
   to stdout/stderr and `IO.read_line` are `std/stream.mo` streams on
   fds 0-2 (`monad_stream_read`/`monad_stream_write`). Both are `RawIO`
   natives (`raw_io_passthrough`, lang/src/codegen/natives.mo) returning
   their raw payload.

   Read the same group's comment in `std/io.mo` for the contract, and
   `core/src/core_native.rs`'s `read_stdin_exact` for the Rust
   evaluator's half. That half needs a UTF-8-carry subtlety this one
   does not: bytes are stored raw here, which is exactly what a byte
   stream wants, so no chunk boundary can surprise this side.

   Every stdin read goes through `read(0, ...)` rather than stdio
   (`getchar`/`fgets`), and that is load-bearing rather than a
   preference: stdio reads a whole block ahead into its own buffer, so
   the bytes after a line would be swallowed before the caller's next
   `read_stdin_exact` -- the protocol stream would desynchronize with no
   error anywhere. */

/* `read_stdin_exact : I64 -> RawIO String` -- blocking read of UP TO
   `n` bytes from stdin, returning exactly the bytes read. The result
   being SHORTER than `n` (including "") means EOF to the caller, which
   is what makes that a reliable end-of-stream test rather than "the OS
   returned a short read this time": the loop below only stops early
   when a `read` actually reports 0, so a partial return is always EOF.
   `n <= 0` returns "".

   The result is NUL-terminated but its LENGTH is the caller's count of
   bytes, not `strlen` -- a frame body may legitimately contain NULs.
   Note that a String with an embedded NUL is a representation this
   runtime's other String consumers (`ByteBuf.of_string`, `strlen`-based
   comparisons) cannot round-trip; the caller slices it with
   `String.slice`, which is length-based (`monad_string_slice`), so the
   byte stream survives as far as the framing reader needs it. */
char* monad_read_stdin_exact(int64_t n) {
    if (n <= 0) {
        char* empty = (char*)monad_alloc_atomic(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    size_t want = (size_t)n;
    char* buf = (char*)monad_alloc_atomic(want + 1);
    if (!buf) {
        /* Never hand back NULL: a NULL String crashes the first
           `strlen`-based consumer, whereas "" is exactly the
           end-of-stream signal this native already has a meaning for
           (a result shorter than `n`). An absurd `n` (e.g. a
           `Content-Length` read out of a corrupt frame) lands here
           rather than taking the process down. */
        char* empty = (char*)monad_alloc_atomic(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    size_t got = 0;
    /* Bytes a chunked line read pulled off fd 0 and did not use come
       first -- they are already past the descriptor's read position. */
    ssize_t carried = stream_carry_take(0, buf, want);
    if (carried > 0) got = (size_t)carried;
    while (got < want) {
        ssize_t r = read(0, buf + got, want - got);
        if (r < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (r == 0) break;            /* EOF */
        got += (size_t)r;
    }
    buf[got] = '\0';
    return buf;
}

/* `flush_stdout : RawIO Unit` -- needed because stdout is block-buffered
   when it is a pipe (which is how a language server's peer reads it), so
   a written frame stays invisible until this runs. */
void* monad_flush_stdout(void) {
    errno = 0;
    stdio_die_on_epipe(fflush(stdout) == EOF);
    return tcp_unit();
}

/* Raise the stack limit before running any Monad code.
 *
 * The compiler recurses deeply over the module graph and over terms --
 * deeply enough that compiling a large program (the compiler itself, at
 * ~140 modules) overflows the usual 8 MB stack and dies with a bare
 * SIGSEGV: no diagnostic, no stage name, just exit 139. `devenv.nix`'s
 * bootstrap task has carried `ulimit -s 131072` for exactly this reason,
 * but that only helps the task; anyone invoking a compiled binary
 * directly got the silent crash.
 *
 * Raising RLIMIT_STACK here makes the binary self-sufficient. Only the
 * SOFT limit is raised, and only up to whatever hard limit the system
 * allows, so this can never exceed what the user's environment permits.
 * Failure is ignored deliberately: a lower ceiling is the environment's
 * decision, and the program should still run for inputs that fit.
 *
 * Note this must happen before the deep recursion starts, and cannot be
 * done from Monad code. It is also only half the answer, and the weaker
 * half: see `main`'s trampoline below, which hands `main_monad` a stack
 * of its own rather than relying on this having worked. */
static void raise_stack_limit(void) {
    const rlim_t wanted = (rlim_t)128 * 1024 * 1024; /* matches devenv.nix */
    struct rlimit rl;
    if (getrlimit(RLIMIT_STACK, &rl) != 0) return;
    if (rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur < wanted) {
        rlim_t target = wanted;
        if (rl.rlim_max != RLIM_INFINITY && target > rl.rlim_max) target = rl.rlim_max;
        if (target > rl.rlim_cur) {
            rl.rlim_cur = target;
            setrlimit(RLIMIT_STACK, &rl);
        }
    }
}

typedef struct {
    void* args;
    int64_t result;
} MainThread;

/* Run `main_monad` on a thread whose stack is sized explicitly, rather
   than on the one the OS handed the process.

   `raise_stack_limit` above moves only the SOFT limit, which is enough
   on Linux: it grows the main thread's stack on demand up to that
   limit. Darwin instead sizes the main thread's stack as a fixed
   mapping at exec time, so a limit raised afterwards changes nothing
   there and the binary gets ~8 MB however the shell was configured --
   under half the ~64 MB the ladder itself states it needs, and nowhere
   near the 128 MB a fiber gets. An explicit stack makes the depth
   independent of the ambient rlimit on every platform, which is what
   raising the limit was trying to buy in the first place.

   Same shape and same fallback as `monad_fork_io`'s worker: if the
   reservation is refused, retry on the default stack, because a shallow
   stack that still runs beats a process that cannot start. */
static void* main_thread_main(void* p) {
    MainThread* m = (MainThread*)p;
    m->result = (int64_t)(intptr_t)main_monad(m->args);
    return NULL;
}

int main(int argc, char** argv) {
    raise_stack_limit();
    GC_INIT();
    /* A write to a pipe or socket whose reader has gone must come back as
       EPIPE (a `Result.err` the caller can see), not kill the process --
       Rust's std makes the same choice process-wide. `MSG_NOSIGNAL` only
       covers `send`; `monad_stream_write`'s `write` to a child that
       already exited has no such cover. Ignored dispositions survive
       `exec`, so
       every fork child (`monad_exec_cmd`, `monad_proc_spawn`) restores
       the default before exec'ing, or `yes | head` in a spawned shell
       would never stop. The process's own stdout/stderr keep dying of
       SIGPIPE through `stdio_die_on_epipe`. */
    signal(SIGPIPE, SIG_IGN);
    /* Exclude argv[0] (the binary's own path) -- matches the
       interpreter's own `run <file> <args...>` semantics (args passed to
       a compiled program's `main` are just the extra CLI args, not the
       program's own path), and makes an empty `args` list actually
       reachable (e.g. examples/hello.mo's "no arguments" fallback). */
    void* args = monad_build_args(argc - 1, argv + 1);
    MainThread m;
    m.args = args;
    m.result = 0;
    pthread_t thread;
    pthread_attr_t attr;
    int rc = pthread_attr_init(&attr);
    if (rc == 0) {
        pthread_attr_setstacksize(&attr, MONAD_DEEP_STACK_BYTES);
        rc = pthread_create(&thread, &attr, main_thread_main, &m);
        if (rc != 0) {
            pthread_attr_destroy(&attr);
            pthread_attr_init(&attr);
            rc = pthread_create(&thread, &attr, main_thread_main, &m);
        }
        pthread_attr_destroy(&attr);
    }
    if (rc != 0) {
        /* No thread at all. `raise_stack_limit` above is then the only
           stack this process has -- exactly the behaviour before this
           trampoline existed, which is the right way to degrade. */
        return (int)(intptr_t)main_monad(args);
    }
    pthread_join(thread, NULL);
    return (int)m.result;
}
