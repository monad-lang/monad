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
    MONAD_STAT(MONAD_STAT_SCANNED, size);
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
    MONAD_STAT(MONAD_STAT_ATOMIC, size);
    return GC_malloc_atomic(size);
}

void monad_retain(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    atomic_fetch_add(&h->refcount, 1);
}

/* ── Owned allocation (ownership-regions-memory O3/O4) ──────────────────
   The Owned half of the split. A default build forwards to the GC, so the
   flag being unset is byte-for-byte the old behaviour. Under
   `-DMONAD_OWNERSHIP` the block is real `calloc` memory: zeroed like
   Boehm's, but owned by the program and returned by `monad_owned_free`.
   `calloc` rather than `malloc` because codegen reads an unset
   Constructor field the same way on both paths.

   `-DMONAD_OWNERSHIP_POISON` keeps the real allocation but never frees:
   the free path fills the whole block with 0xDE instead. That makes a
   use-after-free deterministic (a tag read returns garbage immediately)
   without needing a sanitizer. */
rt_word monad_owned_alloc(rt_size size) {
#if defined(MONAD_OWNERSHIP)
    void* ptr = calloc(1, (size_t)size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
        h->size = size;
    }
    return ptr;
#else
    return monad_alloc(size);
#endif
}

void monad_owned_free(rt_word ptr) {
#if defined(MONAD_OWNERSHIP)
    if (!ptr) return;
    MONAD_STAT(MONAD_STAT_OWNED_FREE, 0);
#ifdef MONAD_OWNERSHIP_POISON
    Header* h = (Header*)RT_PTR(ptr);
    memset(ptr, 0xDE, (size_t)h->size);
#else
    free(RT_PTR(ptr));
#endif
#else
    /* GC-owned: freeing it would corrupt the collector's heap. */
    (void)ptr;
#endif
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

/* ── Allocation stats (ownership-regions-memory O-M0) ─────────────────
   Per-kind counters, printed at exit when MONAD_ALLOC_STATS=1. The split
   between constructors/closures (Owned candidates) and strings/ByteBufs/
   Ref/Array (Region candidates) is what decides how much O4's drop glue can
   recover before regions exist. `monad_alloc` counts the SCANNED total and
   `monad_alloc_atomic` the ATOMIC total; runtime_core.c adds the per-kind
   entries for constructors, closures, Array, Ref and ByteBuf. */
static unsigned long long monad_stat_counts[MONAD_STAT_KIND_COUNT];
static unsigned long long monad_stat_bytes[MONAD_STAT_KIND_COUNT];
static int monad_stats_on = 0;

void monad_alloc_stats_note(int kind, rt_size bytes) {
    if (!monad_stats_on) return;
    if (kind < 0 || kind >= MONAD_STAT_KIND_COUNT) return;
    /* Fibers are OS threads, and every one of them allocates: plain `+=`
       here is a data race that loses increments. Relaxed atomics are enough
       for counters; the printer runs after the main thread is joined. */
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
        case MONAD_STAT_ATOMIC: return "atomic-bytes";
        case MONAD_STAT_SCANNED: return "scanned-bytes";
        case MONAD_STAT_OWNED_CTOR: return "owned-constructors";
        case MONAD_STAT_OWNED_FREE: return "owned-frees";
        default: return "?";
    }
}

static void monad_alloc_stats_print(void) {
    for (int k = 0; k < MONAD_STAT_KIND_COUNT; k++) {
        unsigned long long count =
            __atomic_load_n(&monad_stat_counts[k], __ATOMIC_RELAXED);
        unsigned long long bytes =
            __atomic_load_n(&monad_stat_bytes[k], __ATOMIC_RELAXED);
        fprintf(stderr, "[monad alloc] %-14s count=%llu bytes=%llu\n",
                monad_stat_label(k), count, bytes);
    }
}

/* Read the flag once, then register the printer. Called from `main` before
   any Monad code runs; an unset/empty/"0" value leaves the note function a
   single predictable branch. */
void monad_alloc_stats_install(void) {
    const char* v = getenv("MONAD_ALLOC_STATS");
    if (!v || !*v || v[0] == '0') return;
    monad_stats_on = 1;
    atexit(monad_alloc_stats_print);
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
   to `await_fiber` (rust/core/src/core_native.rs's own "Rust Host Status"
   note), so nothing there can ever interleave. Two visible consequences,
   both deliberate:

   * `forkIO` starts the thread at fork time (eager), and `await_fiber`
     waits for it. The corpus is indifferent to the difference -- every
     `forkIO` in it is awaited, or cancelled-and-discarded -- but a test
     that *requires* interleaving can only pass here.
   * Cancellation is COOPERATIVE, observed at the next IO bind.
     `pthread_cancel` would leave Boehm's allocator lock held and the
     thread unregistered, so `monad_cancel_fiber` sets the flag and
     `monad_io_bind` short-circuits with MONAD_CANCELLED_SENTINEL once it
     is set; the rest of the do-block, side effects included, does not
     run. Native calls and pure code already in progress finish, so a
     fiber stuck in a long pure computation still runs to its end. The
     host can only ever cancel a fiber it has NOT started, which is the
     same observable behaviour for every cancellation point the language
     currently expresses. This bind check is also the yield point S3
     (M:N) needs, so it must not be moved into the compiler.

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
   GC_THREADS IS `GC_pthread_create`, and is created DETACHED: nobody
   joins a fiber. `await`/`poll` learn the result from the handle's
   condvar, never from a join, so a join would only have reclaimed the
   thread -- and a fiber that was cancelled, lost a `race` or was dropped
   with its scope is never awaited at all. Joinable, each of those kept
   its whole stack mapping (the 128 MB reservation below plus every page
   it touched) until the process exited. Detached, the thread gives its
   stack back the moment it returns, and Boehm unregisters it on the way
   out. */

/* MONAD_FIBER_TAG / MONAD_SCOPE_TAG are defined with the other `Header.tag`
   kind values at the head of this file; `monad_get_tag` needs them before
   the fiber code does. */
/* The stack every thread that runs compiled Monad code is created with,
   `main` included -- see its trampoline below. A fiber body can recurse
   exactly as deeply as `main` can, so the plan doc's original 8 KB
   ucontext stack would overflow on the first recursive helper. The
   reservation is ADDRESS space, committed on demand, so a thread that
   does not recurse deeply never pays for it in RSS -- and the stack is
   unmapped again when the (detached) thread exits.

   WAS 128 MB, which was the value `raise_stack_limit` and devenv.nix both
   name. It is 32 MB because that is where the measurement in
   plans/implementations/monad-fiber-scheduler.md P3 put the actual
   requirement, and because the reservation is the ONLY per-fiber cost that
   scales with fiber count (RSS per fiber is ~10 KB regardless):

     * The compiler SELF-COMPILES inside an 8 MB stack
       (`MONAD_STACK_BYTES=8388608 monad build cli/src/main.mo`), and the
       binary it produces then checks the tree cleanly -- so 8 MB is proven
       end to end, not just "the tests pass". `lang/src/parser.mo` alone
       checks at 4 MB.
     * 32 MB is therefore a 4x margin over a measured worst case. A stack
       that is too small is a SEGFAULT rather than a slowdown, so the knob
       stays 4x above the deepest recursion anything has actually reached
       rather than being set to the measured floor.
     * 200 fibers now reserve 6.4 GB of address space instead of 26 GB,
       which is the difference between "a few hundred fibers per process"
       and "a few thousand" on a 64-bit host.
   `MONAD_STACK_BYTES` is unchanged as the per-run escape hatch, and
   `raise_stack_limit` still raises the main thread's SOFT limit for the
   case where this reservation is refused. */
#define MONAD_DEEP_STACK_BYTES ((size_t)32 * 1024 * 1024)
/* The smallest reservation `MONAD_STACK_BYTES` may ask for. A test wants a
   small stack to make an overrun fail in seconds instead of after tens of
   thousands of frames; a typo must not make every program crash, so the
   override is clamped at both ends. */
#define MONAD_MIN_STACK_BYTES ((size_t)1024 * 1024)
#define MONAD_MAX_STACK_BYTES ((size_t)1024 * 1024 * 1024)

/* The reservation for the main trampoline and every fiber. `MONAD_STACK_BYTES`
   (a plain decimal byte count) overrides it; unset or unparsable keeps the
   default. Both trampolines call this so one knob moves both. */
static size_t monad_stack_bytes(void) {
    const char* v = getenv("MONAD_STACK_BYTES");
    if (!v || !*v) return MONAD_DEEP_STACK_BYTES;
    long n = strtol(v, NULL, 10);
    if (n <= 0) return MONAD_DEEP_STACK_BYTES;
    size_t s = (size_t)n;
    if (s < MONAD_MIN_STACK_BYTES) s = MONAD_MIN_STACK_BYTES;
    if (s > MONAD_MAX_STACK_BYTES) s = MONAD_MAX_STACK_BYTES;
    return s;
}

typedef struct {
    Header header;
    void* action;      /* the `Unit -> IO A` closure, until the thread runs */
    int64_t state;     /* 0 while the thread runs, 1 once it has stopped */
    int64_t cancelled; /* set by monad_cancel_fiber, read by monad_io_bind
                          through the thread-local pointer; every access is
                          an `__atomic` builtin (the canceling thread is not
                          the fiber) */
    int64_t io_box;    /* the action's own result: an `IO A`, i.e. a complete
                          `IO.mk (RawIO.io _)` box */
    int64_t released;  /* 1 once the WORKER's retain (monad_fork_io) has been
                          released, by whichever of await/poll/cancel
                          consumes the handle first. The scope's own
                          reference (monad_scope_fork) is a different one,
                          released unconditionally by monad_scope_drop. */
    pthread_mutex_t lock;
    pthread_cond_t finished;
    /* Set to 1 by `fiber_main` as its LAST store, with release ordering,
       so a `fiber_wait_any` waiter can read it without taking `lock`.
       That is what lets the wait span a SET of handles: `state` is
       guarded by each fiber's own `lock`, so scanning N of them would
       mean N lock/unlock pairs per pass, while `done` is one atomic read
       per member and never blocks. Every existing reader of `state`
       (await/poll/cancel) is left on the lock exactly as before; `done`
       is purely additive. Plain `int64_t` with `__atomic_*` builtins,
       matching how `cancelled` above is spelled: the builtins do not
       accept a `_Atomic`-qualified operand. */
    int64_t done;
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
/* Defined with the channel code below; `monad_cancel_fiber` needs it to
   push a wake into any channel the cancelled fiber is parked on. */
static void channel_wake_cancelled(void);

/* ── fiber_wait_any's shared completion condvar ──────────────────────
   Declared here, before `fiber_main`, because the worker broadcasts on
   completion. Every fiber publishes to it; `monad_fiber_wait_any` below
   parks on it. See that function for why one shared condvar and not N. */
static pthread_mutex_t fiber_any_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t fiber_any_cond = PTHREAD_COND_INITIALIZER;

/* Broadcast this condvar (completion, or a cancel). Defined beside
   `monad_fiber_wait_any`; declared here because `fiber_main` and
   `monad_cancel_fiber` both use it and both come first. */
static void fiber_any_wake(void);

static void fiber_mark_cancelled(Fiber* f) {
    pthread_mutex_lock(&f->lock);
    /* Only a fiber that has NOT finished. The host's `Fiber::cancel`
       transitions Pending -> Cancelled and is a no-op otherwise, so
       cancelling a completed fiber must not throw away a result that was
       already in hand. `state` is published under this same lock by
       fiber_main, so the test cannot race the completion it is testing
       for. */
    if (!f->state) __atomic_store_n(&f->cancelled, 1, __ATOMIC_RELEASE);
    pthread_mutex_unlock(&f->lock);
}

/* Runs the fiber's action, then publishes its result. `arg` is the fiber
   itself. The thread is detached; the unlock below is its last touch of
   the handle. */
static void* fiber_main(void* arg) {
    Fiber* f = (Fiber*)arg;
    /* Unit.unit is tag 0, arity 0 -- `builtin_ctor_tags`
       (lang/src/codegen/ctors.mo) pins it, and it is the same value
       monad_array_set_in_place returns for its own `IO Unit`. */
    void* unit = alloc_constructor_impl(0, 0);
    /* Publish this fiber's cancel word for monad_io_bind. The body runs
       with it set, so a cancel that lands while it sleeps or blocks is
       observed at its next bind; the clear is for the thread's later
       life, should anything else run on it. */
    monad_set_cancel_flag(&f->cancelled);
    int64_t box = apply_closure1_impl(f->action, (int64_t)(intptr_t)unit);
    monad_set_cancel_flag(NULL);
    pthread_mutex_lock(&f->lock);
    /* The closure has run: drop the handle's reference to it before the
       result is published. A caller that still holds the handle (weaver's
       poll loop does) must not pin the turn's whole captured environment. */
    f->action = NULL;
    f->io_box = box;
    f->state = 1;
    /* Release-store BEFORE the broadcast: a wait-any waiter reads `done`
       without the lock, so the state/io_box stores above must be visible
       to it the moment `done` flips. */
    __atomic_store_n(&f->done, 1, __ATOMIC_RELEASE);
    pthread_cond_broadcast(&f->finished);
    pthread_mutex_unlock(&f->lock);
    /* Wake every `fiber_wait_any` waiter. Taken AFTER `f->lock` is
       released, so the two locks are never held at once and there is no
       ordering between them to get wrong. */
    fiber_any_wake();
    return NULL;
}

void* monad_fork_io(void* closure) {
    Fiber* f = (Fiber*)monad_alloc(sizeof(Fiber));
    if (!f) return NULL;
    f->header.tag = MONAD_FIBER_TAG;
    f->action = closure;
    f->state = 0;
    __atomic_store_n(&f->cancelled, 0, __ATOMIC_RELAXED);
    f->io_box = 0;
    f->released = 0;
    __atomic_store_n(&f->done, 0, __ATOMIC_RELAXED);
    pthread_mutex_init(&f->lock, NULL);
    pthread_cond_init(&f->finished, NULL);
    /* The worker's own reference, released by whoever consumes the
       handle (await or cancel). Boehm's reachability is what actually
       keeps the block alive today -- the caller holds the pointer too --
       so this is the ownership handoff M4's linear `Fiber` needs, not a
       liveness guard. */
    monad_retain(f);
    pthread_t thread;
    pthread_attr_t attr;
    int rc = pthread_attr_init(&attr);
    if (rc == 0) {
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
        pthread_attr_setstacksize(&attr, monad_stack_bytes());
        rc = pthread_create(&thread, &attr, fiber_main, f);
        if (rc != 0) {
            /* The stack reservation can be refused (thread-count or
               address-space limits). Retry on the default stack: a fiber
               on a small stack beats no fiber. */
            pthread_attr_destroy(&attr);
            pthread_attr_init(&attr);
            pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
            rc = pthread_create(&thread, &attr, fiber_main, f);
        }
        pthread_attr_destroy(&attr);
    }
    if (rc != 0) {
        /* No thread at all. Publish an already-finished state with no
           result rather than a handle that can never become ready: await
           and poll answer it `err never_started` (fiber_answer). The
           action never ran, so drop it too. */
        f->action = NULL;
        f->state = 1;
        f->io_box = 0;
        __atomic_store_n(&f->done, 1, __ATOMIC_RELEASE);
    }
    return f;
}

/* What await and poll answer for a fiber that has stopped, as the raw
   `Result I64 A` payload `std/src/concurrent/fiber.mo` maps to
   `Result FiberError A`: `err 1` cancelled, `err 2` never started (fork
   failure leaves `io_box` 0), else `ok a`. Both natives are
   `raw_io_passthrough` in natives.mo, so the backend adds the `RawIO.io`
   layer. Takes the handle's answer under its lock and releases the
   worker's reference exactly once, by whichever of await/poll/cancel
   consumes the handle first: releasing once per call would drive the
   count negative on a repeated await, which is precisely the ownership
   the count exists to hand to M4. A repeated await or poll answers the
   same again. A NULL handle -- `monad_fork_io` could not allocate one --
   is a fiber that never started. */
static void* fiber_answer(Fiber* f) {
    if (!f) {
        Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
        err->fields[0] = (void*)(intptr_t)2;
        return err;
    }
    pthread_mutex_lock(&f->lock);
    int64_t cancelled = __atomic_load_n(&f->cancelled, __ATOMIC_ACQUIRE);
    int64_t box = f->io_box;
    int release = !f->released;
    f->released = 1;
    pthread_mutex_unlock(&f->lock);
    if (release) monad_release(f);
    if (cancelled || !box) {
        Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
        err->fields[0] = (void*)(intptr_t)(cancelled ? 1 : 2);
        return err;
    }
    /* `box` is the action's own result, typed `IO A` -- a complete
       `IO.mk (RawIO.io a)` box. Peel BOTH layers to reach `a`: peeling one
       was await's past bug, which made it return `IO (RawIO A)`. */
    void* inner = monad_get_field_impl(monad_get_field_impl((void*)(intptr_t)box, 0), 0);
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    ok->fields[0] = inner;
    return ok;
}

/* `#[native "await_fiber"]` -- `Fiber A -> RawIO (Result I64 A)`: block
   on the condvar until the fiber stops, then its answer. */
void* monad_await_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    if (!f) return fiber_answer(NULL);
    pthread_mutex_lock(&f->lock);
    while (!f->state) pthread_cond_wait(&f->finished, &f->lock);
    pthread_mutex_unlock(&f->lock);
    return fiber_answer(f);
}

/* `#[native "poll_fiber"]` -- `Fiber A -> RawIO (Option (Result I64 A))`,
   await's non-blocking sibling: `none` while the fiber still runs, then
   `some` of await's answer. Cancellation cannot preempt
   (`fiber_mark_cancelled`'s comment), so a cancelled fiber may still be
   running, and that is `none` too; `some (err 1)` comes once it stops,
   so a poll loop on an abandoned fiber ends. */
void* monad_poll_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    int64_t done = 1;
    if (f) {
        pthread_mutex_lock(&f->lock);
        done = f->state;
        pthread_mutex_unlock(&f->lock);
    }
    if (!done) return (void*)alloc_constructor_impl(3, 0);  /* Option.none */
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
    some->fields[0] = fiber_answer(f);
    return some;
}

/* ── fiber_wait_any: park until one of N fibers stops ─────────────────

   `#[native "fiber_wait_any"]` -- `List (Fiber A) -> RawIO I64`: block
   until ANY fiber in the list has stopped, then answer the INDEX of the
   first stopped one in list order (-1 for an empty list, or when the
   caller is cancelled).

   WHY ONE SHARED CONDVAR AND NOT N. Waiting on a member's own condvar
   would serialise the scan and, with a tick, could report a win LATER
   than the 1 ms poll loop this replaces. Instead every completion
   broadcasts one process-wide condvar, and the waiter re-scans the list
   on each wake. The scan is N atomic loads of `done` with no locks
   taken, so it is cheap enough to repeat, and it cannot deadlock: no
   fiber lock is ever held while waiting.

   The list is walked with `monad_get_tag_impl(cur) == 6` (List.cons,
   head field 0, tail field 1), the same idiom `monad_build_argv` uses.

   The INDEX returns rather than the answer, so the winner is still
   consumed through the existing `await_fiber`/`pollFiber` reaping path
   and that protocol keeps exactly one implementation.

   CANCELLATION IS PUSHED, NOT POLLED. A waiter parked here can only give
   up through `monad_cancel_fiber` broadcasting this condvar; without that
   push it would have to re-check `monad_fiber_cancelled` on a timer,
   which is the 20 ms tick this used to carry. Every cancel therefore
   wakes the shared condvar (`fiber_any_wake`), the same push-a-wake shape
   P2 gave the channel waits. A broadcast carries no identity, so waking a
   waiter whose fiber was NOT the cancelled one costs one spurious re-scan
   of N atomic loads and nothing else. */

static int fiber_is_done(Fiber* f) {
    if (!f) return 1; /* a NULL handle is a fiber that never started */
    return __atomic_load_n(&f->done, __ATOMIC_ACQUIRE) != 0;
}

/* The index of the first stopped fiber in `fibers`, or -1 if none is. */
static int64_t first_done_index(void* fibers) {
    int64_t i = 0;
    for (void* cur = fibers; cur && monad_get_tag_impl(cur) == 6; ) {
        if (fiber_is_done((Fiber*)monad_get_field_impl(cur, 0))) return i;
        i++;
        cur = monad_get_field_impl(cur, 1);
    }
    return -1;
}

int64_t monad_fiber_wait_any(void* fibers) {
    /* An empty list has no value to return and would never wake; answer
       immediately rather than parking forever. */
    if (!fibers || monad_get_tag_impl(fibers) != 6) return -1;
    pthread_mutex_lock(&fiber_any_lock);
    for (;;) {
        /* Scanned under the lock: a completion broadcasts while holding
           it, so a fiber that stops after this scan but before the wait
           cannot be missed. */
        int64_t idx = first_done_index(fibers);
        if (idx >= 0) {
            pthread_mutex_unlock(&fiber_any_lock);
            return idx;
        }
        /* Checked under `fiber_any_lock`, the same lock `fiber_any_wake`
           takes to broadcast, so a cancel landing between this check and
           the wait below cannot be missed -- the classic lost-wakeup race,
           closed by doing both under one lock rather than by a timeout. */
        if (monad_fiber_cancelled()) {
            pthread_mutex_unlock(&fiber_any_lock);
            return -1;
        }
        pthread_cond_wait(&fiber_any_cond, &fiber_any_lock);
    }
}

/* Wake every `fiber_wait_any` waiter so one whose own fiber was just
   cancelled re-checks `monad_fiber_cancelled` and leaves its park. Called
   from `monad_cancel_fiber`; taken with no other lock held, exactly like
   the completion broadcast in `fiber_main`, so there is no lock order to
   get wrong. Shared by both callers rather than open-coded twice. */
static void fiber_any_wake(void) {
    pthread_mutex_lock(&fiber_any_lock);
    pthread_cond_broadcast(&fiber_any_cond);
    pthread_mutex_unlock(&fiber_any_lock);
}

void* monad_cancel_fiber(void* handle) {
    Fiber* f = (Fiber*)handle;
    if (f) {
        fiber_mark_cancelled(f);
        /* The flag alone would only be observed at the target's next bind
           (`monad_io_bind`), and a fiber parked in a channel `put`/`take`
           is not at a bind -- it is inside the native. Wake every blocked
           channel waiter so the one on the target thread re-checks the
           flag and gives its wait up promptly, instead of on the 50 ms
           tick this replaced. */
        channel_wake_cancelled();
        /* The same push for a fiber parked in `fiber_wait_any` (i.e.
           inside `race`/`select`): that wait is an untimed condvar, so
           without this broadcast a cancelled racer would only be noticed
           on the 20 ms tick it used to re-check the flag on. */
        fiber_any_wake();
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
           fibers keep running to completion in the background, and being
           detached, give their threads back when they finish; only the
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

/* --- Channels (`std/src/concurrent/channel.mo`) ---------------------

   An MVar: at most one value in flight. `put` parks while full and `take`
   parks while empty, both on one condvar, so either side can wake the
   other. Every blocked wait is a bounded `pthread_cond_timedwait` that
   re-checks `monad_fiber_cancelled`: a fiber cancelled inside `put` or
   `take` gives the lock back instead of parking forever, and the bind
   that follows short-circuits on the same flag. The value word lives in a
   GC-scanned block, so the collector traces whatever is in flight. */

typedef struct {
    Header header;
    pthread_mutex_t lock;
    pthread_cond_t changed;
    int64_t full;
    int64_t value;
} ChannelObj;

/* Every channel with a blocked waiter, so `monad_cancel_fiber` can wake it.

   WHY a registry. The wait used to be a bounded `pthread_cond_timedwait`
   re-checking `monad_fiber_cancelled` every `CHANNEL_WAIT_MS` (50 ms), so
   a cancelled fiber noticed on the next tick -- measured at ~31 ms
   (`bench/src/async_bench.mo`'s `channel_cancel_observe_us`) -- and every
   blocked fiber woke 20 times a second for the whole life of its wait.

   The cancel now pushes a wake instead of the waiter polling for it, so
   the wait is indefinite and costs nothing while nothing happens. A node
   is added before parking and removed after waking, under `chan_reg_lock`,
   which is only ever held for the list walk and never across a wait, so
   the two locks cannot deadlock against each other. A channel with no
   waiter holds no node, so a cancel touches only channels it needs to. */
typedef struct ChanReg {
    struct ChanReg* next;
    ChannelObj* chan; /* the channel this node makes the waiter reachable on */
    ChannelObj* park; /* the condvar the waiter actually sleeps on (a
                         `take_any` parks on its FIRST channel's condvar but
                         must be registered on every channel it watches) */
    int waiting;      /* >=1 while >=1 fiber is parked on `chan`'s `changed` */
} ChanReg;

static pthread_mutex_t chan_reg_lock = PTHREAD_MUTEX_INITIALIZER;
static ChanReg* chan_reg_head = NULL;

/* The parking spot of every blocked channel waiter: `park` is the condvar a
   waiter is actually inside `pthread_cond_wait` on, which for a `take_any`
   is its FIRST channel and not necessarily the `chan` its node makes it
   reachable on. Waking `park` is what releases the waiter. Collected under
   the registry lock into a fresh atomic block (channel pointers, not Monad
   words, so it must not be GC-scanned); `*out_n` is its length. */
static ChannelObj** collect_parked(size_t* out_n) {
    *out_n = 0;
    size_t n = 0;
    pthread_mutex_lock(&chan_reg_lock);
    for (ChanReg* r = chan_reg_head; r; r = r->next) {
        if (r->waiting) n++;
    }
    pthread_mutex_unlock(&chan_reg_lock);
    if (n == 0) return NULL;
    ChannelObj** spots = (ChannelObj**)monad_alloc_atomic((rt_size)(n * sizeof(ChannelObj*)));
    if (!spots) return NULL;
    size_t at = 0;
    pthread_mutex_lock(&chan_reg_lock);
    for (ChanReg* r = chan_reg_head; r && at < n; r = r->next) {
        if (!r->waiting) continue;
        spots[at++] = r->park ? r->park : r->chan;
    }
    pthread_mutex_unlock(&chan_reg_lock);
    *out_n = at;
    return spots;
}

/* Broadcast `spots[0..n)` -- each channel lock taken ALONE, never two at
   once and never with the registry held. A broadcast carries no identity,
   so a waiter that was not the intended one just re-checks and parks. */
static void wake_spots(ChannelObj** spots, size_t n) {
    if (!spots) return;
    for (size_t i = 0; i < n; i++) {
        if (!spots[i]) continue;
        pthread_mutex_lock(&spots[i]->lock);
        pthread_cond_broadcast(&spots[i]->changed);
        pthread_mutex_unlock(&spots[i]->lock);
    }
}

/* Wake every blocked channel waiter, so one whose own fiber was just
   cancelled re-checks `monad_fiber_cancelled` and leaves its park.

   LOCK ORDER -- the rule this file keeps: `chan_reg_lock` is a LEAF. A
   thread may hold at most ONE channel lock and then take the registry
   (`channel_wait` registers that way, and so do `monad_channel_put` and
   `monad_channel_take_any`), but nothing may take a channel lock while
   holding the registry, and nothing may hold two channel locks at once.
   `wake_spots` is the one way to broadcast a set: it collects under the
   registry, releases it, and takes each channel lock alone.

   The first version took each channel lock INSIDE the registry walk, which
   inverts against the registration paths above: the cancel path would hold
   `chan_reg_lock` and wait for `c->lock` while a `take_any` holds `c->lock`
   and waits for `chan_reg_lock`. That is an AB-BA deadlock on exactly the
   path this function exists for -- a cancel racing a blocked `select`, or a
   `race` loser cancelled under load. */
static void channel_wake_cancelled(void) {
    size_t n = 0;
    ChannelObj** spots = collect_parked(&n);
    wake_spots(spots, n);
}

/* Park on `c->changed` with `c->lock` held, cancelling-aware. Returns
   with `c->lock` held. Indefinite: a cancel pushes a wake (above), so
   there is nothing to poll for. */
static void channel_wait(ChannelObj* c) {
    ChanReg node;
    node.chan = c;
    node.park = c; /* a plain take parks on the very channel it registers */
    node.waiting = 1;
    pthread_mutex_lock(&chan_reg_lock);
    node.next = chan_reg_head;
    chan_reg_head = &node;
    pthread_mutex_unlock(&chan_reg_lock);

    /* Re-checked under the channel lock before parking, so a cancel that
       lands between the caller's check and this call cannot be missed. */
    if (!monad_fiber_cancelled()) {
        pthread_cond_wait(&c->changed, &c->lock);
    }

    pthread_mutex_lock(&chan_reg_lock);
    ChanReg** pp = &chan_reg_head;
    while (*pp && *pp != &node) pp = &(*pp)->next;
    if (*pp) *pp = node.next;
    pthread_mutex_unlock(&chan_reg_lock);
}

void* monad_channel_new(void) {
    ChannelObj* c = (ChannelObj*)monad_alloc(sizeof(ChannelObj));
    if (!c) return NULL;
    c->header.tag = MONAD_CHANNEL_TAG;
    pthread_mutex_init(&c->lock, NULL);
    pthread_cond_init(&c->changed, NULL);
    c->full = 0;
    c->value = 0;
    return c;
}

void* monad_channel_put(void* handle, int64_t value) {
    ChannelObj* c = (ChannelObj*)handle;
    if (c) {
        pthread_mutex_lock(&c->lock);
        while (c->full && !monad_fiber_cancelled()) channel_wait(c);
        if (!monad_fiber_cancelled()) {
            c->value = value;
            c->full = 1;
            pthread_cond_broadcast(&c->changed);
            /* A `select`/`channel_take_any` waiter parks on the condvar of
               the FIRST channel in its list, which may not be this one --
               so it is asleep on a condvar the broadcast above does not
               reach. Without waking those spots too, a value arriving on a
               non-first channel never releases the select, which then blocks
               forever (`check_channel_take_any` in thread_stress.c).

               So the OTHER spots are collected here -- one channel lock
               (`c->lock`, already held) plus the registry, which is the
               permitted order -- and broadcast only after `c->lock` is
               released, through `wake_spots`. Taking `spot->lock` inline
               would hold two channel locks at once, the inversion
               `channel_wake_cancelled` documents; the value stays in
               `c->full`, so a waiter woken after the release still finds
               it. */
            size_t nspots = 0;
            ChannelObj** spots = collect_parked(&nspots);
            pthread_mutex_unlock(&c->lock);
            wake_spots(spots, nspots);
            return alloc_constructor_impl(0, 0);
        }
        pthread_mutex_unlock(&c->lock);
    }
    return alloc_constructor_impl(0, 0);
}

int64_t monad_channel_take(void* handle) {
    ChannelObj* c = (ChannelObj*)handle;
    if (!c) return 0;
    int64_t value = 0;
    pthread_mutex_lock(&c->lock);
    while (!c->full && !monad_fiber_cancelled()) channel_wait(c);
    /* A cancelled fiber gives the wait up WITHOUT consuming a value that
       arrived at the same moment: the flag wins. */
    if (c->full && !monad_fiber_cancelled()) {
        value = c->value;
        c->full = 0;
        pthread_cond_broadcast(&c->changed);
    }
    pthread_mutex_unlock(&c->lock);
    return value;
}

/* `#[native "channel_take_any"]` -- `List (Channel A) -> RawIO
   (Option A)`: block until any channel in the list holds a value, then
   take it; `Option.none` when the waiting fiber was cancelled or the
   list is empty. An `Option` and not a bare payload because `A` is
   generic: there is no value of `A` to mean "nothing".

   WHAT SELECT NEEDED. It used to poll every channel with `tryTake` once a
   millisecond; this parks once instead.

   EVERY channel in the list gets its OWN registry node, so a put on ANY
   of them broadcasts a condvar this waiter is parked on. Registering only
   the first channel (the original shape) DOES NOT WORK: the waiter parks
   on channel 0's condvar, and `monad_channel_put` broadcasts only the
   channel it wrote to -- so a value arriving on channel 1 never woke the
   waiter, which then blocked forever inside `pthread_cond_wait`. That is
   a hang, not a slow path, and `runtime/tests/thread_stress.c`'s
   `check_channel_take_any` reproduces it. A broadcast has no payload, so
   a wake on a channel the scan then finds EMPTY costs one re-scan and
   nothing else.

   The nodes are one small ATOMIC allocation (not GC-scanned: they hold
   channel pointers, not Monad words the collector traces), and every one
   is unlinked before returning, so nothing outside this call can reach
   them. */
void* monad_channel_take_any(void* chans) {
    if (!chans || monad_get_tag_impl(chans) != 6) {
        return (void*)alloc_constructor_impl(3, 0); /* Option.none */
    }
    int64_t value = 0;
    int64_t got = 0;
    /* One node per channel, plus a count so teardown knows how many. A
       fixed-size array would cap the API at that size, so the array is
       allocated to fit the list. */
    int64_t n = 0;
    for (void* cur = chans; cur && monad_get_tag_impl(cur) == 6;
         cur = monad_get_field_impl(cur, 1)) {
        if (monad_get_field_impl(cur, 0)) n++;
    }
    if (n == 0) return (void*)alloc_constructor_impl(3, 0); /* Option.none */
    /* ATOMIC (unscanned): the array holds channel POINTERS, not Monad
       words the collector must trace, and reading it as a scanned block
       would make Boehm treat the nodes as live objects. It is stack-lifetime
       data that merely has to outlive the registry entries pointing at it,
       which the teardown below guarantees. */
    ChanReg* nodes = (ChanReg*)monad_alloc_atomic((rt_size)(n * (int64_t)sizeof(ChanReg)));
    if (!nodes) return (void*)alloc_constructor_impl(3, 0);

    ChannelObj* park = (ChannelObj*)monad_get_field_impl(chans, 0);
    pthread_mutex_lock(&chan_reg_lock);
    int64_t at = 0;
    for (void* cur = chans; cur && monad_get_tag_impl(cur) == 6;
         cur = monad_get_field_impl(cur, 1)) {
        ChannelObj* c = (ChannelObj*)monad_get_field_impl(cur, 0);
        if (!c) continue;
        nodes[at].chan = c;
        /* EVERY node parks on the first channel's condvar: that is where
           this call actually sleeps, so any wake must be delivered there. */
        nodes[at].park = park;
        nodes[at].waiting = 1;
        nodes[at].next = chan_reg_head;
        chan_reg_head = &nodes[at];
        at++;
    }
    pthread_mutex_unlock(&chan_reg_lock);

    for (;;) {
        for (void* cur = chans; cur && monad_get_tag_impl(cur) == 6; ) {
            ChannelObj* c = (ChannelObj*)monad_get_field_impl(cur, 0);
            if (c) {
                pthread_mutex_lock(&c->lock);
                if (c->full) {
                    value = c->value;
                    c->full = 0;
                    got = 1;
                    /* Wake this channel's own put-waiters. The registry
                       scan that used to guard this broadcast could only
                       ever have broadcast `c->changed` itself, so it is
                       dropped: `c->lock` is held here, and taking the
                       registry under it for a lookup that changes nothing
                       is the inversion `channel_wake_cancelled` documents. */
                    pthread_cond_broadcast(&c->changed);
                }
                pthread_mutex_unlock(&c->lock);
                if (got) break;
            }
            cur = monad_get_field_impl(cur, 1);
        }
        if (got) break;
        if (monad_fiber_cancelled()) break;
        /* Park on the FIRST channel's condvar; every node registered above
           names this spot in its `park` field, so a put on any of them can
           wake this wait through it. `pthread_cond_wait` needs the
           channel's lock held. */
        pthread_mutex_lock(&park->lock);
        if (!monad_fiber_cancelled()) {
            pthread_cond_wait(&park->changed, &park->lock);
        }
        pthread_mutex_unlock(&park->lock);
    }

    pthread_mutex_lock(&chan_reg_lock);
    for (int64_t i = 0; i < at; i++) {
        ChanReg** pp = &chan_reg_head;
        while (*pp && *pp != &nodes[i]) pp = &(*pp)->next;
        if (*pp) *pp = nodes[i].next;
    }
    pthread_mutex_unlock(&chan_reg_lock);

    /* The nodes are no longer registered, so nothing can reach them; the
       block is left to the collector rather than freed, since the runtime
       has no `free` for a GC block and the wait's per-call cost is one
       small allocation on a path that just blocked. */
    if (!got) return (void*)alloc_constructor_impl(3, 0); /* Option.none */
    Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
    some->fields[0] = (void*)(intptr_t)value;
    return some;
}

void* monad_channel_try_take(void* handle) {
    ChannelObj* c = (ChannelObj*)handle;
    int64_t value = 0;
    int64_t got = 0;
    if (c) {
        pthread_mutex_lock(&c->lock);
        if (c->full) {
            value = c->value;
            c->full = 0;
            got = 1;
            pthread_cond_broadcast(&c->changed);
        }
        pthread_mutex_unlock(&c->lock);
    }
    if (got) {
        Constructor* some = (Constructor*)alloc_constructor_impl(4, 1);
        some->fields[0] = (void*)(intptr_t)value;
        return some;
    }
    return alloc_constructor_impl(3, 0);
}

/* SIGPIPE back to its default action, for a stdio writer about to die of
   it (`stdio_die_on_epipe`). Spawned children get the same reset from
   `spawn_child`'s attributes. */
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

/* ── Descriptor inheritance ───────────────────────────────────────────
 * Every descriptor the runtime creates is close-on-exec: a child gets
 * its dup2'd 0/1/2 and nothing else. Without that, a child spawned by
 * one fiber holds the pipes and sockets of every other fiber's work,
 * and the peer never sees EOF while that child lives.
 *
 * Setting FD_CLOEXEC after the fact leaves a window in which another
 * thread can spawn a child with the descriptor still inheritable. This
 * file defines no _GNU_SOURCE, so pipe2(2) is not declared; instead
 * creation and the fcntl happen under `fork_lock` held shared, and every
 * spawn holds it exclusively (the shape of Go's syscall.ForkLock). The
 * lock is never held across a blocking call, so a spawn waits at most
 * for one pipe() or socket() and its fcntl. accept(2) blocks, so it
 * cannot take the lock: on Linux it is accept4(SOCK_CLOEXEC), and
 * elsewhere a narrow window remains. `monad_stream_open` passes
 * O_CLOEXEC to open(2) itself. */
static pthread_rwlock_t fork_lock = PTHREAD_RWLOCK_INITIALIZER;

static void set_cloexec(int fd) {
    fcntl(fd, F_SETFD, FD_CLOEXEC);
}

static int cloexec_pipe(int p[2]) {
    pthread_rwlock_rdlock(&fork_lock);
    int rc = pipe(p);
    if (rc == 0) {
        set_cloexec(p[0]);
        set_cloexec(p[1]);
    }
    pthread_rwlock_unlock(&fork_lock);
    return rc;
}

static int cloexec_socket(int domain, int type, int protocol) {
    pthread_rwlock_rdlock(&fork_lock);
    int fd = socket(domain, type, protocol);
    if (fd >= 0) set_cloexec(fd);
    pthread_rwlock_unlock(&fork_lock);
    return fd;
}

#if defined(__linux__)
/* Exported by glibc and musl alike; declared only under _GNU_SOURCE. */
int accept4(int fd, struct sockaddr* addr, socklen_t* len, int flags);
#endif

static int cloexec_accept(int listener) {
#if defined(__linux__)
    return accept4(listener, NULL, NULL, SOCK_CLOEXEC);
#else
    int fd = accept(listener, NULL, NULL);
    if (fd >= 0) set_cloexec(fd);
    return fd;
#endif
}

extern char** environ;

/* Spawn `argv` with stdin/stdout/stderr from `in_fd`/`out_fd`/`err_fd`
   (-1 inherits) and SIGPIPE back at its default (`main` ignores it, and
   SIG_IGN survives exec). posix_spawnp, not fork: glibc spawns with a
   CLONE_VFORK that copies no page tables, where a fork of a multi-GB
   heap took a second per child. Holds `fork_lock` exclusively, so no
   descriptor is half-created. Returns 0, or the errno of a spawn that
   never happened -- exec failure included. */
static int spawn_child(pid_t* pid, const char* cmd, char** argv, int in_fd, int out_fd, int err_fd) {
    posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;
    int rc = posix_spawn_file_actions_init(&fa);
    if (rc != 0) return rc;
    rc = posix_spawnattr_init(&attr);
    if (rc != 0) {
        posix_spawn_file_actions_destroy(&fa);
        return rc;
    }
    sigset_t defaults;
    sigemptyset(&defaults);
    sigaddset(&defaults, SIGPIPE);
    posix_spawnattr_setsigdefault(&attr, &defaults);
    posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETSIGDEF);
    if (in_fd >= 0) posix_spawn_file_actions_adddup2(&fa, in_fd, 0);
    if (out_fd >= 0) posix_spawn_file_actions_adddup2(&fa, out_fd, 1);
    if (err_fd >= 0) posix_spawn_file_actions_adddup2(&fa, err_fd, 2);
    pthread_rwlock_wrlock(&fork_lock);
    rc = posix_spawnp(pid, cmd, &fa, &attr, argv, environ);
    pthread_rwlock_unlock(&fork_lock);
    posix_spawnattr_destroy(&attr);
    posix_spawn_file_actions_destroy(&fa);
    return rc;
}

/* `exec_cmd` IS NO LONGER A NATIVE. `std/src/process.mo` builds it on
   `monad_proc_spawn`'s inherit flag plus `monad_proc_wait`; what remains
   here is the bootstrap shim `monad_exec_cmd` below and the redirect that
   `monad_proc_spawn`'s `flags == 1` arm reads (`exec_child_out_fd`).

   It is THE load-bearing operation for the bootstrap ladder either way:
   lang/codegen/link.mo shells out to `llc` and `clang` through `exec_cmd`,
   so without a working spawn a self-compiled compiler can never run its
   own `compile` command at all. `monad_proc_spawn` reproduces everything
   this comment used to promise -- the child's exit code, 127 when the
   command could not be executed, -1 when no child could be created or it
   died on a signal (the reference's `status.code().unwrap_or(-1)`) -- and
   `Proc.spawn` + `Proc.wait` surface it. */
/* `#[native "exec_child_output"]` (std/process.mo, `Process.quiet_terminal`).
   Unset (-1), this process writes its own diagnostics to the terminal and
   an `exec_cmd` child inherits stdin/stdout/stderr -- what the compiler's
   own llc/clang calls want. Set, for a full-screen program (weaver's TUI):
   fd 2 itself is pointed at the file, so this process's own stderr (a GC
   warning, a runtime diagnostic) lands there too, and every later
   `exec_cmd` child reads /dev/null and writes stdout and stderr to the
   file. An empty path restores the saved stderr and inheritance. Returns
   0, or -errno when the file cannot be opened. */
static int exec_child_out_fd = -1;
static int saved_stderr_fd = -1;

int64_t monad_exec_child_output(char* path) {
    if (exec_child_out_fd >= 0) { close(exec_child_out_fd); exec_child_out_fd = -1; }
    if (saved_stderr_fd >= 0) {
        fflush(stderr);
        dup2(saved_stderr_fd, 2);
        close(saved_stderr_fd);
        saved_stderr_fd = -1;
    }
    if (!path || !path[0]) return 0;
    int fd = open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0600);
    if (fd < 0) return -(int64_t)errno;
    fflush(stderr);
    saved_stderr_fd = fcntl(2, F_DUPFD_CLOEXEC, 3);
    if (saved_stderr_fd >= 0) dup2(fd, 2);
    exec_child_out_fd = fd;
    return 0;
}

/* BOOTSTRAP SHIM, not a native: nothing in this tree declares or calls it.
   `exec_cmd` (std/src/process.mo) is ordinary Monad over `proc_spawn` +
   `proc_wait` now, but a host compiler built before that change (the
   published nightly, an older rung) still emits calls to this symbol for
   `exec_cmd` and links the CHECKOUT's runtime -- so without it such a host
   cannot build this tree. Same rule as `monad_print_str` above. Delete it
   once a nightly that predates the rebuild is the oldest host anyone
   builds with.

   Kept byte-compatible with the old behaviour on purpose: this is what the
   `inherit` flag of `monad_proc_spawn` reproduces, including the
   `/dev/null` stdin and the `exec_child_out_fd` redirect. */
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

    pid_t pid;
    int out_fd = exec_child_out_fd;
    int in_fd = out_fd >= 0 ? open("/dev/null", O_RDONLY | O_CLOEXEC) : -1;
    int rc = spawn_child(&pid, cmd, argv, in_fd, out_fd, out_fd);
    if (in_fd >= 0) close(in_fd);
    free(argv);
    if (rc != 0) return (rc == EAGAIN || rc == ENOMEM) ? -1 : 127;
    int status = 0;
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
 * Locked: every fiber is an OS thread, so two fibers may spawn or reap
 * at once. `proc_registry_lock` covers claiming and releasing a slot and
 * reading its fields. It is never held across a spawn, `read` or
 * `waitpid`. */
#define MONAD_PROC_MAX 64

typedef struct {
    pid_t pid;
    int in_fd;   /* parent's write end of the child's stdin */
    int out_fd;  /* parent's read end of the child's stdout */
    int err_fd;  /* parent's read end of the child's stderr */
    int live;
} ProcChild;

static ProcChild proc_registry[MONAD_PROC_MAX];
static pthread_mutex_t proc_registry_lock = PTHREAD_MUTEX_INITIALIZER;

/* Caller holds `proc_registry_lock`. */
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
 * EXEC FAILURE IS AN ERROR, not a child that exits 127: `spawn_child`
 * reports the errno of a spawn that never happened, the same
 * `Result.err` the Rust host's `Command::spawn` already reports, which
 * is the contract `std/src/process.mo` declares. */
void* monad_proc_spawn(char* cmd, void* args, int64_t flags) {
    char** argv = monad_build_argv(cmd, args);
    if (!argv) return stream_err(9, "proc_spawn", "out of memory", 0);

    /* `flags` merges the two spawn shapes behind one native rather than
       duplicating it (AGENTS.md's merge-twins rule):
         0 = pipe all three streams (the protocol shape `Proc.spawn` wants)
         1 = the `exec_cmd` shape: stdout/stderr go where this process's
             OWN `monad_exec_child_output` redirect points (or the real
             stdout/stderr when none is set), and stdin is /dev/null.
       That is deliberately NOT `spawn_child(..., -1, -1, -1)` ("leave the
       fds alone"). `Process.quiet_terminal` redirects THIS PROCESS's fd 1
       and 2 and remembers them in `exec_child_out_fd`; a plain inherit
       would therefore hand the child the redirect too, which looks like
       it works -- but it also leaves the child reading the keyboard,
       the one thing `quiet_terminal` promises it will not do. Reusing
       `exec_child_out_fd` here is what keeps `exec_cmd` byte-for-byte
       the behaviour its own native had (see `monad_exec_cmd`, which this
       replaces).
       The registry entry still exists either way, so `Proc.wait`/
       `Proc.kill` work on an inherited child exactly as on a piped one;
       only `proc_stream_fd` answers -1 (dead view), which is correct --
       there is no parent-side pipe to read. */
    if (flags == 1) {
        fflush(NULL);
        int hout = exec_child_out_fd;
        int hin = hout >= 0 ? open("/dev/null", O_RDONLY | O_CLOEXEC) : -1;
        pid_t hpid;
        int hrc = spawn_child(&hpid, cmd, argv, hin, hout, hout);
        if (hin >= 0) close(hin);
        free(argv);
        if (hrc != 0) return stream_os_err("proc_spawn", hrc);
        int hslot = -1;
        pthread_mutex_lock(&proc_registry_lock);
        for (int k = 0; k < MONAD_PROC_MAX; k++) {
            if (!proc_registry[k].live) { hslot = k; break; }
        }
        if (hslot >= 0) {
            proc_registry[hslot].pid = hpid;
            proc_registry[hslot].in_fd = -1;
            proc_registry[hslot].out_fd = -1;
            proc_registry[hslot].err_fd = -1;
            proc_registry[hslot].live = 1;
        }
        pthread_mutex_unlock(&proc_registry_lock);
        if (hslot < 0) {
            kill(hpid, SIGKILL);
            waitpid(hpid, NULL, 0);
            return stream_err(9, "proc_spawn", "child registry full", 0);
        }
        return tcp_ok((void*)(int64_t)(hslot + 1));
    }
    if (flags != 0) return stream_err(22, "proc_spawn", "unknown stdio flag", 0);

    int in_pipe[2], out_pipe[2], err_pipe[2];
    if (cloexec_pipe(in_pipe) < 0) {
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    if (cloexec_pipe(out_pipe) < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    if (cloexec_pipe(err_pipe) < 0) {
        close(in_pipe[0]); close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        free(argv);
        return stream_os_err("proc_spawn", errno);
    }
    fflush(NULL); /* same ordering concern as `monad_exec_cmd` */

    /* Every pipe end is CLOEXEC, so the child keeps only its dup2'd
       0/1/2. A failed spawn leaves no registry entry and no fds. */
    pid_t pid;
    int rc = spawn_child(&pid, cmd, argv, in_pipe[0], out_pipe[1], err_pipe[1]);
    free(argv);
    close(in_pipe[0]);
    close(out_pipe[1]);
    close(err_pipe[1]);
    if (rc != 0) {
        close(in_pipe[1]); close(out_pipe[0]); close(err_pipe[0]);
        return stream_os_err("proc_spawn", rc);
    }

    int slot = -1;
    pthread_mutex_lock(&proc_registry_lock);
    for (int k = 0; k < MONAD_PROC_MAX; k++) {
        if (!proc_registry[k].live) { slot = k; break; }
    }
    if (slot >= 0) {
        proc_registry[slot].pid = pid;
        proc_registry[slot].in_fd = in_pipe[1];
        proc_registry[slot].out_fd = out_pipe[0];
        proc_registry[slot].err_fd = err_pipe[0];
        proc_registry[slot].live = 1;
    }
    pthread_mutex_unlock(&proc_registry_lock);
    if (slot < 0) {
        /* Refuse rather than hand back a child nobody could ever reap:
         * the registry's size is the bound on leaked children, and a
         * spawn that cannot be recorded is torn down on the spot. */
        kill(pid, SIGKILL);
        close(in_pipe[1]); close(out_pipe[0]); close(err_pipe[0]);
        waitpid(pid, NULL, 0);
        return stream_err(9, "proc_spawn", "child registry full", 0);
    }
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
    int64_t fd = -1;
    pthread_mutex_lock(&proc_registry_lock);
    ProcChild* pc = proc_slot(handle);
    if (pc) {
        if (which == 0) fd = pc->in_fd;
        else if (which == 1) fd = pc->out_fd;
        else if (which == 2) fd = pc->err_fd;
    }
    pthread_mutex_unlock(&proc_registry_lock);
    return fd;
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
    /* Copy the entry out and free the slot under the lock, so a racing
       second `wait` on the same handle sees it dead instead of closing
       the descriptors twice. The child is still unreaped here, so its
       pid cannot have been recycled before the `kill` below. */
    pthread_mutex_lock(&proc_registry_lock);
    ProcChild* pc = proc_slot(handle);
    ProcChild child;
    if (pc) {
        child = *pc;
        pc->live = 0;
    }
    pthread_mutex_unlock(&proc_registry_lock);
    if (!pc) return -1;
    if (kill_first) kill(child.pid, SIGKILL);
    stream_carry_clear(child.in_fd);
    stream_carry_clear(child.out_fd);
    stream_carry_clear(child.err_fd);
    close(child.in_fd);
    close(child.out_fd);
    close(child.err_fd);
    pid_t pid = child.pid;
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    return WIFEXITED(status) ? (int64_t)WEXITSTATUS(status) : -1;
}

/* `proc_kill_group : I64 -> I64 -> RawIO I64` -- `killpg`, else `kill`
 * on the bare pid; 0 on delivery, -1 otherwise. `pgid < 2` and signals
 * outside 0..64 are refused: 0 and -1 would address every process the
 * caller may signal, and 1 is init. */
int64_t monad_proc_kill_group(int64_t pgid, int64_t sig) {
    if (pgid < 2 || pgid > INT32_MAX || sig < 0 || sig > 64) return -1;
    if (killpg((pid_t)pgid, (int)sig) == 0) return 0;
    return kill((pid_t)pgid, (int)sig) == 0 ? 0 : -1;
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

static void crash_path_init(void);
static void install_crash_handlers(void);
static int g_crash_handlers_installed = 0;

static void maybe_install_crash_handlers(void) {
    if (g_crash_handlers_installed) return;
    g_crash_handlers_installed = 1;
    crash_path_init();
    install_crash_handlers();
}

static int64_t term_ctl_enter_raw(void) {
    struct termios t;
    if (tcgetattr(STDIN_FILENO, &t) != 0) return 0;
    /* Only a program that takes the terminal gets the terminal-restore
       handler and the crash marker. A plain CLI tool must not emit
       escape sequences or weaver markers on SIGTERM. */
    maybe_install_crash_handlers();
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

/* --- Fatal-signal report ---------------------------------------------
 *
 * A segfault or an external SIGTERM used to strand the alternate screen:
 * the tui restores the terminal only on its controlled exit path, and the
 * runtime installed no handler at all. This handler is deliberately
 * async-signal-safe (write/tcsetattr/open/close/raise only, no malloc,
 * no printf, no Boehm calls): it restores the saved termios, emits the
 * generic reset sequence, appends one marker line to a path computed at
 * startup, then re-raises so the exit status still names the signal.
 *
 * The marker path is decided ONCE in main (snprintf there, not in the
 * handler): WEAVER_CRASH_FILE, else $WEAVER_LOG_DIR/crash-<pid>.log,
 * else $HOME/.weaver/crash-<pid>.log, else /tmp/monad-crash-<pid>.log.
 * Weaver reports and removes it on the next launch (`ev=crash_signal`).
 */
static char g_crash_path[512];
static int g_crash_path_ready = 0;
static volatile sig_atomic_t g_crash_active = 0;

static void crash_path_init(void) {
    const char* explicit_path = getenv("WEAVER_CRASH_FILE");
    const char* log_dir = getenv("WEAVER_LOG_DIR");
    if (explicit_path && *explicit_path)
        snprintf(g_crash_path, sizeof g_crash_path, "%s", explicit_path);
    else if (log_dir && *log_dir)
        snprintf(g_crash_path, sizeof g_crash_path, "%s/crash-%ld.log", log_dir, (long)getpid());
    else
        snprintf(g_crash_path, sizeof g_crash_path, "/tmp/monad-crash-%ld.log", (long)getpid());
    g_crash_path_ready = 1;
}

static void crash_write_all(int fd, const char* s, size_t n) {
    while (n > 0) {
        ssize_t w = write(fd, s, n);
        if (w <= 0) return;
        s += w;
        n -= (size_t)w;
    }
}

static char* crash_put_uint(char* out, unsigned long long v) {
    char tmp[24];
    int n = 0;
    if (v == 0) { *out++ = '0'; return out; }
    while (v > 0) { tmp[n++] = (char)('0' + (v % 10)); v /= 10; }
    while (n > 0) *out++ = tmp[--n];
    return out;
}

static void crash_handler(int sig) {
    if (g_crash_active) {
        signal(sig, SIG_DFL);
        raise(sig);
        return;
    }
    g_crash_active = 1;

    static const char reset[] =
        "\x1b[0m\x1b[?1002l\x1b[?1006l\x1b[?2004l\x1b[?7h\x1b[?1049l\x1b[?25h";
    if (g_term_ctl_saved_valid) {
        tcsetattr(STDIN_FILENO, TCSAFLUSH, &g_term_ctl_saved);
        g_term_ctl_saved_valid = 0;
    }
    crash_write_all(STDOUT_FILENO, reset, sizeof reset - 1);
    crash_write_all(STDERR_FILENO, reset, sizeof reset - 1);

    if (g_crash_path_ready) {
        int fd = open(g_crash_path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
        if (fd >= 0) {
            char line[128];
            char* p = line;
            const char* head = "monad crash signal=";
            while (*head) *p++ = *head++;
            p = crash_put_uint(p, (unsigned long long)sig);
            const char* mid = " pid=";
            while (*mid) *p++ = *mid++;
            p = crash_put_uint(p, (unsigned long long)getpid());
            *p++ = '\n';
            crash_write_all(fd, line, (size_t)(p - line));
            close(fd);
        }
    }

    signal(sig, SIG_DFL);
    raise(sig);
}

/* A stack-overflow SIGSEGV cannot run a handler on the exhausted stack:
   give the handler an alternate one. `union` guarantees the alignment
   sigaltstack requires. */
static union {
    char bytes[65536];
    long double align;
} g_alt_stack;

static void install_crash_handlers(void) {
    stack_t ss;
    memset(&ss, 0, sizeof ss);
    ss.ss_sp = g_alt_stack.bytes;
    ss.ss_size = sizeof g_alt_stack.bytes;
    sigaltstack(&ss, NULL);
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = crash_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESETHAND | SA_ONSTACK;
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGHUP, &sa, NULL);
    sigaction(SIGABRT, &sa, NULL);
    sigaction(SIGFPE, &sa, NULL);
    sigaction(SIGILL, &sa, NULL);
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
static int poll_one(struct pollfd* pfd, int64_t timeout_ms);

static int64_t term_ctl_poll(int64_t timeout_ms) {
    struct pollfd pfd;
    pfd.fd = STDIN_FILENO;
    pfd.events = POLLIN;
    pfd.revents = 0;
    int rc = poll_one(&pfd, timeout_ms);
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

/* `#[native "clock_now"]` (std/io.mo's `IO.epoch_time_nano`) --
   clock_gettime: 0 is CLOCK_REALTIME, 1 is CLOCK_MONOTONIC, in ns;
   -errno on failure, the sys floor's convention (sys/src/raw.mo). */
int64_t monad_clock_now(int64_t clock) {
    if (clock != 0 && clock != 1) return -(int64_t)EINVAL;
    struct timespec ts;
    if (clock_gettime(clock == 1 ? CLOCK_MONOTONIC : CLOCK_REALTIME, &ts) != 0) return -(int64_t)errno;
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

/* `#[native "sys_int"]` (sys/src/raw.mo, the OS floor's integer call).
   One entry point for the scalar syscalls so the floor costs one native:
   `op` selects the call, unused arguments are 0, and a failure is
   `-errno` (the `I64` convention the floor's `.mo` wrappers decode with
   `SysError.of_errno`). `getpriority` is the one call whose result can
   legitimately be negative, so it clears `errno` first and only reports a
   value when `errno` stayed clear. */
int64_t monad_sys_int(int64_t op, int64_t a, int64_t b) {
    switch (op) {
    case 0: return (int64_t)getpid();
    case 1: return (int64_t)getppid();
    case 2: return (int64_t)getuid();
    case 3: return (int64_t)geteuid();
    case 4:
        if (kill((pid_t)a, (int)b) != 0) return -(int64_t)errno;
        return 0;
    case 5: {
        errno = 0;
        int prio = getpriority(PRIO_PROCESS, (id_t)a);
        if (errno != 0) return -(int64_t)errno;
        return (int64_t)prio;
    }
    case 6:
        if (setpriority(PRIO_PROCESS, (id_t)a, (int)b) != 0) return -(int64_t)errno;
        return 0;
    case 7:
        switch (a) {
        case 0: return (int64_t)sysconf(_SC_CLK_TCK);
        case 1: return (int64_t)sysconf(_SC_PAGESIZE);
        case 2: return (int64_t)sysconf(_SC_NPROCESSORS_ONLN);
        default: return -(int64_t)EINVAL;
        }
    default: return -(int64_t)EINVAL;
    }
}

/* `Result`/`Option` construction for the floor's string-shaped calls:
   `ok` is tag 10 and `err` tag 11 (the fixed prelude tags `tcp_ok` above
   uses); a field is a raw word, so a `char*` and an `int64_t` go in
   directly. */
static void* sys_ok_str(char* s) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = s;
    return ok;
}

static void* sys_err(int64_t e) {
    Constructor* err = (Constructor*)alloc_constructor_impl(11, 1);
    if (err) err->fields[0] = (void*)e;
    return err;
}

/* An ok payload that is a WORD, not a string: an opaque handle (`Dir`).
   The Monad side never inspects it, so no representation is promised
   beyond "it round-trips to the next sys_dir call". */
static void* sys_ok_word(int64_t w) {
    Constructor* ok = (Constructor*)alloc_constructor_impl(10, 1);
    if (ok) ok->fields[0] = (void*)w;
    return ok;
}

/* A GC-owned copy of `len` bytes plus a terminator, from a byte range that
   may not be NUL-terminated (`readlink`, `/proc` reads). */
static char* sys_copy_bytes(const char* src, size_t len) {
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (!copy) return NULL;
    memcpy(copy, src, len);
    copy[len] = '\0';
    return copy;
}

/* `#[native "sys_str"]` (sys/src/raw.mo): the floor's string-shaped
   syscalls, `Result.err <errno>` on failure. `op` selects the call:
   0 readlink, 1 uname field, 2 getenv, 3 read_small (open/read-to-EOF/
   close, for /proc and /sys files, which stat() as size 0).

   Directory listing is NOT here any more: it is the `sys_dir_*` family
   below, whose loop lives in `sys/src/sys.mo`. */
void* monad_sys_str(int64_t op, char* arg) {
    switch (op) {
    case 0: {
        if (!arg) return sys_err(EINVAL);
        size_t cap = 256;
        for (;;) {
            char* buf = (char*)monad_alloc_atomic(cap);
            if (!buf) return sys_err(ENOMEM);
            ssize_t n = readlink(arg, buf, cap);
            if (n < 0) return sys_err(errno);
            if ((size_t)n < cap) return sys_ok_str(sys_copy_bytes(buf, (size_t)n));
            cap *= 2;
            if (cap > (1u << 20)) return sys_err(ENAMETOOLONG);
        }
    }
    case 1: {
        struct utsname u;
        if (uname(&u) != 0) return sys_err(errno);
        const char* field = "sysname";
        if (arg) field = arg;
        const char* v;
        if (strcmp(field, "sysname") == 0) v = u.sysname;
        else if (strcmp(field, "release") == 0) v = u.release;
        else if (strcmp(field, "machine") == 0) v = u.machine;
        else if (strcmp(field, "nodename") == 0) v = u.nodename;
        else return sys_err(EINVAL);
        char* copy = sys_copy_bytes(v, strlen(v));
        return copy ? sys_ok_str(copy) : sys_err(ENOMEM);
    }
    case 2: {
        const char* val = arg ? getenv(arg) : NULL;
        if (!val) return sys_err(ENOENT);
        char* copy = sys_copy_bytes(val, strlen(val));
        return copy ? sys_ok_str(copy) : sys_err(ENOMEM);
    }
    case 3: {
        int fd = arg ? open(arg, O_RDONLY) : -1;
        if (fd < 0) return sys_err(errno);
        size_t cap = 4096, n = 0;
        char* buf = (char*)monad_alloc_atomic(cap);
        if (!buf) { close(fd); return sys_err(ENOMEM); }
        for (;;) {
            if (n == cap) {
                size_t grown_cap = cap * 2;
                char* grown = (char*)monad_alloc_atomic(grown_cap);
                if (!grown) { close(fd); return sys_err(ENOMEM); }
                memcpy(grown, buf, n);
                buf = grown;
                cap = grown_cap;
            }
            ssize_t got = read(fd, buf + n, cap - n);
            if (got < 0) {
                if (errno == EINTR) continue;
                int e = errno;
                close(fd);
                return sys_err(e);
            }
            if (got == 0) break;
            n += (size_t)got;
        }
        close(fd);
        return sys_ok_str(sys_copy_bytes(buf, n));
    }
    default: return sys_err(EINVAL);
    }
}

/* `#[native "sys_dir_open"|"sys_dir_next"|"sys_dir_close"]`
   (sys/src/raw.mo): `opendir`/`readdir`/`closedir` as three calls, so the
   listing loop is Monad (`Sys.list_dir`) instead of a C function that
   joins entries into one string.

   The handle is the `DIR*` itself, wrapped in a `Result.ok` word; Monad
   treats it as opaque (`Dir`) and the interpreter uses a registry slot
   instead -- the same split `FdStream` and `Child` use, and the two
   never mix because a handle never leaves the backend that made it.

   `sys_dir_next` answers an EMPTY name at the end of the stream (POSIX
   never yields one), so end-of-dir needs no errno: `readdir` sets errno
   only on a real failure, which is reported as `Result.err <errno>`. */
void* monad_sys_dir_open(char* path) {
    if (!path) return sys_err(EINVAL);
    DIR* d = opendir(path);
    if (!d) return sys_err(errno);
    return sys_ok_word((int64_t)(intptr_t)d);
}

void* monad_sys_dir_next(void* handle) {
    DIR* d = (DIR*)handle;
    if (!d) return sys_err(EBADF);
    for (;;) {
        errno = 0;
        struct dirent* e = readdir(d);
        if (!e) {
            if (errno != 0) return sys_err(errno);
            return sys_ok_str(sys_copy_bytes("", 0));
        }
        if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
        char* copy = sys_copy_bytes(e->d_name, strlen(e->d_name));
        return copy ? sys_ok_str(copy) : sys_err(ENOMEM);
    }
}

void* monad_sys_dir_close(void* handle) {
    DIR* d = (DIR*)handle;
    if (!d) return (void*)(int64_t)-EBADF;
    if (closedir(d) != 0) return (void*)(int64_t)(-errno);
    return (void*)0;
}

/* `#[native "sys_stat"]` (sys/src/raw.mo): `stat`/`lstat` fields and
   `statvfs`, packed as space-separated decimal words because the floor may
   not name a `ByteBuf`. The Monad side splits them; the order is the
   contract:
   0 stat(path)    -> "mode size mtime"
   1 lstat(path)   -> the same, without following a symlink
   2 statvfs(path) -> "bsize frsize blocks bfree bavail files ffree" */
void* monad_sys_stat(int64_t op, char* path) {
    if (!path) return sys_err(EINVAL);
    char out[256];
    if (op == 2) {
        struct statvfs v;
        if (statvfs(path, &v) != 0) return sys_err(errno);
        snprintf(out, sizeof out, "%llu %llu %llu %llu %llu %llu %llu",
                 (unsigned long long)v.f_bsize, (unsigned long long)v.f_frsize,
                 (unsigned long long)v.f_blocks, (unsigned long long)v.f_bfree,
                 (unsigned long long)v.f_bavail, (unsigned long long)v.f_files,
                 (unsigned long long)v.f_ffree);
        return sys_ok_str(sys_copy_bytes(out, strlen(out)));
    }
    if (op != 0 && op != 1) return sys_err(EINVAL);
    struct stat st;
    int rc = op == 1 ? lstat(path, &st) : stat(path, &st);
    if (rc != 0) return sys_err(errno);
    snprintf(out, sizeof out, "%llu %lld %lld",
             (unsigned long long)st.st_mode, (long long)st.st_size,
             (long long)st.st_mtime);
    return sys_ok_str(sys_copy_bytes(out, strlen(out)));
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

/* poll(2) on one descriptor: a positive timeout is a deadline, zero
   polls once, negative blocks. EINTR retries against the same deadline:
   a signal must not hand the wait a fresh budget, nor end it early --
   Boehm's stop-the-world signals interrupt every blocked thread
   whenever another one collects, which used to cut TUI ticks short. */
static int poll_one(struct pollfd* pfd, int64_t timeout_ms) {
    int64_t deadline = deadline_after_ms(timeout_ms);
    int rc;
    do {
        int t;
        if (timeout_ms > 0) t = remaining_ms(deadline, timeout_ms);
        else if (timeout_ms < 0) t = -1;
        else t = 0;
        rc = poll(pfd, 1, t);
    } while (rc < 0 && errno == EINTR);
    return rc;
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
        fd = cloexec_socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
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
    int fd = cloexec_socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
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
        fd = cloexec_socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
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
        fd = cloexec_accept((int)listener);
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
   ignored (`main`), so a vanished reader is EPIPE -> `broken_pipe`.

   BOTH fds are flushed. stderr always was (a log line must not be lost),
   and stdout needs it for the same reason once it is a PIPE rather than a
   terminal: `Proc.spawn` gives every child piped stdio, so a spawned script
   or MCP server writing `println` would otherwise sit in stdio's
   block buffer until it EXITS -- which for a long-running child is never.
   A terminal's line buffering hid that for as long as everything was run
   directly; `monad script --watch` is the first caller that reads a
   child's stdout while the child keeps running. */
void* monad_stream_write(int64_t fd, void* buf) {
    BufObj* obj = (BufObj*)buf;
    int64_t n = obj ? obj->len : 0;
    if (n == 0) return tcp_ok((void*)(int64_t)0);
    if (fd == 1 || fd == 2) {
        FILE* f = fd == 1 ? stdout : stderr;
        errno = 0;
        int failed = fwrite(obj->payload, 1, (size_t)n, f) != (size_t)n;
        failed = fflush(f) == EOF || failed;
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
    int rc = poll_one(&pfd, timeout_ms);
    if (rc < 0) return stream_os_err("stream_poll", errno);
    return tcp_ok((void*)(int64_t)(rc > 0 ? 1 : 0));
}

/* `stream_seek : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) I64)` -- `lseek(2)`; the ok payload is the new offset. A
   line read's carried bytes belong to the old position, so they go. */
void* monad_stream_seek(int64_t fd, int64_t offset, int64_t whence) {
    if (whence < 0 || whence > 2) return stream_os_err("stream_seek", EINVAL);
    int how = whence == 0 ? SEEK_SET : (whence == 1 ? SEEK_CUR : SEEK_END);
    off_t at = lseek((int)fd, (off_t)offset, how);
    if (at < 0) return stream_os_err("stream_seek", errno);
    stream_carry_clear((int)fd);
    return tcp_ok((void*)(int64_t)at);
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

/* ─── inotify (`std/watch.mo`) ────────────────────────────────────────
   A watch IS an `FdStream` over the kernel's inotify queue: the four
   natives below are the whole OS surface, and `Watch.decode`
   (`std/src/watch.mo`) parses the 16-byte `inotify_event` headers in
   Monad. That split is deliberate -- the parser is unit-tested over
   synthetic bytes, and this file never looks inside an event.

   `inotify_read` is poll+read in one call rather than `stream_poll`
   followed by `stream_read`: a timeout is then an EMPTY buffer in both
   backends (the Rust host has no `stream_poll`), and the "ready but
   EAGAIN" race has one answer instead of two.

   Linux only. On another POSIX target (macOS) the four functions exist
   and fail with ENOSYS, so `Watch.new` is an ordinary `StreamError` and
   a caller with a polling fallback keeps working -- rather than the
   link failing for a target that has no inotify at all. */
#if defined(__linux__)

/* `inotify_init : I64 -> RawIO (Result (Pair I64 String) FdStream)` --
   the init flags are `Watch.init_flags` (IN_NONBLOCK|IN_CLOEXEC). */
void* monad_inotify_init(int64_t flags) {
    int fd;
    do {
        fd = inotify_init1((int)flags);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return stream_os_err("inotify_init", errno);
    stream_carry_clear(fd); /* a reused descriptor inherits nothing */
    return tcp_ok((void*)(int64_t)fd);
}

/* `inotify_add_watch : FdStream -> String -> I64 -> RawIO (Result (Pair
   I64 String) I64)` -- one DIRECTORY, the watch descriptor out. */
void* monad_inotify_add_watch(int64_t fd, char* path, int64_t mask) {
    int wd = inotify_add_watch((int)fd, path ? path : "", (uint32_t)mask);
    if (wd < 0) return stream_os_err("inotify_add_watch", errno);
    return tcp_ok((void*)(int64_t)wd);
}

/* `inotify_rm_watch : FdStream -> I64 -> RawIO (Result (Pair I64 String)
   Unit)`. */
void* monad_inotify_rm_watch(int64_t fd, int64_t watch) {
    if (inotify_rm_watch((int)fd, (int)watch) != 0)
        return stream_os_err("inotify_rm_watch", errno);
    return tcp_ok(tcp_unit());
}

/* `inotify_read : FdStream -> I64 -> I64 -> RawIO (Result (Pair I64
   String) ByteBuf)` -- wait at most `timeout_ms` for events (negative
   waits forever), then one read of at most `max_bytes`.

   A TIMEOUT IS AN EMPTY BUFFER, not an error: that is how
   `Watch.next` reports "nothing happened". The kernel returns EINVAL
   rather than split an event, and `Watch.read_bytes` (4 KiB) is larger
   than the largest event (16 + NAME_MAX + 1), so a read never truncates
   one. */
void* monad_inotify_read(int64_t fd, int64_t timeout_ms, int64_t max_bytes) {
    struct pollfd pfd;
    pfd.fd = (int)fd;
    pfd.events = POLLIN;
    pfd.revents = 0;
    int rc = poll_one(&pfd, timeout_ms);
    if (rc < 0) return stream_os_err("inotify_read", errno);
    if (rc == 0) return tcp_ok(bytebuf_new(0));
    return monad_stream_read(fd, max_bytes);
}
#else
void* monad_inotify_init(int64_t flags) {
    (void)flags;
    return stream_os_err("inotify_init", ENOSYS);
}
void* monad_inotify_add_watch(int64_t fd, char* path, int64_t mask) {
    (void)fd;
    (void)path;
    (void)mask;
    return stream_os_err("inotify_add_watch", ENOSYS);
}
void* monad_inotify_rm_watch(int64_t fd, int64_t watch) {
    (void)fd;
    (void)watch;
    return stream_os_err("inotify_rm_watch", ENOSYS);
}
void* monad_inotify_read(int64_t fd, int64_t timeout_ms, int64_t max_bytes) {
    (void)fd;
    (void)timeout_ms;
    (void)max_bytes;
    return stream_os_err("inotify_read", ENOSYS);
}
#endif

/* ─── Raw stdio (`std/io.mo`'s raw-stdio group) ──────────────────────
   The two stdio operations the byte streams above cannot express:
   `read_stdin_exact`'s fill-to-n read and a real stdout flush. Writing
   to stdout/stderr and `IO.read_line` are `std/stream.mo` streams on
   fds 0-2 (`monad_stream_read`/`monad_stream_write`). Both are `RawIO`
   natives (`raw_io_passthrough`, lang/src/codegen/natives.mo) returning
   their raw payload.

   Read the same group's comment in `std/io.mo` for the contract, and
   `rust/core/src/core_native.rs`'s `read_stdin_exact` for the Rust
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
    monad_alloc_stats_install();
    GC_INIT();
    /* A write to a pipe or socket whose reader has gone must come back as
       EPIPE (a `Result.err` the caller can see), not kill the process --
       Rust's std makes the same choice process-wide. `MSG_NOSIGNAL` only
       covers `send`; `monad_stream_write`'s `write` to a child that
       already exited has no such cover. Ignored dispositions survive
       `exec`, so
       every spawned child (`spawn_child`) gets the default back, or `yes | head` in a spawned shell
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
        pthread_attr_setstacksize(&attr, monad_stack_bytes());
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
