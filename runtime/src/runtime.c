/* THREADED Boehm, and this define has to come BEFORE <gc.h>: the header
   uses it to decide whether it declares the thread API at all, and
   (gc/gc_pthread_redirects.h) to redirect pthread_create/pthread_join to
   GC_pthread_create/GC_pthread_join -- which is what registers a new
   thread with the collector and hands it the right stack base. Without
   it, a worker thread that allocates makes the collector corrupt itself
   silently: Boehm's single-threaded mode assumes only the GC_INIT thread
   ever allocates. nixpkgs' boehmgc IS built with thread support --
   GC_pthread_create and GC_register_my_thread are defined symbols in its
   libgc.so, verified with nm(1) rather than assumed.

   gc.h is also deliberately the FIRST include, as it already was: when
   GC_PTHREADS is on, gc_config_macros.h defines `_REENTRANT` itself with
   a comment saying that only works for system headers included after it.
   `-pthread` on the compile command (llvm/src/link.mo) sets it up front
   as well, which is the belt to this braces. */
#define GC_THREADS
#include <gc.h>
#include <pthread.h>
#include <errno.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/stat.h>
#include <dirent.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <unistd.h>

typedef struct {
    _Atomic(int64_t) refcount;
    uint16_t tag;
    uint16_t flags;
} Header;

/* Allocation-KIND values for `Header.tag` (offset 8) -- deliberately
   distinct from a Constructor's own tag, which is a separate int64 field
   at offset 16. 0 is a bare `monad_alloc` block, 1 Closure, 2 Constructor,
   3 String, and the two handle kinds below. `monad_get_tag` is the one
   reader that has to tell the two slots apart, because a Fiber/Scope
   handle has no Constructor to read, so the handle kinds are named here --
   above every user of them -- rather than in the fiber section where they
   are described. */
#define MONAD_FIBER_TAG 17
#define MONAD_SCOPE_TAG 18
/* The tag `lang/src/codegen/ctors.mo`'s `builtin_ctor_tags` assigns to
   `IO.mk`, so a box built here and one built by emitted code are the same
   value. 16 is `Array.mk` and 17/18 are the handle kinds above, so 19 is
   the next free slot -- the two tables have to be changed together. */
#define MONAD_IO_MK_TAG 19

typedef struct {
    Header header;
    void* entry;
    int64_t arity;
    int64_t env_size;
    void* env[];
} Closure;

typedef struct {
    Header header;
    int64_t tag;
    int64_t field_count;
    void* fields[];
} Constructor;

typedef struct {
    Header header;
    int64_t length;
    char data[];
} StringObj;

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

void* alloc_closure(void* entry, int64_t arity, int64_t env_size) {
    size_t size = sizeof(Closure) + env_size * sizeof(void*);
    Closure* c = (Closure*)monad_alloc(size);
    if (c) {
        c->header.tag = 1;
        c->entry = entry;
        c->arity = arity;
        c->env_size = env_size;
    }
    return c;
}

/* alloc_closure only ALLOCATES space for env_size captured slots -- it
   has no way to accept capture VALUES itself (its signature is just
   (entry, arity, env_size)). These two are the write/read halves of
   actually populating/reading that env array, mirroring
   monad_set_field/monad_get_field's identical role for Constructor
   (see those functions' own doc comments) -- except Closure's env[]
   sits after THREE leading fields (entry, arity, env_size), not
   Constructor's TWO (tag, field_count), so monad_set_field/
   monad_get_field's own offset arithmetic does not apply here; hence
   these dedicated functions rather than reuse.
   monad_closure_set_env is called once per captured value, right after
   alloc_closure, from the ENCLOSING function that's allocating a lifted
   lambda's closure (lang/codegen/emit.mo's compile_db_lam_ir).
   monad_closure_get_env is called from INSIDE a lifted lambda's own
   compiled body, via its own `self` parameter (see apply_closureN's own
   doc comment below for how `self` gets there), to read back a
   captured value at the point it's actually referenced. */
void monad_closure_set_env(void* clos, int64_t idx, int64_t value) {
    if (!clos) return;
    ((Closure*)clos)->env[idx] = (void*)(intptr_t)value;
}

int64_t monad_closure_get_env(void* clos, int64_t idx) {
    if (!clos) return 0;
    return (int64_t)(intptr_t)((Closure*)clos)->env[idx];
}

/* Fixed-arity indirect-call trampolines for a boxed Closure value (see
   alloc_closure above) -- used whenever a function value is stored/
   passed/extracted rather than called immediately at its own reference
   site (lang/codegen/emit.mo's Term.var value-position case boxes such
   a reference via alloc_closure instead of eager-calling it;
   compile_general_db_call's callee dispatch calls back through here
   once the callee is a computed value rather than a statically-known
   global name). Every entry function this backend ever boxes is
   compiled with a UNIFORM (self, i64, i64, ..., i64) -> i64 signature,
   `self` being the closure pointer itself, passed here as this
   trampoline's own leading argument to `entry` -- this is what lets a
   genuinely CAPTURING lifted lambda (lang/codegen/emit.mo's
   compile_db_lam_ir) read its own closure instance's captured values
   back out via monad_closure_get_env(self, idx) at the point they're
   referenced inside its body: there can be many separate closure
   instances of the same lambda template with different captured
   values (e.g. one per loop iteration or recursive call), so `self`
   is the only way the lambda's own compiled code can tell which
   instance it's running as.
   This convention is applied UNIFORMLY to every entry ever boxed here,
   including a top-level Monad def referenced as a first-class value
   (e.g. passed to List.map) -- such a def's own DIRECT-call signature
   elsewhere in the program has no leading self param and must stay
   that way, so codegen boxes a small forwarding SHIM instead of the
   def's own entry point in that case (build_closure_shim_func,
   lang/codegen/emit.mo) -- the shim itself conforms to this uniform
   convention (ignoring its own unused self param) and forwards through
   to the real def unchanged. Either way, this file's own trampolines
   need no knowledge of which case they're dispatching to -- entry is
   ALWAYS (self, a0, ..., a{N-1}) -> i64 by the time it gets here.
   Capped at 8 args -- comfortably above the arities of the function
   VALUES (not ordinary direct calls, which never go through here) this
   backend needs to box today; extend by adding more typedef+function
   pairs if that ever changes. */
typedef int64_t (*Fn2)(int64_t, int64_t);
typedef int64_t (*Fn3)(int64_t, int64_t, int64_t);
typedef int64_t (*Fn4)(int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*Fn5)(int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*Fn6)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*Fn7)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*Fn8)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*Fn9)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);

/* Raw, non-arity-checked trampolines -- the ORIGINAL apply_closureN
   behavior (blind-cast `entry` to an N-ary function and call it with
   all N args at once). Not called directly by codegen -- kept as the
   base case `apply_closure_dispatch` (below) chains through, one
   `clos`-own-arity-sized bite at a time. */
static int64_t apply_closure_raw1(void* clos, int64_t a0) {
    return ((Fn2)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0);
}
static int64_t apply_closure_raw2(void* clos, int64_t a0, int64_t a1) {
    return ((Fn3)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1);
}
static int64_t apply_closure_raw3(void* clos, int64_t a0, int64_t a1, int64_t a2) {
    return ((Fn4)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2);
}
static int64_t apply_closure_raw4(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3) {
    return ((Fn5)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3);
}
static int64_t apply_closure_raw5(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4) {
    return ((Fn6)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4);
}
static int64_t apply_closure_raw6(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5) {
    return ((Fn7)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5);
}
static int64_t apply_closure_raw7(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6) {
    return ((Fn8)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5, a6);
}
static int64_t apply_closure_raw8(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) {
    return ((Fn9)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5, a6, a7);
}

/* The REAL fix: `apply_closureN`'s own historical assumption ("every
   entry function this backend ever boxes is compiled with a UNIFORM
   (self, a0, ..., a{N-1}) -> i64 signature", the doc comment above)
   holds for a boxed TOP-LEVEL DEF's own shim (build_closure_shim_func,
   lang/codegen/emit.mo -- always genuinely flat, forwards all its args
   in one call) but NOT for a CURRIED inline `fn a b c => ...` lambda's
   own closure chain: compile_db_lam_ir compiles each NESTED Term.lam as
   its own independent closure with arity 1 (alloc_closure's own second
   argument), so a 5-param inline lambda like `std/map.mo`'s
   `BTreeMap.with_node` callback (`fn k v left right h => ...`) is FIVE
   chained arity-1 closures, never one flat arity-5 entry. `combine_
   indirect_call` (lang/codegen/emit.mo) has no way to know at compile
   time which shape a given computed callee will turn out to be at
   runtime, so it always emits a single `apply_closureN` call sized to
   the STATIC argument count -- correct when the runtime closure's own
   arity happens to match N (the common case), silently wrong otherwise:
   the old blind-cast `apply_closure5` above only ever ran the FIRST
   curry level of a 5-level chain and returned an intermediate CLOSURE
   POINTER as if it were the real i64 result. Confirmed live: exactly
   this call site, `BTreeMap_with_node`'s own `apply_closure5`, silently
   corrupted every `BTreeMap` built through this backend (heights,
   comparisons, and tree fields all became garbage closure pointers
   masquerading as real values) -- the first time this instance
   method's own codegen became reachable at all (a self-hosted-parser
   fix earlier the same session, `lambda_dispatch`/`lambda_typed_params`,
   let its `with_node` callback finally get explicit param types the
   dictionary-passing pass needed).

   `alloc_closure`'s own `arity` field (already stored, previously never
   READ by apply_closureN) is exactly the missing piece: chase through
   `clos`'s own arity, `take` args at a time (`take = min(arity, n)`),
   feeding each intermediate result back in as the NEXT `clos` for the
   remaining args, until all `n` are consumed. For `clos->arity == n`
   (the common, previously-only-correct case) this takes exactly one
   raw call, identical to the old behavior -- this is a strict
   generalization, not a behavior change for anything that already
   worked. */
static int64_t apply_closure_dispatch(void* clos, int64_t* args, int n) {
    while (1) {
        int64_t arity = ((Closure*)clos)->arity;
        // Defensive: an arity outside [1, n] (0, negative, or -- not
        // expected in practice but not worth crashing over -- larger
        // than what this call site statically has) is treated as 1
        // rather than trusted blindly, so a malformed/unexpected
        // closure degrades to the old per-arg chaining behavior instead
        // of an out-of-bounds `args` read or an infinite loop.
        int64_t take = (arity >= 1 && arity <= n) ? arity : 1;
        int64_t result;
        switch (take) {
            case 1: result = apply_closure_raw1(clos, args[0]); break;
            case 2: result = apply_closure_raw2(clos, args[0], args[1]); break;
            case 3: result = apply_closure_raw3(clos, args[0], args[1], args[2]); break;
            case 4: result = apply_closure_raw4(clos, args[0], args[1], args[2], args[3]); break;
            case 5: result = apply_closure_raw5(clos, args[0], args[1], args[2], args[3], args[4]); break;
            case 6: result = apply_closure_raw6(clos, args[0], args[1], args[2], args[3], args[4], args[5]); break;
            case 7: result = apply_closure_raw7(clos, args[0], args[1], args[2], args[3], args[4], args[5], args[6]); break;
            default: result = apply_closure_raw8(clos, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]); break;
        }
        n -= (int)take;
        if (n <= 0) return result;
        args += take;
        clos = (void*)(intptr_t)result;
    }
}

int64_t apply_closure1(void* clos, int64_t a0) {
    // n=1 has no chaining ambiguity (there is no "remaining args" to
    // possibly re-dispatch) -- goes straight to the raw trampoline,
    // same as before.
    return apply_closure_raw1(clos, a0);
}
int64_t apply_closure2(void* clos, int64_t a0, int64_t a1) {
    int64_t args[2] = {a0, a1};
    return apply_closure_dispatch(clos, args, 2);
}
int64_t apply_closure3(void* clos, int64_t a0, int64_t a1, int64_t a2) {
    int64_t args[3] = {a0, a1, a2};
    return apply_closure_dispatch(clos, args, 3);
}
int64_t apply_closure4(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3) {
    int64_t args[4] = {a0, a1, a2, a3};
    return apply_closure_dispatch(clos, args, 4);
}
int64_t apply_closure5(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4) {
    int64_t args[5] = {a0, a1, a2, a3, a4};
    return apply_closure_dispatch(clos, args, 5);
}
int64_t apply_closure6(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5) {
    int64_t args[6] = {a0, a1, a2, a3, a4, a5};
    return apply_closure_dispatch(clos, args, 6);
}
int64_t apply_closure7(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6) {
    int64_t args[7] = {a0, a1, a2, a3, a4, a5, a6};
    return apply_closure_dispatch(clos, args, 7);
}
int64_t apply_closure8(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) {
    int64_t args[8] = {a0, a1, a2, a3, a4, a5, a6, a7};
    return apply_closure_dispatch(clos, args, 8);
}

/* A NULLARY constructor carries no payload -- its entire identity is
   its tag -- so every `List.empty`, `Option.none`, `Bool.true`,
   `Unit.unit` can be ONE shared immutable object rather than a fresh
   32-byte allocation each time.

   This is not a micro-optimization. Measured on `check lang/main.mo`:
   68,312,246 of the 133,912,941 total allocations were 0-field
   constructors, 2.19 GiB of 4.30 GiB. Sharing them collapses that to
   one object per distinct tag (16 in that run), cutting total
   allocations by 51% and bytes by 47%, and taking collections from 497
   to 281.

   Sound because a 0-field constructor has nothing to write --
   `monad_set_field` is never called at field_count 0 -- and Monad
   compares constructors by TAG, never by address. Tags above the cache
   bound simply allocate as before. */
#define MONAD_NULLARY_CACHE 4096
static Constructor* g_nullary[MONAD_NULLARY_CACHE];

void* alloc_constructor(int64_t tag, int64_t field_count) {
    if (field_count == 0 && tag >= 0 && tag < MONAD_NULLARY_CACHE) {
        Constructor* cached = g_nullary[tag];
        if (cached) return cached;
    }
    size_t size = sizeof(Constructor) + field_count * sizeof(void*);
    Constructor* c = (Constructor*)monad_alloc(size);
    if (c) {
        c->header.tag = 2;
        c->tag = tag;
        c->field_count = field_count;
        if (field_count == 0 && tag >= 0 && tag < MONAD_NULLARY_CACHE) {
            g_nullary[tag] = c;
        }
    }
    return c;
}

void* alloc_string(char* data, int64_t length) {
    size_t size = sizeof(StringObj) + length + 1;
    StringObj* s = (StringObj*)monad_alloc(size);
    if (s) {
        s->header.tag = 3;
        s->length = length;
        memcpy(s->data, data, length);
        s->data[length] = '\0';
    }
    return s;
}

/* Read a Constructor's tag / a field back out of an already-allocated
   value at runtime — needed for match dispatch codegen (compile_match_ir,
   lang/codegen/emit.mo), which has no other way to inspect a value it
   didn't just construct itself. */
/* A Fiber/Scope handle is not a Constructor, so `Constructor.tag` is the
   wrong slot to read for one: at offset 16 a `Fiber` holds `action`, a
   pointer, and reporting its low half would let a `match` on a handle
   take an arbitrary arm. The allocation-KIND slot in `Header` is what
   separates the two representations, so it is consulted first -- every
   Constructor carries kind 2 there, so the comparison cannot misfire on a
   real constructor tag no matter how large a program's tag numbering
   runs, and a handle reports 17/18, which no constructor tag collides
   with. See the HANDLES ARE NOT CONSTRUCTORS note above. */
int64_t monad_get_tag(void* ptr) {
    if (!ptr) return -1;
    Header* header = (Header*)ptr;
    if (header->tag == MONAD_FIBER_TAG || header->tag == MONAD_SCOPE_TAG) {
        return header->tag;
    }
    return ((Constructor*)ptr)->tag;
}

void* monad_get_field(void* ptr, int64_t idx) {
    if (!ptr) return NULL;
    return ((Constructor*)ptr)->fields[idx];
}

/* alloc_constructor only allocates space for `field_count` fields --
   it has no way to accept field values itself (its signature is just
   (tag, field_count)). Without this, every constructor with 1+
   arguments (e.g. `some 42`, `cons head tail`) allocated a correctly
   tagged/sized object whose fields were simply left as whatever
   malloc happened to return (compile_con_ir, lang/codegen/emit.mo, has
   nothing else that writes into a freshly-allocated Constructor's
   fields array). */
void monad_set_field(void* ptr, int64_t idx, void* value) {
    if (!ptr) return;
    ((Constructor*)ptr)->fields[idx] = value;
}

/* --- `std/array.mo` ------------------------------------------------

   An `Array A` value IS a Constructor: `alloc_constructor(tag, n)`
   already gives a GC-managed, indexable vector of n boxed elements
   (`fields[]`), with the length recorded in `field_count`. That is
   exactly an array, so these natives need no new heap shape -- and
   because `fields[]` is `void*`, they need no element type either,
   which is what makes them generic in `A`.

   `Array.mk`'s tag is 16, registered in `builtin_ctor_tags`
   (lang/codegen/ctors.mo) alongside Option's 3/4 and List's 5/6. It has
   to be a builtin precisely because these C functions allocate one: a C
   function cannot consult the per-program constructor numbering a
   non-builtin type would get. */
#define MONAD_ARRAY_TAG 16

void* monad_array_new(int64_t n, void* fill) {
    int64_t len = n < 0 ? 0 : n;
    void* a = alloc_constructor(MONAD_ARRAY_TAG, len);
    for (int64_t i = 0; i < len; i++) {
        monad_set_field(a, i, fill);
    }
    return a;
}

int64_t monad_array_len(void* a) {
    if (!a) return 0;
    return ((Constructor*)a)->field_count;
}

/* Bounds-checked: an out-of-range read must not be undefined behaviour,
   so this returns `Option.none` (tag 3) rather than reading past the
   end. `Option` IS a builtin, so its tags are the fixed ones
   (`builtin_ctor_tags`, lang/codegen/ctors.mo). */
void* monad_array_get(void* a, int64_t i) {
    int64_t len = monad_array_len(a);
    if (i < 0 || i >= len) {
        return alloc_constructor(3, 0);
    }
    void* some = alloc_constructor(4, 1);
    monad_set_field(some, 0, monad_get_field(a, i));
    return some;
}

/* The persistent `set`: allocate a fresh Constructor, copy, then write.
   The input is untouched -- that is the whole contract, and the reason
   this is O(n) while `set_in_place` is O(1). An out-of-range index
   returns the array unchanged. */
void* monad_array_with(void* a, int64_t i, void* v) {
    int64_t len = monad_array_len(a);
    if (i < 0 || i >= len) return a;
    void* copy = alloc_constructor(MONAD_ARRAY_TAG, len);
    for (int64_t k = 0; k < len; k++) {
        monad_set_field(copy, k, monad_get_field(a, k));
    }
    monad_set_field(copy, i, v);
    return copy;
}

/* Genuinely O(1) here, unlike the interpreter's copy-on-write (see
   `std/array.mo`'s own doc comment for why the two differ). Returns
   `IO Unit` -- the payload is never inspected, matching
   `monad_write_file`'s own convention. */
void* monad_array_set_in_place(void* a, int64_t i, void* v) {
    int64_t len = monad_array_len(a);
    if (i >= 0 && i < len) {
        monad_set_field(a, i, v);
    }
    return alloc_constructor(0, 0);
}

/* COPIES rather than casting: a cast would leave the builder aliasing a
   value pure code believes is frozen, and a later `set_in_place` would
   mutate it. */
void* monad_array_freeze(void* b) {
    int64_t len = monad_array_len(b);
    void* frozen = alloc_constructor(MONAD_ARRAY_TAG, len);
    for (int64_t k = 0; k < len; k++) {
        monad_set_field(frozen, k, monad_get_field(b, k));
    }
    return frozen;
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
    void* unit = alloc_constructor(0, 0);
    int64_t box = apply_closure1(f->action, (int64_t)(intptr_t)unit);
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
        void* raw_io = alloc_constructor(7, 1);
        monad_set_field(raw_io, 0, NULL);
        void* io_mk = alloc_constructor(MONAD_IO_MK_TAG, 1);
        monad_set_field(io_mk, 0, raw_io);
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

/* monad_io_pure: RawIO.pure (a : A) : RawIO A -- wraps a value in the
   RawIO.io constructor (tag 7, one field). */
void* monad_io_pure(int64_t a) {
    void* c = alloc_constructor(7, 1);
    monad_set_field(c, 0, (void*)(intptr_t)a);
    return c;
}

/* monad_io_bind: RawIO.bind (a : RawIO A) (f : A -> RawIO B) : RawIO B --
   unwraps the RawIO.io constructor (field 0) and calls f on the inner
   value via apply_closure1. */
int64_t monad_io_bind(int64_t io_val, int64_t f) {
    void* inner = monad_get_field((void*)(intptr_t)io_val, 0);
    return apply_closure1((void*)(intptr_t)f, (int64_t)(intptr_t)inner);
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
    return alloc_constructor(0, 0);
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
    return alloc_constructor(0, 0);
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
    return alloc_constructor(0, 0);
}

void monad_print_str(char* s) {
    if (s) printf("%s\n", s);
}

/* `#[native string_length]` (init/string.mo's `String.length`) dispatches
   generically through `Term.ntv`/`compile_ntv_ir` (lang/codegen/emit.mo)
   to `monad_string_length` -- that generic mechanism was already fully
   wired end-to-end, just missing every actual String primitive's C
   implementation (a real, separate, much bigger gap than this one
   function closes -- `String.beq`/`concat`/`slice`/`drop`/... are still
   unimplemented). Added here specifically so `I64.to_string`'s own
   result (added just above) has a way to be verified by a real
   compile-and-run test without depending on unrelated, still-missing
   String natives. */
int64_t monad_string_length(char* s) {
    return s ? (int64_t)strlen(s) : 0;
}

/* `#[native string_count_newlines]` / `#[native string_trailing_chars]`
   (init/string.mo) -- the two scans `lang/parser/position.mo`'s bulk
   offset resolver needs in order to walk one step per SPAN rather than
   one per character. Both look at the first `len` bytes of `s` IN PLACE
   and return a count; neither allocates, and neither calls `strlen`.

   Both of those properties are load-bearing, not tidiness. The resolver
   threads a remainder forward and asks about the segment between two
   consecutive spans, so it makes one call per span; a `strlen` (or a
   `monad_string_slice`, which does a `strlen` AND a malloc AND a memcpy)
   would make each call O(whole remaining file) and the walk quadratic
   again -- exactly the shape `monad_string_drop`'s own comment above
   describes paying for. Stopping early at NUL is what replaces the
   bounds check a `strlen` would have provided, the same trick
   `monad_string_drop` uses, so the cost stays O(min(len, strlen(s))).

   `trailing_chars` counts CHARACTERS after the last '\n' (or across all
   of the range, if it contains none) -- a character being a byte that is
   not a UTF-8 continuation byte, `(b & 0xC0) != 0x80`, which is the same
   0x80-0xBF range `is_utf8_continuation_byte` (lang/parser/position.mo)
   tests for. Counting bytes here instead would put a column after a
   multi-byte character in the wrong place, and
   `test_resolve_offsets_column_counts_characters` is the test that says
   so. `core/src/core_native.rs`'s two implementations must agree with
   these byte for byte: a disagreement shows up as the host and a
   self-compiled binary reporting different columns, which reads like a
   codegen bug and is not one. */
int64_t monad_string_count_newlines(char* s, int64_t len) {
    if (!s || len <= 0) return 0;
    int64_t n = 0;
    for (int64_t i = 0; i < len; i++) {
        if (s[i] == '\0') break;
        if (s[i] == '\n') n++;
    }
    return n;
}

int64_t monad_string_trailing_chars(char* s, int64_t len) {
    if (!s || len <= 0) return 0;
    int64_t n = 0;
    for (int64_t i = 0; i < len; i++) {
        unsigned char c = (unsigned char)s[i];
        if (c == '\0') break;
        if (c == '\n') n = 0;
        else if ((c & 0xC0) != 0x80) n++;
    }
    return n;
}

/* `I64.to_string` (init/number.mo) had no backing implementation at
   all -- neither a Monad-level `:=` body nor a runtime primitive.
   Returns a plain malloc'd NUL-terminated buffer, matching this
   runtime's uniform raw-`char*` String convention (see
   monad_build_args's own doc comment: strings are never
   alloc_string's boxed StringObj in practice, every native that
   consumes/produces a String uses a bare char*). */
char* monad_i64_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
    char* out = (char*)monad_alloc_atomic((size_t)len + 1);
    if (out) memcpy(out, buf, (size_t)len + 1);
    return out;
}

/* `#[native string_concat]` (init/string.mo's `String.concat`, also the
   `++`/`Append.append` infix's own real backing for two Strings) --
   previously entirely unwired in codegen: `compile_native_app_db`/
   `compile_native_ir` have no NativeOp entry for it, so every call fell
   through to the generic "native def with no known implementation"
   fallback, which compiles to a meaningless `alloc_constructor(0, 0)` --
   confirmed as a real gap via direct repro (a do-block printing a
   `String.concat` result printed nothing meaningful). Same bare-`char*`
   convention as `monad_i64_to_string` just above (this backend's Strings
   are never `alloc_string`'s boxed `StringObj` in practice). NULL-safe:
   a NULL operand is treated as empty, matching `monad_print_str`'s own
   NULL tolerance elsewhere in this file, since a still-missing/upstream
   String native could plausibly hand this a NULL rather than a real
   empty string. */
char* monad_string_concat(char* a, char* b) {
    size_t la = a ? strlen(a) : 0;
    size_t lb = b ? strlen(b) : 0;
    char* out = (char*)monad_alloc_atomic(la + lb + 1);
    if (!out) return NULL;
    if (la) memcpy(out, a, la);
    if (lb) memcpy(out + la, b, lb);
    out[la + lb] = '\0';
    return out;
}

/* `#[native string_eq]` (init/string.mo's `String.beq`) -- same
   previously-unwired gap as `monad_string_concat` above. Returns a
   plain `int64_t` 0/1 (this backend's uniform boolean-as-i64
   convention, matching `I64_eq`'s own `icmp`-then-widen codegen), not a
   real tagged `Bool` constructor -- correct for this native's use as an
   `icmp`-style comparison operand (see NativeOp.op_eq's own codegen),
   not as a first-class `Bool` value passed around opaquely. */
int64_t monad_string_eq(char* a, char* b) {
    if (a == b) return 1;
    if (!a || !b) return 0;
    return strcmp(a, b) == 0 ? 1 : 0;
}

/* `#[native string_lt]`/`#[native string_gt]` (init/string.mo's
   `String.lt`/`String.gt`, used by `instance BOrd String`) -- same
   previously-unwired gap as `monad_string_eq` above: with no entry in
   `native_runtime_fn_name` (lang/codegen/emit.mo), a `#[native]` def
   with no real body silently compiled to the generic "return Unit"
   stub, discarding both arguments and returning the SAME value every
   time. Confirmed live via a real compiled binary: `std/map.mo`'s
   `instance [BOrd K] Map BTreeMap`'s own `BOrd.lt`/`BOrd.gt` calls,
   backed by these natives, always took the SAME branch regardless of
   input -- silently corrupting every `BTreeMap String _` built through
   the self-hosted LLVM codegen path (a later `BTreeMap_to_list_asc`
   crashed dereferencing a field that was never a valid tree pointer to
   begin with). Byte-lexicographic `strcmp` ordering, matching the Rust
   host's own `str < str`/`str > str` (`core/src/core_native.rs`'s
   `string_lt`/`string_gt`, whose own doc comment notes UTF-8's byte
   ordering agrees with codepoint ordering) -- same `strcmp` choice
   `monad_string_eq` above already made, same "NULL treated as empty"
   tolerance as `monad_string_concat`. Returns a plain `int64_t` 0/1, not
   a real tagged `Bool` -- `NativeWrapKind.bool_result` (lang/codegen/
   emit.mo) does the raw-int-to-tagged-`Bool` conversion at the call
   site, matching `monad_string_eq`'s own convention. */
int64_t monad_string_lt(char* a, char* b) {
    const char* sa = a ? a : "";
    const char* sb = b ? b : "";
    return strcmp(sa, sb) < 0 ? 1 : 0;
}

int64_t monad_string_gt(char* a, char* b) {
    const char* sa = a ? a : "";
    const char* sb = b ? b : "";
    return strcmp(sa, sb) > 0 ? 1 : 0;
}

/* `#[native string_slice]` (init/string.mo's `String.slice`) -- another
   previously-unwired gap: `#[native]` with no real body silently
   compiled to the generic "return Unit" stub, discarding every argument
   -- confirmed live via a self-compiled binary calling itself: `lang/
   codegen/emit.mo`'s own `remove_quotes_loop` recursing on `String.slice
   s 1 (String.length s - 1)` never actually shrank `s` (the stub always
   returned the same bogus zero-tag value regardless of input), looping
   until the native stack overflowed instead of terminating once `s`
   became empty.

   Byte-oriented (not UTF-8-char-aware) and clamps rather than errors on
   any out-of-range input, bit-for-bit matching the Rust host's own
   reference semantics (`core/src/core_native.rs`'s `string_slice`,
   `SharedStr::subslice`) so compiled and interpreted execution agree:
   `start` clamps into `[0, strlen(s)]`, `len` clamps to `>= 0` and to
   whatever remains after `start`, and a NULL `s` yields `""` -- never a
   panic/OOB read for a bad boundary or an over-long `len`.

   BOTH CLAMPS ARE WALKS BOUNDED BY THE ARGUMENTS, NOT A `strlen`. The
   previous body opened with `strlen(s)`, which made every slice cost
   O(remaining string) no matter how small the slice was -- and that is
   not a micro-optimization here, it is the difference between linear and
   quadratic for every per-character scanner in the compiler. The
   documented cost model is O(slice): `lang/parser/combinators.mo`'s
   `take_while` comment justifies its shape with "once `slice` is O(1),
   the correct shape is ... one O(1) slice", and `take_while_loop`
   deliberately does one `String.slice input 0 width` PER CHARACTER.
   That holds in the interpreted backend, where `SharedStr::subslice`
   shares the backing allocation (see `shared_str.rs`), and did not hold
   here: `String.drop` is zero-copy, so it hands back a pointer into the
   middle of a large buffer and every subsequent one-character slice
   walked the whole rest of that buffer. Measured on the LSP's own input:
   parsing a 320 KB JSON string payload cost 19 s compiled against 0.03 s
   for the same work interpreted, because the payload is sliced once per
   character. This is the same pathology, and the same remedy, as
   `monad_string_drop`'s own comment describes ("a full `strlen` would
   reintroduce the same O(n^2) in CPU"): walk at most `start` bytes to
   find `start`'s clamp point, and use `memchr` -- the bounded form of
   the `strlen` this replaces -- to find `len`'s. Stopping at NUL is what
   replaces the bounds check `strlen` provided, and the walk cannot read
   past the NUL because it stops there. Cost is O(start + len); the
   bytes produced are unchanged. */
char* monad_string_slice(char* s, int64_t start_in, int64_t len_in) {
    if (!s) s = "";
    size_t start = 0;
    if (start_in > 0) {
        size_t want = (size_t)start_in;
        while (start < want && s[start] != '\0') start++;
    }
    size_t len = len_in < 0 ? 0 : (size_t)len_in;
    if (len == 0) {
        char* out = (char*)monad_alloc_atomic(1);
        if (!out) return NULL;
        out[0] = '\0';
        return out;
    }
    const void* nul = memchr(s + start, '\0', len);
    size_t avail = nul ? (size_t)((const char*)nul - (s + start)) : len;
    char* out = (char*)monad_alloc_atomic(avail + 1);
    if (!out) return NULL;
    if (avail) memcpy(out, s + start, avail);
    out[avail] = '\0';
    return out;
}

/* `#[native string_drop]` (init/string.mo's `String.drop`) -- same
   reference semantics as `core/src/core_native.rs`'s `string_drop`/
   `SharedStr::drop_prefix`: drops the first `n` bytes (clamped to
   `[0, strlen(s)]`), never errors on an out-of-range `n`.
   ZERO-COPY: returns a pointer INTO `s` rather than a fresh buffer.
   This is sound because strings in this runtime are immutable
   NUL-terminated `char*` and nothing ever mutates or frees one
   (`monad_release` is never emitted; runtime.c only frees its own
   scratch buffers) -- the alias keeps the whole original buffer
   alive, and the dropped prefix becomes unreachable, which is no
   worse than this runtime's uniform no-free discipline elsewhere.
   The old malloc+memcpy of the whole REMAINDER made every parser
   scan step cost O(remaining) bytes both in copies and leaked RSS:
   measured, a single `take_while` pass over a 225KB file (one
   drop per input char) leaked ~2.4GB in one glibc arena and made
   `check lang/main.mo` OOM at 30GB. Scanning forward at most `n`
   bytes to find the clamp point keeps the common small-`n` scan step
   O(1) (a full `strlen` would reintroduce the same O(n^2) in CPU);
   for `n > strlen(s)` the first NUL terminates the walk early and
   `s + that_index` is the empty string, identical to the old clamped
   result. NULL input propagates NULL (every string native here is
   NULL-tolerant, treating it as empty). */
char* monad_string_drop(int64_t n, char* s) {
    if (!s) return NULL;
    if (n <= 0) return s;
    for (size_t i = 0; i < (size_t)n; i++) {
        if (s[i] == '\0') return s + i;
    }
    return s + n;
}

char* monad_read_file(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (size < 0) { fclose(f); return NULL; }
    char* buf = (char*)monad_alloc_atomic(size + 1);
    if (!buf) { fclose(f); return NULL; }
    size_t got = fread(buf, 1, size, f);
    fclose(f);
    if (got != (size_t)size) { return NULL; }
    buf[size] = '\0';
    return buf;
}

void monad_write_file(char* path, char* data, int64_t len) {
    if (!path || !data || len < 0) return;
    FILE* f = fopen(path, "wb");
    if (!f) return;
    fwrite(data, 1, (size_t)len, f);
    fclose(f);
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

/* djb2 hash: hash = hash * 33 + byte, seed 5381 -- bit-identical to
   `core/src/core_native.rs`'s own `string_hash` (wrapping u64 mul/add)
   and to `init/string.mo`'s own `String.hash_selfhosted` reference
   implementation. Pure (no `IO` in String.hash's declared type), so
   this returns a plain i64 rather than the truthy-pointer convention
   above -- see `needs_io_wrap`'s own doc comment in lang/codegen/emit.mo. */
int64_t monad_string_hash(char* s) {
    uint64_t hash = 5381u;
    if (!s) return (int64_t)hash;
    for (unsigned char* p = (unsigned char*)s; *p; p++) {
        hash = hash * 33u + (uint64_t)(*p);
    }
    return (int64_t)hash;
}

/* Build a List String (linked list) from command line args.
   List.empty is constructor tag 5, List.cons is constructor tag 6 (2
   fields: head, tail) -- must match emit.mo's constructor_tag, which is
   the single source of truth for the fixed prelude-constructor tag table
   this codegen uses (tags used to be 0/1 here, out of sync with
   constructor_tag's 5/6 -- any match on `args` compared against the
   wrong tags no matter what the match codegen itself did).
   Each head is `argv[i]` directly -- a raw, already-NUL-terminated
   `char*`, valid for the process's whole lifetime -- NOT alloc_string's
   boxed StringObj. Every native that consumes a "String" value
   (monad_print_str, ...) expects the SAME representation string
   LITERALS compile to: a bare `char*` (compile_lit_ir's Literal.str
   case emits a plain LLVM global constant, no StringObj wrapping at
   all). Boxing argv here via alloc_string produced a value with a
   totally different, incompatible layout (StringObj's `{ header;
   length; data[] }`, data offset well past the pointer's start) --
   `monad_print_str` reading straight from that pointer as if it were a
   C string just printed nothing/garbage from the header bytes instead
   of the actual argument, the moment ANY CLI arg (as opposed to a
   literal string, e.g. hello.mo's own "no arguments" fallback) reached
   it. This codegen has no unified boxed-vs-raw string representation
   generally (a real, separate gap) -- matching the raw-pointer
   convention everywhere `String` values are actually consumed today is
   the correct fix, not introducing a second, competing representation
   here.
   Builds the list in reverse (cons prepends), so argv[0] is first. */
/* ─── Natives that are genuinely C-shaped ────────────────────────────
   These need libc facilities (fork/exec, opendir, qsort) or buffer
   building that the `lang/codegen/runtime.mo` generated-IR emitters
   have no clean way to express yet. Everything simpler than these --
   the String byte loops, the U8/U64 arithmetic -- is now GENERATED
   Monad-side (see that module's own doc comment); this file keeps only
   what actually earns its C.

   All of them follow this file's uniform conventions: Strings are raw
   NUL-terminated char*, and List/Option results are built with
   alloc_constructor + direct field stores using the fixed builtin tag
   table (List.empty 5, List.cons 6) that emit.mo's builtin_ctor_tags
   is the single source of truth for. */

/* `#[native string_concat_list]` (init/string.mo's `String.concat_list`).

   Concatenating a list of strings pairwise is quadratic: every
   `String.concat` copies BOTH sides, so folding one over N pieces
   recopies the accumulated prefix N times. The backend's own emitters
   (`emit_functions`/`emit_blocks`/`emit_globals`/`emit_decls`,
   lang/codegen/ir.mo) build a 3.8 MB module that way, which is the
   difference between seconds and hours at this size.

   Deliberately separate from `String.concat_all`, which stays ordinary
   Monad code: `concat_all` is reachable from macro expansion, and that
   runs in the self-hosted meta-evaluator's small fixed native table
   (lang/core_eval.mo) whose constructor tags are the program's own, not
   this file's fixed List.empty 5 / List.cons 6. Widening that sandbox
   for the code generator's performance would be the wrong trade.

   Two passes, one allocation: measure, then copy. `parts` is a
   `List String` in the usual convention (List.empty 5, List.cons 6,
   fields head/tail), and each head is a raw NUL-terminated char* like
   every other String here -- NOT a boxed StringObj.

   C rather than generated Monad IR for the same reason the rest of this
   section is: it needs a real buffer built in one shot, which the
   generated-IR emitters have no way to express. */
char* monad_string_concat_list(void* parts) {
    size_t total = 0;
    for (void* n = parts; n && monad_get_tag(n) == 6; n = monad_get_field(n, 1)) {
        char* piece = (char*)monad_get_field(n, 0);
        if (piece) total += strlen(piece);
    }

    char* out = (char*)monad_alloc_atomic(total + 1);
    if (!out) return NULL;
    size_t at = 0;
    for (void* n = parts; n && monad_get_tag(n) == 6; n = monad_get_field(n, 1)) {
        char* piece = (char*)monad_get_field(n, 0);
        if (piece) {
            size_t len = strlen(piece);
            memcpy(out + at, piece, len);
            at += len;
        }
    }
    out[at] = '\0';
    return out;
}

/* `#[native string_to_lowercase]` (init/string.mo). ASCII-only, matching
   what every caller in the compiler's own closure needs (identifier and
   keyword folding); the reference's Rust `to_lowercase` is full Unicode,
   a difference that cannot show up for the ASCII inputs this backend
   sees. Returns a fresh malloc'd buffer -- never mutates its argument,
   which may well be a read-only string literal in .rodata. */
char* monad_string_to_lowercase(char* s) {
    if (!s) return NULL;
    size_t n = strlen(s);
    char* out = (char*)monad_alloc_atomic(n + 1);
    if (!out) return NULL;
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        out[i] = (c >= 'A' && c <= 'Z') ? (char)(c - 'A' + 'a') : (char)c;
    }
    out[n] = '\0';
    return out;
}

/* `#[native string_from_list]` (init/string.mo): walk a `List U8` cons
   chain, collecting each head byte into a fresh NUL-terminated buffer.
   The inverse of the GENERATED monad_string_to_list -- kept in C
   because the buffer-building loop needs a growable allocation, which
   the generated-IR emitters have no malloc/realloc story for yet.
   Two passes (count, then fill) so the allocation is exact. */
char* monad_string_from_list(void* list) {
    int64_t n = 0;
    for (void* cur = list; cur && monad_get_tag(cur) == 6; ) {
        n++;
        cur = monad_get_field(cur, 1);
    }
    char* out = (char*)monad_alloc_atomic((size_t)n + 1);
    if (!out) return NULL;
    int64_t i = 0;
    for (void* cur = list; cur && monad_get_tag(cur) == 6; ) {
        out[i++] = (char)((int64_t)monad_get_field(cur, 0) & 0xFF);
        cur = monad_get_field(cur, 1);
    }
    out[n] = '\0';
    return out;
}

/* `#[native i32_to_string]` (init/number.mo). Same shape as
   monad_i64_to_string above -- this backend holds every integer width
   in an i64, so the only real difference is truncating to 32 bits
   first, matching the reference's own I32 formatting. */
char* monad_i32_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%d", (int)(int32_t)n);
    char* out = (char*)monad_alloc_atomic((size_t)len + 1);
    if (out) memcpy(out, buf, (size_t)len + 1);
    return out;
}

/* `#[native u8_to_string]`/`#[native u16_to_string]`/`#[native
   u64_to_string]` (init/number.mo). Same shape as
   monad_i64_to_string/monad_i32_to_string above; all three print
   UNSIGNED, which is the whole difference from the signed variants (a
   U64 near the top of its range is a negative i64 in this backend's
   uniform i64 representation, and must still print as the large
   positive number the reference prints). */
char* monad_u8_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%u", (unsigned)(uint8_t)n);
    char* out = (char*)monad_alloc_atomic((size_t)len + 1);
    if (out) memcpy(out, buf, (size_t)len + 1);
    return out;
}

char* monad_u16_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%u", (unsigned)(uint16_t)n);
    char* out = (char*)monad_alloc_atomic((size_t)len + 1);
    if (out) memcpy(out, buf, (size_t)len + 1);
    return out;
}

char* monad_u64_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)n);
    char* out = (char*)monad_alloc_atomic((size_t)len + 1);
    if (out) memcpy(out, buf, (size_t)len + 1);
    return out;
}

/* ─── F64 ────────────────────────────────────────────────────────────
   `init/number.mo`'s `F64` family: `#[native f64_add]`/`f64_sub`/
   `f64_mul`/`f64_div`/`f64_eq`/`f64_lt`/`f64_gt`, plus `f64_to_string`
   and `f64_of_string` below.

   An F64 value here is its IEEE-754 double BIT PATTERN held in the same
   uniform unboxed i64 payload every other number uses: this backend's
   value flow has no float in it at all, which is why every operation
   below is memcpy-in / compute / memcpy-out rather than a real float
   type. `Literal.flt`'s own doc comment (`lang/types.mo`) describes the
   same choice from the source end, and `lang/codegen/emit.mo`'s
   `compile_lit_ir` lowers a float literal to one of these bit patterns
   as a plain i64 constant.

   The SEMANTICS mirror `core/src/core_native.rs`'s
   `float_binop`/`float_cmp`/`float_to_string` exactly, because that is
   what the Rust runner and every `#[test]` in the optics files were
   written against:

   - the four arithmetic ops are plain C double arithmetic -- Rust's f64
     IS the same hardware double, so these agree bit for bit,
     including the rounding of a result that lands between two doubles;
   - `eq`/`lt`/`gt` are C's `==`/`<`/`>`, which match Rust's operators in
     the NaN cases too (all three are false for a NaN operand under
     both languages, which is what makes `x == x` false rather than
     true);
   - `to_string` is the shortest decimal that round-trips, in plain
     positional notation -- see its own comment below.

   Declared `int64_t`-in/`char*`-out exactly like the to_string family
   above: the C signature says what the function really is, while the
   emitted IR's `declare`/call convention is the uniform i64. */
static double monad_f64_unbits(int64_t bits) {
    double d;
    memcpy(&d, &bits, sizeof d);
    return d;
}
static int64_t monad_f64_bits(double d) {
    int64_t bits;
    memcpy(&bits, &d, sizeof bits);
    return bits;
}
int64_t monad_f64_add(int64_t a, int64_t b) { return monad_f64_bits(monad_f64_unbits(a) + monad_f64_unbits(b)); }
int64_t monad_f64_sub(int64_t a, int64_t b) { return monad_f64_bits(monad_f64_unbits(a) - monad_f64_unbits(b)); }
int64_t monad_f64_mul(int64_t a, int64_t b) { return monad_f64_bits(monad_f64_unbits(a) * monad_f64_unbits(b)); }
int64_t monad_f64_div(int64_t a, int64_t b) { return monad_f64_bits(monad_f64_unbits(a) / monad_f64_unbits(b)); }
int64_t monad_f64_eq(int64_t a, int64_t b) { return monad_f64_unbits(a) == monad_f64_unbits(b) ? 1 : 0; }
int64_t monad_f64_lt(int64_t a, int64_t b) { return monad_f64_unbits(a) < monad_f64_unbits(b) ? 1 : 0; }
int64_t monad_f64_gt(int64_t a, int64_t b) { return monad_f64_unbits(a) > monad_f64_unbits(b) ? 1 : 0; }

/* The decimal -> double conversion. `Literal.flt` carries the literal's
   SOURCE TEXT, not a value (`lang/types.mo`: self-hosted Monad has no
   native bridge to parse a decimal into a float bit pattern), so the
   compiler needs exactly this to lower a float literal -- and it reaches
   it the ordinary way, as a `#[native f64_of_string]` call from
   `lang/codegen/emit.mo`'s `compile_lit_ir`, rather than by growing an
   IEEE-754 decimal parser inside the compiler. `strtod` is the same
   parse the Rust host does with `f64::from_str` for the forms a Monad
   float literal can take (digits with an optional fraction and exponent;
   the lexer produces nothing else). A NULL or unparsable string gives
   0.0 rather than a crash -- a wrong value is a test failure, not a
   segfault in the compiler. */
int64_t monad_f64_of_string(char* s) {
    return monad_f64_bits(s ? strtod(s, NULL) : 0.0);
}

/* Rust's `f64::to_string` -- what `F64.to_string` means on the host --
   prints the SHORTEST decimal that round-trips, in plain positional
   notation, and never in exponent form: "100" for 100.0, "0.1" for 0.1,
   "100000000000000000000" for 1e20, "0.0000001" for 1e-7. `%g` cannot
   do that on its own: at its default precision it prints 3.14's
   neighbours badly, and it switches to exponent form whenever the
   exponent is outside [1, precision) -- "1e+20" where Rust spells the
   number out in full.

   So this finds the digit count the same way the Rust formatter's own
   shortest-round-trip search does -- the first `%.*e` precision that
   `strtod`s back to the identical bits -- and then renders those digits
   positionally around the decimal point `%e` reports. 17 significant
   digits always suffice for a double, so the search is bounded and
   short. Rust's spellings for the non-finite values ("NaN", "inf",
   "-inf") come out of the no-digits exit below. */
char* monad_f64_to_string(int64_t v) {
    double d = monad_f64_unbits(v);
    char mant[64];
    int prec = 0;
    for (; prec <= 16; prec++) {
        snprintf(mant, sizeof(mant), "%.*e", prec, d);
        if (strtod(mant, NULL) == d) break;
    }
    if (prec > 16) snprintf(mant, sizeof(mant), "%.16e", d);

    char digits[24];
    int ndig = 0;
    int exp10 = 0;
    int neg = 0;
    const char* p = mant;
    if (*p == '-') { neg = 1; p++; }
    for (; *p && *p != 'e' && *p != 'E'; p++) {
        if (*p >= '0' && *p <= '9') { if (ndig < 23) digits[ndig++] = *p; }
    }
    if (*p == 'e' || *p == 'E') exp10 = (int)strtol(p + 1, NULL, 10);

    char out[400];
    int n = 0;
    /* The sign goes first, for every finite value and for an infinity --
       `-0` and `-inf` are both real Rust spellings. A NaN is the one
       value that prints without one (`d == d` is false exactly there),
       which is why this is a guard rather than a plain `if (neg)`. */
    if (neg && d == d) out[n++] = '-';
    if (ndig == 0) {
        /* No digits at all from `%e`: a NaN or an infinity, the only
           values that produce none. Same spelling as the Rust host's
           Display, which is what the two runners have to agree on. */
        const char* word = (d != d) ? "NaN" : "inf";
        while (*word && n < 399) out[n++] = *word++;
    } else if (exp10 >= 0) {
        int before = exp10 + 1;
        for (int i = 0; i < ndig && n < 399; i++) {
            if (i == before) out[n++] = '.';
            out[n++] = digits[i];
        }
        for (int i = ndig; i < before && n < 399; i++) out[n++] = '0';
    } else {
        out[n++] = '0';
        out[n++] = '.';
        for (int i = 0; i < -exp10 - 1 && n < 399; i++) out[n++] = '0';
        for (int i = 0; i < ndig && n < 399; i++) out[n++] = digits[i];
    }
    out[n] = '\0';

    char* res = (char*)monad_alloc_atomic((size_t)n + 1);
    if (res) memcpy(res, out, (size_t)n + 1);
    return res;
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
    int64_t argc = 0;
    for (void* cur = args; cur && monad_get_tag(cur) == 6; ) {
        argc++;
        cur = monad_get_field(cur, 1);
    }
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) return -1;
    argv[0] = cmd;
    int64_t i = 1;
    for (void* cur = args; cur && monad_get_tag(cur) == 6; ) {
        argv[i++] = (char*)monad_get_field(cur, 0);
        cur = monad_get_field(cur, 1);
    }
    argv[i] = NULL;

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
        execvp(cmd, argv);
        _exit(127);            /* exec failed -- conventional shell code */
    }
    int status = 0;
    free(argv);
    if (waitpid(pid, &status, 0) < 0) return -1;
    return WIFEXITED(status) ? (int64_t)WEXITSTATUS(status) : -1;
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

/* `#[native "build_commit"]` (lang/main.mo's `build_commit : String`) --
   returns the git commit hash this binary was compiled from, baked in
   at build time via -DMONAD_BUILD_COMMIT. "unknown" if git was
   unavailable or the build wasn't from a repo. Pure (no `IO`), zero
   args, returns a `String` (char* = i64 in this backend's convention,
   same as `monad_process_id`). */
const char* monad_build_commit(void) {
#ifdef MONAD_BUILD_COMMIT
    return MONAD_BUILD_COMMIT;
#else
    return "unknown";
#endif
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
    if (!d) return (void*)alloc_constructor(5, 0);   /* List.empty */

    size_t cap = 16, n = 0;
    char** names = (char**)GC_malloc(sizeof(char*) * cap);
    if (!names) { closedir(d); return (void*)alloc_constructor(5, 0); }

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
    void* list = (void*)alloc_constructor(5, 0);
    for (size_t i = n; i > 0; i--) {
        Constructor* cons = (Constructor*)alloc_constructor(6, 2);
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
    if (!val) return (void*)alloc_constructor(3, 0);   /* Option.none */
    size_t len = strlen(val);
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (!copy) return (void*)alloc_constructor(3, 0);  /* OOM -> none */
    memcpy(copy, val, len + 1);
    Constructor* some = (Constructor*)alloc_constructor(4, 1);
    some->fields[0] = copy;
    return some;
}

/* ─── TCP ────────────────────────────────────────────────────────────
   `std/io.mo`'s eight `#[native "tcp_*"]` defs, reached by
   `motes/moon`'s server and `motes/moose`'s client.

   This is TCP's ONLY implementation. The reference deliberately has
   none -- a second implementation was not worth its maintenance cost --
   so the behaviours recorded here ARE the contract, and
   `slow_tests/src/codegen_wired_natives_e2e_tests.mo` is what holds
   them to it. `std/io.mo`'s own declarations restate the same contract
   for a reader who starts from the source side.

   A Socket/Listener value is the raw FILE DESCRIPTOR as an i64, not a
   constructor. `type Socket { socket }` exists so the checker has a
   nominal type; its single zero-arity constructor is never built,
   because `alloc_constructor` CACHES nullary constructors by tag (see
   MONAD_NULLARY_CACHE above) -- one shared pointer for every socket in
   the program, which could not carry an fd in any case. Nothing in the
   corpus pattern-matches, compares or prints one, so an fd in the
   payload position is all this flow ever needs; it is the same shape
   the generated `List U8` code already uses to hold a byte. It also
   means no handle table is needed here, and no `constructor_tag`
   lookup -- the `io_passthrough` wrapper in `lang/codegen/natives.mo`
   only IO-wraps whatever word comes back.

   Divergences from the deleted Rust implementation, recorded rather
   than papered over:

     - A double `close` here closes a RECYCLED descriptor, where the
       Rust version's handle drop was a harmless no-op for an unknown
       id. Latent only (every test closes each descriptor at most
       once), and the trade is deliberate: a C-side handle table would
       buy nothing the fd does not already give, and would have to be
       kept in step with the collector.
     - `tcp_local_port : IO U16` has no `Result` channel, so a failing
       `getsockname` returns 0 where the Rust version raised.
     - No poll loop anywhere: every motes test writes before it reads
       on a single thread, so a blocking read cannot deadlock. That is
       a property of the corpus rather than of these functions -- a
       test that reads before it writes WILL block on both sides.
     - `MSG_NOSIGNAL` on every send, because this file installs no
       SIGPIPE handler where Rust's std ignores SIGPIPE process-wide: a
       write to a peer that already closed would otherwise kill the
       process instead of returning `Result.err`.
*/

/* Build `Result.ok <word>`. `Result.ok` is tag 10, `Result.err` tag 11
   and `Unit.unit` tag 0 -- `lang/src/codegen/ctors.mo`'s fixed prelude
   tags, the same table the generated `rt_tag_*` helpers mirror. The
   field holds a raw word, so one `tcp_ok` serves an fd, a byte count
   and a `List U8` pointer alike. */
static void* tcp_ok(void* payload) {
    Constructor* ok = (Constructor*)alloc_constructor(10, 1);
    if (ok) ok->fields[0] = payload;
    return ok;
}

/* `Result.err` (tag 11) carrying `<a>: <b>`, or `<a>: <b> (os error
   <n>)` when `errnum` is positive. The message is COPIED into a
   GC-visible buffer: `strerror`'s storage is libc's and a format
   string is the caller's, and every other `String` here is an owned
   char* (same reasoning as `monad_get_env` above). */
static void* tcp_err_pair(const char* a, const char* b, int errnum) {
    char buf[512];
    if (errnum != 0) {
        snprintf(buf, sizeof(buf), "%s: %s (os error %d)", a, b, errnum);
    } else {
        snprintf(buf, sizeof(buf), "%s: %s", a, b);
    }
    size_t len = strlen(buf);
    char* copy = (char*)monad_alloc_atomic(len + 1);
    if (copy) memcpy(copy, buf, len + 1);
    Constructor* err = (Constructor*)alloc_constructor(11, 1);
    if (err) err->fields[0] = copy;
    return err;
}

/* `<op>: <strerror> (os error <errno>)` -- the shape the deleted Rust
   implementation got from `std::io::Error`'s own Display. Nothing in
   the corpus asserts on the text; keeping the shape keeps a familiar
   debugging aid. */
static void* tcp_os_err(const char* op, int errnum) {
    return tcp_err_pair(op, strerror(errnum), errnum);
}

/* `Unit.unit` (tag 0). The nullary cache makes this the same instance
   every call. */
static void* tcp_unit(void) {
    return alloc_constructor(0, 0);
}

/* Count a `List U8` cons chain -- `monad_string_from_list`'s own walk,
   split out because `tcp_write` needs the length before it needs the
   bytes (it is the ok payload). */
static int64_t tcp_list_len(void* list) {
    int64_t n = 0;
    for (void* cur = list; cur && monad_get_tag(cur) == 6; ) {
        n++;
        cur = monad_get_field(cur, 1);
    }
    return n;
}

/* `IO.tcp_connect (host : String) (port : U16) : IO (Result String Socket)`
   -- blocking connect. `getaddrinfo` resolves the host the way the
   Rust version's `TcpStream::connect((host, port))` did, so
   `"127.0.0.1"`, `"localhost"` and a real name all work, and each
   address it returns is tried in turn (a v6 address that fails to
   connect must not stop a working v4 one from being tried). */
void* monad_tcp_connect(char* host, int64_t port) {
    struct addrinfo hints;
    struct addrinfo* res = NULL;
    char portbuf[16];
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    snprintf(portbuf, sizeof(portbuf), "%u", (unsigned)(uint16_t)port);
    int rc = getaddrinfo(host ? host : "", portbuf, &hints, &res);
    if (rc != 0) return tcp_err_pair("tcp_connect", gai_strerror(rc), 0);
    int fd = -1;
    int last_errno = 0;
    for (struct addrinfo* ai = res; ai != NULL; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) { last_errno = errno; continue; }
        if (connect(fd, ai->ai_addr, ai->ai_addrlen) == 0) break;
        last_errno = errno;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) return tcp_os_err("tcp_connect", last_errno);
    return tcp_ok((void*)(int64_t)fd);
}

/* `IO.tcp_listen (port : U16) : IO (Result String Listener)` -- binds
   `0.0.0.0:port`, with port 0 asking the OS for one (read it back with
   `tcp_local_port`). Deliberately NO `SO_REUSEADDR`: the Rust version
   set none, every test binds port 0, and setting it would let a second
   bind steal a port a lingering connection still owns. Backlog 128 is
   Rust's own default for `TcpListener::bind`. */
void* monad_tcp_listen(int64_t port) {
    int fd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (fd < 0) return tcp_os_err("tcp_listen", errno);
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons((uint16_t)port);
    if (bind(fd, (struct sockaddr*)&addr, sizeof(addr)) != 0) {
        int e = errno;
        close(fd);
        return tcp_os_err("tcp_listen", e);
    }
    if (listen(fd, 128) != 0) {
        int e = errno;
        close(fd);
        return tcp_os_err("tcp_listen", e);
    }
    return tcp_ok((void*)(int64_t)fd);
}

/* `IO.tcp_accept (listener : Listener) : IO (Result String Socket)` --
   blocking accept, returning a new Socket for the accepted connection.
   `EINTR` retries rather than surfacing: no signal handler in this file
   wants the caller to see a spurious failure. */
void* monad_tcp_accept(int64_t listener) {
    int fd;
    do {
        fd = accept((int)listener, NULL, NULL);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return tcp_os_err("tcp_accept", errno);
    return tcp_ok((void*)(int64_t)fd);
}

/* `IO.tcp_read (sock : Socket) (max_bytes : U64) : IO (Result String (List U8))`
   -- blocking read of AT MOST `max_bytes`. EOF (the peer closed) is
   `Result.ok List.empty`, NOT an error; only a real read error
   (connection reset, and so on) is `Result.err`. Both motes' read loops
   terminate on exactly this convention. */
void* monad_tcp_read(int64_t sock, int64_t max_bytes) {
    if (max_bytes <= 0) return tcp_ok(alloc_constructor(5, 0));  /* List.empty */
    char* buf = (char*)malloc((size_t)max_bytes);
    if (!buf) return tcp_err_pair("tcp_read", "out of memory", 0);
    ssize_t n;
    do {
        n = recv((int)sock, buf, (size_t)max_bytes, 0);
    } while (n < 0 && errno == EINTR);
    if (n < 0) {
        int e = errno;
        free(buf);
        return tcp_os_err("tcp_read", e);
    }
    /* Built back-to-front so the list reads in the order the bytes
       arrived; each head is the byte as a raw word, the representation
       `monad_string_from_list` reads back. */
    void* list = alloc_constructor(5, 0);
    for (ssize_t i = n - 1; i >= 0; i--) {
        Constructor* cons = (Constructor*)alloc_constructor(6, 2);
        if (!cons) break;
        cons->fields[0] = (void*)(int64_t)(unsigned char)buf[i];
        cons->fields[1] = list;
        list = cons;
    }
    free(buf);
    return tcp_ok(list);
}

/* `IO.tcp_write (sock : Socket) (data : List U8) : IO (Result String U64)`
   -- blocking write of ALL of `data`, with the ok payload the FULL
   length rather than the last partial count (`write_all(&data).map(|()
   | data.len())` in the Rust version). `send` in a loop, because a
   stream socket is free to accept less than asked. */
void* monad_tcp_write(int64_t sock, void* data) {
    int64_t n = tcp_list_len(data);
    if (n == 0) return tcp_ok((void*)(int64_t)0);
    char* buf = (char*)malloc((size_t)n);
    if (!buf) return tcp_err_pair("tcp_write", "out of memory", 0);
    int64_t i = 0;
    for (void* cur = data; cur && monad_get_tag(cur) == 6 && i < n; ) {
        buf[i++] = (char)((int64_t)monad_get_field(cur, 0) & 0xFF);
        cur = monad_get_field(cur, 1);
    }
    int64_t done = 0;
    while (done < n) {
        ssize_t w = send((int)sock, buf + done, (size_t)(n - done), MSG_NOSIGNAL);
        if (w < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            free(buf);
            return tcp_os_err("tcp_write", e);
        }
        done += w;
    }
    free(buf);
    return tcp_ok((void*)(int64_t)n);
}

/* `IO.tcp_close (sock : Socket) : IO Unit` -- closes the socket. Never
   fails: the type has no error channel, and every caller closes each
   descriptor once. */
void* monad_tcp_close(int64_t sock) {
    if (sock >= 0) close((int)sock);
    return tcp_unit();
}

/* `IO.tcp_close_listener (listener : Listener) : IO Unit` -- same, for
   a listening socket (closing it does not touch connections already
   accepted from it). */
void* monad_tcp_close_listener(int64_t listener) {
    if (listener >= 0) close((int)listener);
    return tcp_unit();
}

/* `IO.tcp_local_port (listener : Listener) : IO U16` -- the port the
   listener actually bound, which is the only way to learn the
   OS-assigned port after `tcp_listen 0u16`. Returns 0 if
   `getsockname` fails; see the divergence note above. */
int64_t monad_tcp_local_port(int64_t listener) {
    struct sockaddr_in addr;
    socklen_t len = sizeof(addr);
    if (getsockname((int)listener, (struct sockaddr*)&addr, &len) != 0) return 0;
    return (int64_t)ntohs(addr.sin_port);
}

/* ─── Pointer FFI (`init/prelude.mo`'s `Ptr`) ──────────────────────── */

/* `Ptr.null : Ptr` -- the NULL pointer, for C functions whose callback
   argument is NULL (`SSL_set_verify` in motes/tls is the first caller). A
   `Ptr` value is its raw machine word, so the NULL word is the whole
   implementation. */
int64_t monad_ptr_null(void) {
    return 0;
}

/* ─── ByteBuf (`std/bytebuf.mo`) ─────────────────────────────────────
   A flat byte buffer the C FFI can address: `SSL_read`/`SSL_write`
   (motes/tls) take a `void*` plus a length, and no other `std/` type
   exposes one.

   A `ByteBuf` value is the raw pointer to a GC-ALLOCATED buffer (the
   `Socket`-as-fd shape: the value is never a constructor). GC
   allocation is why `monad_bytebuf_free` is a deliberate no-op: a
   forgotten buffer is reclaimed, and a real `GC_free` on a word another
   live value still holds would be a use-after-free. The buffer records
   no length; `to_list`'s `len` is the count the CALLER knows
   (`SSL_read`'s return), and `alloc` zero-fills so a round-trip test
   never depends on malloc's spare bytes. The list walks are
   `monad_tcp_write`/`monad_tcp_read`'s, reusing the same cons-chain
   conventions (tags 5/6). */

/* `IO.ByteBuf.alloc (n : I64) : IO ByteBuf` -- n zeroed bytes. A
   negative n clamps to 0 rather than allocating a huge size. */
void* monad_bytebuf_alloc(int64_t n) {
    size_t len = n > 0 ? (size_t)n : 0;
    unsigned char* buf = (unsigned char*)monad_alloc_atomic(len);
    if (buf && len) memset(buf, 0, len);
    return buf;
}

/* `IO.ByteBuf.of_list (xs : List U8) : IO ByteBuf` -- the same copy walk
   `monad_tcp_write` uses, into a GC buffer. */
void* monad_bytebuf_of_list(void* list) {
    int64_t n = tcp_list_len(list);
    unsigned char* buf = (unsigned char*)monad_alloc_atomic(n > 0 ? (size_t)n : 0);
    if (!buf) return buf;
    int64_t i = 0;
    for (void* cur = list; cur && monad_get_tag(cur) == 6 && i < n; ) {
        buf[i++] = (unsigned char)((int64_t)monad_get_field(cur, 0) & 0xFF);
        cur = monad_get_field(cur, 1);
    }
    return buf;
}

/* `IO.ByteBuf.to_list (b : ByteBuf) (len : I64) : IO (List U8)` -- the
   first `len` bytes, built back-to-front exactly `monad_tcp_read` builds
   its list so it reads in memory order. A non-positive `len` yields
   `List.empty`; a `len` past what was allocated reads out of bounds
   (the module doc makes the caller the length's owner). */
void* monad_bytebuf_to_list(void* buf, int64_t len) {
    if (len <= 0) return alloc_constructor(5, 0);  /* List.empty */
    unsigned char* bytes = (unsigned char*)buf;
    void* list = alloc_constructor(5, 0);
    for (int64_t i = len - 1; i >= 0; i--) {
        Constructor* cons = (Constructor*)alloc_constructor(6, 2);
        if (!cons) break;
        cons->fields[0] = (void*)(int64_t)bytes[i];
        cons->fields[1] = list;
        list = cons;
    }
    return list;
}

/* `IO.ByteBuf.free (b : ByteBuf) : IO Unit` -- no-op (see the section
   comment); returns the Unit ctor like every `IO Unit` native. */
void* monad_bytebuf_free(void* buf) {
    (void)buf;
    return tcp_unit();
}

/* `ByteBuf.ptr (b : ByteBuf) : Ptr` -- identity: the representation IS
   the raw pointer the FFI wants. */
int64_t monad_bytebuf_ptr(int64_t b) {
    return b;
}

/* ─── Raw stdio (`std/io.mo`'s raw-stdio group) ──────────────────────
   The byte-level half of stdio, added for the language server (`lsp`):
   it writes LSP frames to stdout with no extra newline, logs to stderr
   without corrupting its own protocol stream on fd 1, and reads a stdin
   byte stream whose frames the OS is free to split across reads.
   `monad_print_str` (above) and `monad_read_file` can express none of
   that -- the first always appends '\n' and cannot be aimed anywhere
   but fd 1 (or 2, at all), the second takes a path.

   Read the same group's comment in `std/io.mo` for the contract, and
   `core/src/core_native.rs`'s `read_stdin_exact` family for the Rust
   evaluator's half. That half needs a UTF-8-carry subtlety this one
   does not: bytes are stored raw here, which is exactly what a byte
   stream wants, so no chunk boundary can surprise this side.

   A returned `String` is a bare NUL-terminated `char*`, the same
   representation every other String native here returns and the one
   `compile_lit_ir`'s string literals have (see `monad_print_str`'s own
   notes on the boxed `StringObj`). The `IO Unit` natives return the
   Unit constructor pointer via `tcp_unit` just above --
   `io_passthrough` (`lang/src/codegen/natives.mo`) IO-wraps a native's
   raw result, so an `IO Unit` native returns the Unit ctor rather than
   nothing at all.

   Every read here goes through `read(0, ...)` rather than stdio
   (`getchar`/`fgets`), and that is load-bearing rather than a
   preference: stdio reads a whole block ahead into its own buffer, so
   a `getchar`-based `monad_read_line` would silently swallow the bytes
   the caller's next `monad_read_stdin_exact` is looking for -- the
   protocol stream would desynchronize with no error anywhere. Nothing
   else in this runtime touches fd 0, so one reader is all there is. */

/* One line from stdin, WITHOUT its trailing newline. `Option.none`
   (tag 3) when nothing at all was read, `Option.some line` (tag 4)
   otherwise -- the same fixed tags `monad_get_env` above builds, and
   the same ones `monad_array_get` / runtime.mo's `rt_tag_some` use.
   A final line with no trailing newline is still `some`, and `\r` is
   deliberately NOT stripped (the caller wants the bytes the peer
   actually sent).

   Byte-at-a-time deliberately: anything that reads a block ahead would
   consume bytes belonging to the caller's NEXT read. A line is short,
   so the syscall per byte costs nothing worth optimizing against a
   desynchronized protocol stream. */
char* monad_read_line(void) {
    size_t cap = 64;
    size_t len = 0;
    /* Did the stream yield anything at all? A bare "\n" reads no
       characters but is still a line (`some ""`), whereas reading
       nothing at all is EOF (`none`) -- so the two cases cannot be told
       apart from `len` alone. */
    int saw_byte = 0;
    char* buf = (char*)monad_alloc_atomic(cap);
    if (!buf) return (char*)alloc_constructor(3, 0);
    for (;;) {
        char c;
        ssize_t got = read(0, &c, 1);
        if (got < 0) {
            if (errno == EINTR) continue;
            break;                    /* a read error is EOF to the caller */
        }
        if (got == 0) break;          /* EOF */
        saw_byte = 1;
        if (c == '\n') break;         /* the terminator is not part of the line */
        if (len + 1 >= cap) {
            size_t grown_cap = cap * 2;
            char* grown = (char*)GC_realloc(buf, grown_cap);
            if (!grown) break;        /* OOM: hand back what we have */
            buf = grown;
            cap = grown_cap;
        }
        buf[len++] = c;
    }
    if (!saw_byte) return (char*)alloc_constructor(3, 0);   /* Option.none */
    buf[len] = '\0';
    Constructor* some = (Constructor*)alloc_constructor(4, 1);
    if (some) some->fields[0] = buf;
    return (char*)some;
}

/* `IO.read_stdin_exact (n : I64) : IO String` -- blocking read of UP TO
   `n` bytes from stdin, returning exactly the bytes read. The result
   being SHORTER than `n` (including "") means EOF to the caller, which
   is what makes that a reliable end-of-stream test rather than "the OS
   returned a short read this time": the loop below only stops early
   when a `read` actually reports 0, so a partial return is always EOF.
   `n <= 0` returns "".

   The result is NUL-terminated but its LENGTH is the caller's count of
   bytes, not `strlen` -- a frame body may legitimately contain NULs.
   Note that a String with an embedded NUL is a representation this
   runtime's other String consumers (`monad_print_str`, `strlen`-based
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

/* `IO.write_stdout (s : String) : IO Unit` -- `s` to stdout VERBATIM:
   no trailing newline (the whole difference from `monad_print_str`) and
   no flush (a frame's pieces go out first, then `monad_flush_stdout`
   once). Null-tolerant like its neighbours. */
void* monad_write_stdout(char* s) {
    if (s) fputs(s, stdout);
    return tcp_unit();
}

/* `IO.flush_stdout : IO Unit` -- needed because stdout is block-buffered
   when it is a pipe (which is how a language server's peer reads it), so
   a written frame stays invisible until this runs. */
void* monad_flush_stdout(void) {
    fflush(stdout);
    return tcp_unit();
}

/* `IO.write_stderr (s : String) : IO Unit` -- `s` to stderr verbatim,
   no trailing newline, and FLUSHED at once: a log line that sits in a
   buffer until process exit is no log line at all for a server that
   never exits. A native of its own rather than an fd argument to the
   one above so that a log line can never interleave into the protocol
   stream the peer is parsing. */
void* monad_write_stderr(char* s) {
    if (s) {
        fputs(s, stderr);
        fflush(stderr);
    }
    return tcp_unit();
}

void* monad_build_args(int argc, char** argv) {
    void* list = alloc_constructor(5, 0);   /* List.empty */
    for (int i = argc - 1; i >= 0; i--) {
        Constructor* cons = (Constructor*)alloc_constructor(6, 2);
        cons->fields[0] = argv[i];  /* head -- raw char*, matches string literals' own representation */
        cons->fields[1] = list;     /* tail */
        list = cons;
    }
    return list;
}

int64_t main_monad(void* args);

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
    m->result = main_monad(m->args);
    return NULL;
}

int main(int argc, char** argv) {
    raise_stack_limit();
    GC_INIT();
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
        return (int)main_monad(args);
    }
    pthread_join(thread, NULL);
    return (int)m.result;
}
