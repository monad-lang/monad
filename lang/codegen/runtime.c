#include <gc.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <dirent.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct {
    _Atomic(int64_t) refcount;
    uint16_t tag;
    uint16_t flags;
} Header;

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
int64_t monad_get_tag(void* ptr) {
    if (!ptr) return -1;
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
   panic/OOB read for a bad boundary or an over-long `len`. */
char* monad_string_slice(char* s, int64_t start_in, int64_t len_in) {
    size_t slen = s ? strlen(s) : 0;
    size_t start = start_in < 0 ? 0 : (size_t)start_in;
    if (start > slen) start = slen;
    size_t len = len_in < 0 ? 0 : (size_t)len_in;
    size_t max_len = slen - start;
    if (len > max_len) len = max_len;
    char* out = (char*)monad_alloc_atomic(len + 1);
    if (!out) return NULL;
    if (len) memcpy(out, s + start, len);
    out[len] = '\0';
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

/* `#[native u8_to_string]`/`#[native u64_to_string]` (init/number.mo).
   Same shape as monad_i64_to_string/monad_i32_to_string above; both
   print UNSIGNED, which is the whole difference from the signed
   variants (a U64 near the top of its range is a negative i64 in this
   backend's uniform i64 representation, and must still print as the
   large positive number the reference prints). */
char* monad_u8_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%u", (unsigned)(uint8_t)n);
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

/* `#[native "process_id"]` (std/process.mo's `process_id : I64`) -- returns
   the OS process ID, used to build unique /tmp paths for parallel test
   isolation. Pure (no IO), returns a plain i64, matching `monad_bench_now`'s
   own convention. */
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

int main(int argc, char** argv) {
    GC_INIT();
    /* Exclude argv[0] (the binary's own path) -- matches the
       interpreter's own `run <file> <args...>` semantics (args passed to
       a compiled program's `main` are just the extra CLI args, not the
       program's own path), and makes an empty `args` list actually
       reachable (e.g. examples/hello.mo's "no arguments" fallback). */
    void* args = monad_build_args(argc - 1, argv + 1);
    return (int)main_monad(args);
}
