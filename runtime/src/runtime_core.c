/* Portable runtime: heap objects, closures, constructors, strings, ByteBuf.
   Compiled for every target. Pointer values cross the IR boundary as i64
   words on wasm; see runtime_abi.h. */

typedef struct {
    rt_refcount refcount;
    uint16_t tag;
    uint16_t flags;
#ifdef MONAD_OWNERSHIP
    /* The allocation's own size, recorded only in ownership builds so
       `monad_owned_free`'s poison mode can fill exactly the block. The GC
       path never reads it, and default builds do not carry the field at
       all -- every translation unit is compiled with the same defines
       (`llvm/src/link.mo`), so the layout cannot disagree. */
    rt_size size;
#endif
} Header;

/* ── Region allocation (ownership-regions-memory O3) ────────────────────
   The Region half of the ownership split: values that may be shared,
   cyclic or `Copy`, and must never be freed individually. In this phase
   these forward to the platform allocator, exactly as every allocation
   did before -- the split is a naming boundary that a later region
   implementation (O5) can move without touching a call site. */
rt_word monad_region_alloc(rt_size size) { return monad_alloc(size); }
rt_word monad_region_alloc_atomic(rt_size size) { return monad_alloc_atomic(size); }

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
/* A `ByteBuf`'s block (see the ByteBuf section below) -- the fourth
   allocation kind, and the shape `plans/bootstrapping/mlir-codegen.md`'s
   `Buf E` generalises into a typed `Buf`. 20 is the next free slot after
   16/17/18/19 above; unlike `IO.mk` and `Array.mk` it needs NO entry in
   `lang/src/codegen/ctors.mo`'s `builtin_ctor_tags`, because nothing ever
   CONSTRUCTS one -- every `ByteBuf` comes from a native, and its
   `bytebuf` constructor is never built at run time. `monad_get_tag`
   therefore has to name this kind for the same reason it names 17/18: a
   `BufObj` has no Constructor slot to read. */
#define MONAD_BUF_TAG 20
/* A `Ref` slot (`std/src/ref.mo`): a GC-scanned cell holding one Monad word,
   with a pthread mutex on native targets. 21 is the next free slot after
   `MONAD_BUF_TAG`. A `Ref` has no Constructor slot, so `monad_get_tag` names
   its kind too; matching on a `Ref` is documented as unsupported, and the
   interpreter rejects it with "value is not a constructor". */
#define MONAD_REF_TAG 21
/* A channel (`std/src/concurrent/channel.mo`): an MVar whose value word is
   GC-traced, with pthread mutex/condvar on native targets. 22 is the next
   free slot after `MONAD_REF_TAG`. Like every handle, it has no Constructor
   slot, so `monad_get_tag` names it; matching on a channel is unsupported. */
#define MONAD_CHANNEL_TAG 22
/* A `Cell` (`init/src/view.mo`): an opaque linear handle over one Copy
   payload word. 23 is the next free slot after `MONAD_CHANNEL_TAG`. Like
   every handle it has no Constructor slot, so `monad_get_tag` names it. */
#define MONAD_CELL_TAG 23
/* A `Slot` (`init/src/view.mo`): an opaque linear handle that is either empty
   or holds one value of any type. 24 is the next free slot after
   `MONAD_CELL_TAG`. Like every handle it has no Constructor slot, so
   `monad_get_tag` names it. */
#define MONAD_SLOT_TAG 24
/* `Pair.pair`'s builtin tag (`lang/src/codegen/ctors.mo`'s
   `builtin_ctor_tags`). `monad_view_get` builds the pair in C because a
   Cell handle and its payload must travel as one value; a fixed tag is
   available for exactly the constructors `builtin_ctor_tags` names. */
#define MONAD_PAIR_TAG 15
/* `Array.mk`'s builtin tag (16), registered in `builtin_ctor_tags`
   alongside Option's 3/4 and List's 5/6. It has to be a builtin precisely
   because the C array helpers allocate one: a C function cannot consult the
   per-program constructor numbering a non-builtin type would get. Defined
   here, before `alloc_constructor_impl`, so the allocation stats can tell an
   Array cell from an ordinary constructor. */
#define MONAD_ARRAY_TAG 16

typedef struct {
    Header header;
    void* entry;
    int64_t arity;
    int64_t env_size;
    rt_field env[];
} Closure;

typedef struct {
    Header header;
    int64_t tag;
    int64_t field_count;
    rt_field fields[];
} Constructor;

typedef struct {
    Header header;
    int64_t length;
    char data[];
} StringObj;

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
static rt_word alloc_closure_impl(rt_word entry, int64_t arity, int64_t env_size) {
    size_t size = sizeof(Closure) + (size_t)env_size * sizeof(rt_field);
    MONAD_STAT(MONAD_STAT_CLOSURE, size);
    Closure* c = (Closure*)RT_PTR(monad_region_alloc((rt_size)size));
    if (c) {
        c->header.tag = 1;
        c->entry = RT_PTR(entry);
        c->arity = arity;
        c->env_size = env_size;
    }
    return RT_WORD(c);
}

static void monad_closure_set_env_impl(rt_word clos, int64_t idx, rt_field value) {
    if (!clos) return;
    ((Closure*)RT_PTR(clos))->env[idx] = value;
}

static rt_field monad_closure_get_env_impl(rt_word clos, int64_t idx) {
    if (!clos) return RT_FIELD(0);
    return ((Closure*)RT_PTR(clos))->env[idx];
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
   back out via monad_closure_get_env_impl(self, idx) at the point they're
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

static int64_t apply_closure1_impl(void* clos, int64_t a0) {
    // n=1 has no chaining ambiguity (there is no "remaining args" to
    // possibly re-dispatch) -- goes straight to the raw trampoline,
    // same as before.
    return apply_closure_raw1(clos, a0);
}
static int64_t apply_closure2_impl(void* clos, int64_t a0, int64_t a1) {
    int64_t args[2] = {a0, a1};
    return apply_closure_dispatch(clos, args, 2);
}
static int64_t apply_closure3_impl(void* clos, int64_t a0, int64_t a1, int64_t a2) {
    int64_t args[3] = {a0, a1, a2};
    return apply_closure_dispatch(clos, args, 3);
}
static int64_t apply_closure4_impl(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3) {
    int64_t args[4] = {a0, a1, a2, a3};
    return apply_closure_dispatch(clos, args, 4);
}
static int64_t apply_closure5_impl(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4) {
    int64_t args[5] = {a0, a1, a2, a3, a4};
    return apply_closure_dispatch(clos, args, 5);
}
static int64_t apply_closure6_impl(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5) {
    int64_t args[6] = {a0, a1, a2, a3, a4, a5};
    return apply_closure_dispatch(clos, args, 6);
}
static int64_t apply_closure7_impl(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6) {
    int64_t args[7] = {a0, a1, a2, a3, a4, a5, a6};
    return apply_closure_dispatch(clos, args, 7);
}
static int64_t apply_closure8_impl(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) {
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
   bound simply allocate as before.

   Fibers are OS threads, so a slot is published with a release store and
   read with an acquire load: a reader that sees the pointer also sees the
   tag and field count written before it. Two threads filling the same
   slot at once is harmless; both objects are valid and the later store
   wins. The `__atomic` builtins rather than <stdatomic.h> because the web
   profile is freestanding; on single-threaded wasm they are plain loads
   and stores. */
#define MONAD_NULLARY_CACHE 4096
static Constructor* g_nullary[MONAD_NULLARY_CACHE];

static rt_word alloc_constructor_impl(int64_t tag, int64_t field_count) {
    if (field_count == 0 && tag >= 0 && tag < MONAD_NULLARY_CACHE) {
        Constructor* cached = __atomic_load_n(&g_nullary[tag], __ATOMIC_ACQUIRE);
        if (cached) return RT_WORD(cached);
    }
    size_t size = sizeof(Constructor) + (size_t)field_count * sizeof(rt_field);
    MONAD_STAT(tag == MONAD_ARRAY_TAG ? MONAD_STAT_ARRAY : MONAD_STAT_CTOR, size);
    Constructor* c = (Constructor*)RT_PTR(monad_region_alloc((rt_size)size));
    if (c) {
        c->header.tag = 2;
        c->tag = tag;
        c->field_count = field_count;
        if (field_count == 0 && tag >= 0 && tag < MONAD_NULLARY_CACHE) {
            __atomic_store_n(&g_nullary[tag], c, __ATOMIC_RELEASE);
        }
    }
    return RT_WORD(c);
}

/* The Owned allocation path (ownership-regions-memory O3/O4).
 *
 * Only callers whose value the ownership verdict classified Owned use this:
 * a monomorphic inductive with no nullary constructor whose fields are all
 * `Copy` or themselves Owned. Such a value is freed by generated drop glue,
 * so it must come from `monad_owned_alloc` -- mixing a GC block in would
 * hand `monad_owned_free` a pointer `free()` cannot take.
 *
 * Deliberately never consults `g_nullary`: those singletons are shared and
 * static, and a type with a nullary constructor is Region by the verdict.
 * The nullary arm below is a second defence only. `monad_owned_alloc`
 * zeroes the block (Boehm does; `malloc` does not), so an unset field reads
 * the same as on the GC path. */
static rt_word alloc_constructor_owned_impl(int64_t tag, int64_t field_count) {
    if (field_count == 0) return alloc_constructor_impl(tag, field_count);
    size_t size = sizeof(Constructor) + (size_t)field_count * sizeof(rt_field);
    MONAD_STAT(MONAD_STAT_OWNED_CTOR, size);
    Constructor* c = (Constructor*)RT_PTR(monad_owned_alloc((rt_size)size));
    if (c) {
        c->header.tag = 2;
        c->tag = tag;
        c->field_count = field_count;
    }
    return RT_WORD(c);
}

static rt_word alloc_string_impl(rt_str data, int64_t length) {
    size_t size = sizeof(StringObj) + length + 1;
    StringObj* s = (StringObj*)RT_PTR(monad_region_alloc((rt_size)size));
    if (s) {
        s->header.tag = 3;
        s->length = length;
        memcpy(s->data, RT_STR(data), (size_t)length);
        s->data[length] = '\0';
    }
    return RT_WORD(s);
}

/* Read a Constructor's tag / a field back out of an already-allocated
   value at runtime — needed for match dispatch codegen (compile_match_ir,
   lang/codegen/emit.mo), which has no other way to inspect a value it
   didn't just construct itself. */
/* A Fiber/Scope handle or a `BufObj` is not a Constructor, so
   `Constructor.tag` is the wrong slot to read for one: at offset 16 a
   `Fiber` holds `action`, a pointer, a `ByteBuf` holds `elem_kind`, and
   reporting either low half would let a `match` on one take an arbitrary
   arm. The allocation-KIND slot in `Header` is what separates the two
   representations, so it is consulted first -- every Constructor carries
   kind 2 there, so the comparison cannot misfire on a real constructor
   tag no matter how large a program's tag numbering runs, and a handle
   reports 17/18 and a buffer 20, which no constructor tag collides with.
   See the HANDLES ARE NOT CONSTRUCTORS note above. */
static int64_t monad_get_tag_impl(rt_word ptr) {
    if (!ptr) return -1;
    Header* header = (Header*)RT_PTR(ptr);
    if (header->tag == MONAD_FIBER_TAG || header->tag == MONAD_SCOPE_TAG
        || header->tag == MONAD_BUF_TAG || header->tag == MONAD_REF_TAG
        || header->tag == MONAD_CHANNEL_TAG || header->tag == MONAD_CELL_TAG
        || header->tag == MONAD_SLOT_TAG) {
        return header->tag;
    }
    return ((Constructor*)RT_PTR(ptr))->tag;
}

static rt_field monad_get_field_impl(rt_word ptr, int64_t idx) {
    if (!ptr) return RT_FIELD(0);
    return ((Constructor*)RT_PTR(ptr))->fields[idx];
}

/* alloc_constructor only allocates space for `field_count` fields --
   it has no way to accept field values itself (its signature is just
   (tag, field_count)). Without this, every constructor with 1+
   arguments (e.g. `some 42`, `cons head tail`) allocated a correctly
   tagged/sized object whose fields were simply left as whatever
   malloc happened to return (compile_con_ir, lang/codegen/emit.mo, has
   nothing else that writes into a freshly-allocated Constructor's
   fields array). */
static void monad_set_field_impl(rt_word ptr, int64_t idx, rt_field value) {
    if (!ptr) return;
    ((Constructor*)RT_PTR(ptr))->fields[idx] = value;
}

/* --- `std/array.mo` ------------------------------------------------

   An `Array A` value IS a Constructor: `alloc_constructor_impl(tag, n)`
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

static rt_word monad_array_new_impl(int64_t n, rt_word fill) {
    int64_t len = n < 0 ? 0 : n;
    rt_word a = alloc_constructor_impl(MONAD_ARRAY_TAG, len);
    for (int64_t i = 0; i < len; i++) {
        monad_set_field_impl(a, i, RT_FIELD(fill));
    }
    return a;
}

static int64_t monad_array_len_impl(rt_word a) {
    if (!a) return 0;
    return ((Constructor*)RT_PTR(a))->field_count;
}

/* Bounds-checked: an out-of-range read must not be undefined behaviour,
   so this returns `Option.none` (tag 3) rather than reading past the
   end. `Option` IS a builtin, so its tags are the fixed ones
   (`builtin_ctor_tags`, lang/codegen/ctors.mo). */
static rt_word monad_array_get_impl(rt_word a, int64_t i) {
    int64_t len = monad_array_len_impl(a);
    if (i < 0 || i >= len) {
        return alloc_constructor_impl(3, 0);
    }
    rt_word some = alloc_constructor_impl(4, 1);
    monad_set_field_impl(some, 0, monad_get_field_impl(a, i));
    return some;
}

/* The allocation-free read: out-of-range answers the caller's fallback, and
   an in-range read returns the element itself. No `Option` box is built,
   which is what `Array.get_or` uses on the hot path. */
static rt_word monad_array_get_or_impl(rt_word a, int64_t i, rt_word fallback) {
    int64_t len = monad_array_len_impl(a);
    if (i < 0 || i >= len) return fallback;
    return monad_get_field_impl(a, i);
}

/* The persistent `set`: allocate a fresh Constructor, copy, then write.
   The input is untouched -- that is the whole contract, and the reason
   this is O(n) while `set_in_place` is O(1). An out-of-range index
   returns the array unchanged. */
static rt_word monad_array_with_impl(rt_word a, int64_t i, rt_word v) {
    int64_t len = monad_array_len_impl(a);
    if (i < 0 || i >= len) return a;
    rt_word copy = alloc_constructor_impl(MONAD_ARRAY_TAG, len);
    for (int64_t k = 0; k < len; k++) {
        monad_set_field_impl(copy, k, monad_get_field_impl(a, k));
    }
    monad_set_field_impl(copy, i, RT_FIELD(v));
    return copy;
}

/* Genuinely O(1) here, unlike the interpreter's copy-on-write (see
   `std/array.mo`'s own doc comment for why the two differ). Returns
   `IO Unit` -- the payload is never inspected. */
static rt_word monad_array_set_in_place_impl(rt_word a, int64_t i, rt_word v) {
    int64_t len = monad_array_len_impl(a);
    if (i >= 0 && i < len) {
        monad_set_field_impl(a, i, RT_FIELD(v));
    }
    return alloc_constructor_impl(0, 0);
}

/* COPIES rather than casting: a cast would leave the builder aliasing a
   value pure code believes is frozen, and a later `set_in_place` would
   mutate it. */
static rt_word monad_array_freeze_impl(rt_word b) {
    int64_t len = monad_array_len_impl(b);
    rt_word frozen = alloc_constructor_impl(MONAD_ARRAY_TAG, len);
    for (int64_t k = 0; k < len; k++) {
        monad_set_field_impl(frozen, k, monad_get_field_impl(b, k));
    }
    return frozen;
}


/* monad_io_pure: RawIO.pure (a : A) : RawIO A -- wraps a value in the
   RawIO.io constructor (tag 7, one field). */
static rt_word monad_io_pure_impl(int64_t a) {
    rt_word c = alloc_constructor_impl(7, 1);
    monad_set_field_impl(c, 0, RT_FIELD(a));
    return c;
}

/* Cooperative cancellation: the fiber trampoline points this at the
   running fiber's `cancelled` word (platform_posix.c's fiber_main) and
   clears it on the way out. NULL on main and on the wasm profiles, where
   there are no fibers to cancel. Reads are atomic because the cancel
   lands on another thread; see MONAD_CANCELLED_SENTINEL in
   runtime_abi.h for the protocol. */
static _Thread_local int64_t* monad_cancel_flag;

void monad_set_cancel_flag(int64_t* flag) {
    monad_cancel_flag = flag;
}

static int monad_io_cancelled(void) {
    int64_t* flag = monad_cancel_flag;
    return flag != NULL && __atomic_load_n(flag, __ATOMIC_ACQUIRE) != 0;
}

/* For blocking natives (channels) that must give a cancelled fiber back
   instead of parking it forever. Not part of the IR surface. */
int monad_fiber_cancelled(void) {
    return monad_io_cancelled();
}

/* monad_io_bind: RawIO.bind (a : RawIO A) (f : A -> RawIO B) : RawIO B --
   unwraps the RawIO.io constructor (field 0) and calls f on the inner
   value via apply_closure1.

   This is the cancellation point: a set flag, or a sentinel already
   propagated from an inner bind, short-circuits the continuation. The
   check comes BEFORE the field read, so the sentinel is never treated as
   a RawIO. */
static int64_t monad_io_bind_impl(int64_t io_val, int64_t f) {
    if (io_val == MONAD_CANCELLED_SENTINEL || monad_io_cancelled())
        return MONAD_CANCELLED_SENTINEL;
    rt_field inner = monad_get_field_impl(RT_FIELD(io_val), 0);
    return apply_closure1_impl(RT_PTR(f), RT_VALUE(inner));
}

/* monad_io_bind_guard: the cancellation half of `monad_io_bind`, for the
   codegen's direct-style (fused) IO bind. A fused bind compiles to a
   branch -- cancel before reading any field, else continue inline -- so
   it needs the same check as `monad_io_bind_impl` without the call into
   the continuation. Returns MONAD_CANCELLED_SENTINEL when the bind must
   short-circuit (the value is already the sentinel, or this fiber is
   cancelled) and 0 otherwise; 0 is not a valid IO value, so the caller
   branches on `!= 0`. See `plans/bootstrapping/heapless-loops.md` H1. */
static int64_t monad_io_bind_guard_impl(int64_t io_val) {
    if (io_val == MONAD_CANCELLED_SENTINEL || monad_io_cancelled())
        return MONAD_CANCELLED_SENTINEL;
    return 0;
}

/* ── Ref (std/src/ref.mo) ──────────────────────────────────────────────
   A shared mutable slot, lock-free: native fibers are OS threads, so every
   access to the value word is atomic (the `__atomic` builtins, as for
   `g_nullary`, so wasi/web compile them to plain accesses).
   `monad_cell_update` reads the word, applies the closure with nothing
   held, and compare-and-swaps the result in, retrying from the new word if
   another fiber got there first. Holding a lock across the closure used to
   deadlock when the closure touched the same Ref (compiled IO natives run
   when evaluated), and stalled every other fiber on a slow one. `f` is
   pure, so running it more than once is invisible; comparing words is
   enough because a word names an immutable value. The value word is
   stored in a GC-scanned block (`monad_alloc`), so the collector traces
   it. Slots are never freed: a Ref has no drop operation. */

typedef struct {
    Header header;
    rt_word value;
} RefObj;

static RefObj* ref_of(rt_word handle) {
    RefObj* r = (RefObj*)RT_PTR(handle);
    if (!r || r->header.tag != MONAD_REF_TAG) return NULL;
    return r;
}

static rt_word ref_new_impl(rt_word init) {
    MONAD_STAT(MONAD_STAT_REF, sizeof(RefObj));
    RefObj* r = (RefObj*)RT_PTR(monad_region_alloc((rt_size)sizeof(RefObj)));
    if (!r) return 0;
    r->header.tag = MONAD_REF_TAG;
    __atomic_store_n(&r->value, init, __ATOMIC_RELEASE);
    return RT_WORD(r);
}

static rt_word ref_get_impl(rt_word handle) {
    RefObj* r = ref_of(handle);
    if (!r) return 0;
    return __atomic_load_n(&r->value, __ATOMIC_ACQUIRE);
}

static rt_word ref_set_impl(rt_word handle, rt_word v) {
    RefObj* r = ref_of(handle);
    if (r) __atomic_store_n(&r->value, v, __ATOMIC_RELEASE);
    return alloc_constructor_impl(0, 0);
}

static rt_word ref_update_impl(rt_word handle, rt_word f) {
    RefObj* r = ref_of(handle);
    if (!r) return 0;
    rt_word old = __atomic_load_n(&r->value, __ATOMIC_ACQUIRE);
    rt_word next;
    do {
        next = (rt_word)(intptr_t)apply_closure1_impl(RT_PTR(f), (int64_t)(intptr_t)old);
    } while (!__atomic_compare_exchange_n(&r->value, &old, next, 0,
                                          __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE));
    return next;
}

static int64_t ref_add_i64_impl(rt_word handle, int64_t delta) {
    RefObj* r = ref_of(handle);
    if (!r) return 0;
    rt_word old = __atomic_load_n(&r->value, __ATOMIC_ACQUIRE);
    int64_t next;
    do {
        /* Unsigned addition, then reinterpret: signed `+` here is UB on
           overflow and clang emits `add nsw`, while the interpreter and I64
           arithmetic wrap. */
        next = (int64_t)((uint64_t)(intptr_t)old + (uint64_t)delta);
    } while (!__atomic_compare_exchange_n(&r->value, &old, (rt_word)(intptr_t)next, 0,
                                          __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE));
    return next;
}

/* ── Cell (init/src/view.mo) ────────────────────────────────────────────
   An opaque LINEAR handle over one Copy payload word. Linearity is the
   checker's guarantee (view-types P1/P2): two fibers cannot legally hold
   the same Cell, so the payload word needs no lock -- unlike Ref, which
   is a shared cell. The block is GC-SCANNED (`monad_alloc`, not
   `monad_alloc_atomic`): a Copy payload can still be a `String` pointer,
   and an atomic block would hide it from Boehm.

   `view_free_impl` POISONS rather than frees. The block is Boehm-owned
   (`monad_release`'s own comment explains why free() would corrupt the
   collector); real freeing arrives with ownership-regions O3/O4, at
   which point this body becomes an owned free. Poisoning still makes a
   use-after-free fail its tag check deterministically during bring-up. */
typedef struct {
    Header header;
    rt_word payload;
} CellObj;

static CellObj* cell_of(rt_word handle) {
    CellObj* c = (CellObj*)RT_PTR(handle);
    if (!c || c->header.tag != MONAD_CELL_TAG) return NULL;
    return c;
}

static rt_word view_new_impl(rt_word init) {
    CellObj* c = (CellObj*)RT_PTR(monad_region_alloc((rt_size)sizeof(CellObj)));
    if (!c) return 0;
    c->header.tag = MONAD_CELL_TAG;
    c->payload = init;
    return RT_WORD(c);
}

/* Returns `Pair A (Cell A)` as a real constructor: the payload and the
   same handle must travel together, and the `.mo` wrapper may not use the
   handle twice (it is linear). */
static rt_word view_get_impl(rt_word handle) {
    CellObj* c = cell_of(handle);
    if (!c) return 0;
    Constructor* pair = (Constructor*)alloc_constructor_impl(MONAD_PAIR_TAG, 2);
    pair->fields[0] = c->payload;
    pair->fields[1] = handle;
    return RT_WORD(pair);
}

/* The fused do-bind's read half (`try_compile_view_bind_db`,
   lang/src/codegen/emit.mo). When the continuation destructures the pair
   immediately, codegen emits this instead of `monad_view_get`, so no
   `Pair` is allocated; the handle half is passed through separately,
   which is exactly what `view_get_impl` would have put in field 1 -- it
   returns the SAME word it was given. A poisoned or foreign handle reads
   0, the same answer `view_get_impl`'s failed tag check gives. */
static rt_word view_payload_impl(rt_word handle) {
    CellObj* c = cell_of(handle);
    if (!c) return 0;
    return c->payload;
}

static rt_word view_set_impl(rt_word handle, rt_word v) {
    CellObj* c = cell_of(handle);
    if (!c) return 0;
    c->payload = v;
    return handle;
}

static rt_word view_free_impl(rt_word handle) {
    CellObj* c = cell_of(handle);
    if (!c) return 0;
    /* Poison: a later op on this word fails the tag check instead of
       reading a payload the program believes freed. */
    c->header.tag = 0;
    c->payload = 0;
    return 0;
}

/* ── Slot (init/src/view.mo) ─────────────────────────────────────────────
   A linear handle that is either EMPTY or FULL, with the state carried in
   the type (`Slot Empty A` / `Slot Full A`), not a runtime tag the user can
   branch on. Unlike `Cell`, the payload need not be `Copy`: `take` moves it
   out and `fill` moves one in. The block is GC-SCANNED (a non-`Copy`
   payload can be, or can contain, a pointer).

   `slot_take` on an empty slot and `slot_peek` on a non-full one answer 0
   the way `Cell.get` does on a bad handle: well-typed code cannot reach
   them, and the state is enforced by the types plus linearity, not by a
   runtime error. `slot_free` POISONS for the same reason `view_free_impl`
   does (the block is Boehm-owned until ownership-regions O3/O4). */
typedef struct {
    Header header;
    rt_word payload;
    int64_t full;
} SlotObj;

static SlotObj* slot_of(rt_word handle) {
    SlotObj* s = (SlotObj*)RT_PTR(handle);
    if (!s || s->header.tag != MONAD_SLOT_TAG) return NULL;
    return s;
}

static rt_word slot_new_impl(rt_word init) {
    SlotObj* s = (SlotObj*)RT_PTR(monad_region_alloc((rt_size)sizeof(SlotObj)));
    if (!s) return 0;
    s->header.tag = MONAD_SLOT_TAG;
    s->payload = init;
    s->full = 1;
    return RT_WORD(s);
}

static rt_word slot_empty_impl(void) {
    SlotObj* s = (SlotObj*)RT_PTR(monad_region_alloc((rt_size)sizeof(SlotObj)));
    if (!s) return 0;
    s->header.tag = MONAD_SLOT_TAG;
    s->payload = 0;
    s->full = 0;
    return RT_WORD(s);
}

static rt_word slot_take_impl(rt_word handle) {
    SlotObj* s = slot_of(handle);
    if (!s || !s->full) return 0;
    Constructor* pair = (Constructor*)alloc_constructor_impl(MONAD_PAIR_TAG, 2);
    if (!pair) return 0;
    pair->fields[0] = s->payload;
    pair->fields[1] = handle;
    s->payload = 0;
    s->full = 0;
    return RT_WORD(pair);
}

static rt_word slot_fill_impl(rt_word handle, rt_word v) {
    SlotObj* s = slot_of(handle);
    if (!s) return 0;
    s->payload = v;
    s->full = 1;
    return handle;
}

static rt_word slot_peek_impl(rt_word handle) {
    SlotObj* s = slot_of(handle);
    if (!s || !s->full) return 0;
    Constructor* pair = (Constructor*)alloc_constructor_impl(MONAD_PAIR_TAG, 2);
    if (!pair) return 0;
    pair->fields[0] = s->payload;
    pair->fields[1] = handle;
    return RT_WORD(pair);
}

static rt_word slot_free_impl(rt_word handle) {
    SlotObj* s = slot_of(handle);
    if (!s) return 0;
    s->header.tag = 0;
    s->payload = 0;
    s->full = 0;
    return 0;
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
static int64_t monad_string_length_impl(char* s) {
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
   so. `rust/core/src/core_native.rs`'s two implementations must agree with
   these byte for byte: a disagreement shows up as the host and a
   self-compiled binary reporting different columns, which reads like a
   codegen bug and is not one. */
static int64_t monad_string_count_newlines_impl(char* s, int64_t len) {
    if (!s || len <= 0) return 0;
    int64_t n = 0;
    for (int64_t i = 0; i < len; i++) {
        if (s[i] == '\0') break;
        if (s[i] == '\n') n++;
    }
    return n;
}

static int64_t monad_string_trailing_chars_impl(char* s, int64_t len) {
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

static char* monad_string_concat_impl(char* a, char* b) {
    size_t la = a ? strlen(a) : 0;
    size_t lb = b ? strlen(b) : 0;
    char* out = (char*)RT_PTR(monad_region_alloc_atomic((rt_size)(la + lb + 1)));
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
static int64_t monad_string_eq_impl(char* a, char* b) {
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
   host's own `str < str`/`str > str` (`rust/core/src/core_native.rs`'s
   `string_lt`/`string_gt`, whose own doc comment notes UTF-8's byte
   ordering agrees with codepoint ordering) -- same `strcmp` choice
   `monad_string_eq` above already made, same "NULL treated as empty"
   tolerance as `monad_string_concat`. Returns a plain `int64_t` 0/1, not
   a real tagged `Bool` -- `NativeWrapKind.bool_result` (lang/codegen/
   emit.mo) does the raw-int-to-tagged-`Bool` conversion at the call
   site, matching `monad_string_eq`'s own convention. */
static int64_t monad_string_lt_impl(char* a, char* b) {
    const char* sa = a ? a : "";
    const char* sb = b ? b : "";
    return strcmp(sa, sb) < 0 ? 1 : 0;
}

static int64_t monad_string_gt_impl(char* a, char* b) {
    const char* sa = a ? a : "";
    const char* sb = b ? b : "";
    return strcmp(sa, sb) > 0 ? 1 : 0;
}

/* A UTF-8 continuation byte (0x80..0xBF) -- the byte AFTER one of the
   0xC0..0xF7 lead bytes and BEFORE the character's last byte. Position
   `i` lands in the MIDDLE of a character exactly when the byte at `i`
   is one of these. */
static int monad_utf8_continuation(char c) {
    return ((unsigned char)c & 0xC0) == 0x80;
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

   Byte-oriented and clamps rather than errors on any out-of-range
   input, bit-for-bit matching the Rust host's own reference semantics
   (`rust/core/src/core_native.rs`'s `string_slice`, `SharedStr::subslice`)
   so compiled and interpreted execution agree: `start` clamps into
   `[0, strlen(s)]`, `len` clamps to `>= 0` and to whatever remains
   after `start`, and a NULL `s` yields `""` -- never a panic/OOB read
   for a bad boundary or an over-long `len`. This INCLUDES subslice's
   UTF-8 character-boundary rule: a slice whose start or end byte lands
   in the middle of a multi-byte character is `""`, not the raw bytes
   (`SharedStr::subslice` falls back to empty on a non-boundary offset).
   Without this, a compiled TUI input decoder probing byte offsets of
   "é" read continuation bytes as standalone one-byte strings while the
   same code interpreted read `""` (see motes/tui/src/input.mo's
   byte-first walk, which is built around the `""` behavior).

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
   past the NUL because it stops there. The two boundary checks below are
   single-byte reads and do not change the O(start + len) cost; the
   bytes produced are unchanged for every whole-character slice. */
static char* monad_string_slice_impl(char* s, int64_t start_in, int64_t len_in) {
    if (!s) s = "";
    size_t start = 0;
    if (start_in > 0) {
        size_t want = (size_t)start_in;
        while (start < want && s[start] != '\0') start++;
    }
    /* start lands mid-character: the byte there is a continuation byte
       (a NUL here is the end of the string, which IS a boundary). */
    if (s[start] != '\0' && monad_utf8_continuation(s[start])) {
        char* out = (char*)RT_PTR(monad_region_alloc_atomic(1));
        if (!out) return NULL;
        out[0] = '\0';
        return out;
    }
    size_t len = len_in < 0 ? 0 : (size_t)len_in;
    if (len == 0) {
        char* out = (char*)RT_PTR(monad_region_alloc_atomic(1));
        if (!out) return NULL;
        out[0] = '\0';
        return out;
    }
    const void* nul = memchr(s + start, '\0', len);
    size_t avail = nul ? (size_t)((const char*)nul - (s + start)) : len;
    /* The slice ends mid-character: the byte just past its last byte is
       a continuation byte (a NUL means the slice ran to the string's
       end, which IS a boundary). */
    if (s[start + avail] != '\0' && monad_utf8_continuation(s[start + avail])) {
        char* out = (char*)RT_PTR(monad_region_alloc_atomic(1));
        if (!out) return NULL;
        out[0] = '\0';
        return out;
    }
    char* out = (char*)RT_PTR(monad_region_alloc_atomic(avail + 1));
    if (!out) return NULL;
    if (avail) memcpy(out, s + start, avail);
    out[avail] = '\0';
    return out;
}

/* `#[native string_drop]` (init/string.mo's `String.drop`) -- same
   reference semantics as `rust/core/src/core_native.rs`'s `string_drop`/
   `SharedStr::drop_prefix`: drops the first `n` bytes (clamped to
   `[0, strlen(s)]`), never errors on an out-of-range `n`. Like
   `monad_string_slice` above, `n` landing in the middle of a multi-byte
   character yields `""` (drop_prefix routes through subslice's
   boundary rule), not the raw remaining bytes.
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
static char* monad_string_drop_impl(int64_t n, char* s) {
    if (!s) return NULL;
    if (n <= 0) return s;
    size_t i = 0;
    while (i < (size_t)n && s[i] != '\0') i++;
    /* The drop point lands mid-character: a continuation byte (a NUL
       is the string's end, which IS a boundary and yields the empty
       tail). */
    if (s[i] != '\0' && monad_utf8_continuation(s[i])) {
        char* out = (char*)RT_PTR(monad_region_alloc_atomic(1));
        if (!out) return NULL;
        out[0] = '\0';
        return out;
    }
    return s + i;
}

/* djb2 hash: hash = hash * 33 + byte, seed 5381 -- bit-identical to
   `rust/core/src/core_native.rs`'s own `string_hash` (wrapping u64 mul/add)
   and to `init/string.mo`'s own `String.hash_selfhosted` reference
   implementation. Pure (no `IO` in String.hash's declared type), so
   this returns a plain i64 rather than the truthy-pointer convention
   above -- see `needs_io_wrap`'s own doc comment in lang/codegen/emit.mo. */
static int64_t monad_string_hash_impl(char* s) {
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
   (ByteBuf.of_string, ...) expects the SAME representation string
   LITERALS compile to: a bare `char*` (compile_lit_ir's Literal.str
   case emits a plain LLVM global constant, no StringObj wrapping at
   all). Boxing argv here via alloc_string produced a value with a
   totally different, incompatible layout (StringObj's `{ header;
   length; data[] }`, data offset well past the pointer's start) --
   the former `monad_print_str` reading straight from that pointer as if
   it were a C string just printed nothing/garbage from the header bytes instead
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
static char* monad_string_concat_list_impl(rt_word parts) {
    size_t total = 0;
    for (rt_word n = parts; n && monad_get_tag_impl(n) == 6; n = monad_get_field_impl(n, 1)) {
        char* piece = RT_STR(monad_get_field_impl(n, 0));
        if (piece) total += strlen(piece);
    }

    char* out = (char*)RT_PTR(monad_region_alloc_atomic((rt_size)(total + 1)));
    if (!out) return NULL;
    size_t at = 0;
    for (rt_word n = parts; n && monad_get_tag_impl(n) == 6; n = monad_get_field_impl(n, 1)) {
        char* piece = RT_STR(monad_get_field_impl(n, 0));
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
static char* monad_string_to_lowercase_impl(char* s) {
    if (!s) return NULL;
    size_t n = strlen(s);
    char* out = (char*)RT_PTR(monad_region_alloc_atomic(n + 1));
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
static char* monad_string_from_list_impl(rt_word list) {
    int64_t n = 0;
    for (rt_word cur = list; cur && monad_get_tag_impl(cur) == 6; ) {
        n++;
        cur = monad_get_field_impl(cur, 1);
    }
    char* out = (char*)RT_PTR(monad_region_alloc_atomic((rt_size)((size_t)n + 1)));
    if (!out) return NULL;
    int64_t i = 0;
    for (rt_word cur = list; cur && monad_get_tag_impl(cur) == 6; ) {
        out[i++] = (char)(RT_VALUE(monad_get_field_impl(cur, 0)) & 0xFF);
        cur = monad_get_field_impl(cur, 1);
    }
    out[n] = '\0';
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

   The SEMANTICS mirror `rust/core/src/core_native.rs`'s
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

/* The F32 family. An `F32` value is the f32-ROUNDED value held in a
   double (the uniform-storage invariant, plans/implementations/
   true-numeric-types.md 3.1): the payload's double converts to float
   exactly, every operation computes in `float` so each intermediate
   rounds to single precision, and the result widens back through
   double -- the C spelling of the reference's `(op(a, b) as f32) as
   f64`. `0.1f32 + 0.2f32` therefore equals `0.3f32` here exactly as
   it does in the interpreter. Division follows IEEE float rules, like
   the f64 family: no zero-divisor guard, `1.0f/0.0f` is `inf`. */
static float monad_f32_unbits(int64_t bits) {
    double d;
    memcpy(&d, &bits, sizeof d);
    return (float)d;
}
static int64_t monad_f32_bits(float f) {
    double d = (double)f;
    int64_t bits;
    memcpy(&bits, &d, sizeof bits);
    return bits;
}
int64_t monad_f32_add(int64_t a, int64_t b) { return monad_f32_bits(monad_f32_unbits(a) + monad_f32_unbits(b)); }
int64_t monad_f32_sub(int64_t a, int64_t b) { return monad_f32_bits(monad_f32_unbits(a) - monad_f32_unbits(b)); }
int64_t monad_f32_mul(int64_t a, int64_t b) { return monad_f32_bits(monad_f32_unbits(a) * monad_f32_unbits(b)); }
int64_t monad_f32_div(int64_t a, int64_t b) { return monad_f32_bits(monad_f32_unbits(a) / monad_f32_unbits(b)); }
int64_t monad_f32_eq(int64_t a, int64_t b) { return monad_f32_unbits(a) == monad_f32_unbits(b) ? 1 : 0; }
int64_t monad_f32_lt(int64_t a, int64_t b) { return monad_f32_unbits(a) < monad_f32_unbits(b) ? 1 : 0; }
int64_t monad_f32_gt(int64_t a, int64_t b) { return monad_f32_unbits(a) > monad_f32_unbits(b) ? 1 : 0; }

/* Signed-width integer arithmetic: the C spelling of the reference's
   `mask_to_suffix(op(mask_to_suffix(a), mask_to_suffix(b)))` -- C's
   `(int8_t)`/`(int16_t)`/`(int32_t)` casts ARE the reference's `v as iN`
   (both truncate to N bits and sign-extend). The narrow casts run the
   operation on int-promoted operands (no signed-overflow UB: two i8s
   cannot overflow int), and the i32 family computes in int64_t for the
   same reason. Division guards the zero divisor (0, like the
   evaluator's `native_int_div_width`) and runs in a WIDER integer so
   `INT_MIN / -1` wraps instead of triggering C's division UB; the
   closing narrow cast folds the wrapped quotient back (i8: -128). */
int64_t monad_i8_add(int64_t a, int64_t b) { return (int64_t)(int8_t)((int8_t)a + (int8_t)b); }
int64_t monad_i8_sub(int64_t a, int64_t b) { return (int64_t)(int8_t)((int8_t)a - (int8_t)b); }
int64_t monad_i8_mul(int64_t a, int64_t b) { return (int64_t)(int8_t)((int8_t)a * (int8_t)b); }
int64_t monad_i8_div(int64_t a, int64_t b) {
    int8_t x = (int8_t)a, y = (int8_t)b;
    if (y == 0) return 0;
    return (int64_t)(int8_t)((int)x / (int)y);
}
int64_t monad_i16_add(int64_t a, int64_t b) { return (int64_t)(int16_t)((int16_t)a + (int16_t)b); }
int64_t monad_i16_sub(int64_t a, int64_t b) { return (int64_t)(int16_t)((int16_t)a - (int16_t)b); }
int64_t monad_i16_mul(int64_t a, int64_t b) { return (int64_t)(int16_t)((int16_t)a * (int16_t)b); }
int64_t monad_i16_div(int64_t a, int64_t b) {
    int16_t x = (int16_t)a, y = (int16_t)b;
    if (y == 0) return 0;
    return (int64_t)(int16_t)((int)x / (int)y);
}
int64_t monad_i32_add(int64_t a, int64_t b) { return (int64_t)(int32_t)((int64_t)(int32_t)a + (int64_t)(int32_t)b); }
int64_t monad_i32_sub(int64_t a, int64_t b) { return (int64_t)(int32_t)((int64_t)(int32_t)a - (int64_t)(int32_t)b); }
int64_t monad_i32_mul(int64_t a, int64_t b) { return (int64_t)(int32_t)((int64_t)(int32_t)a * (int64_t)(int32_t)b); }
int64_t monad_i32_div(int64_t a, int64_t b) {
    int32_t x = (int32_t)a, y = (int32_t)b;
    if (y == 0) return 0;
    return (int64_t)(int32_t)((int64_t)x / (int64_t)y);
}
/* i16 comparisons: the one signed-width family that could not be an
   LLVM emitter -- `LLVMType` has no `i16_` and `LLVMValue` no `ashr`,
   so the trunc+sext shape its i8/i32 twins use (natives.mo's
   emit_i8_icmp_native) is unspellable there. C casts handle it in one
   line, the same C route the f64 comparison family takes. */
int64_t monad_i16_eq(int64_t a, int64_t b) { return (int16_t)a == (int16_t)b ? 1 : 0; }
int64_t monad_i16_lt(int64_t a, int64_t b) { return (int16_t)a < (int16_t)b ? 1 : 0; }
int64_t monad_i16_gt(int64_t a, int64_t b) { return (int16_t)a > (int16_t)b ? 1 : 0; }

/* `#[native "build_commit"]` (lang/main.mo's `build_commit : String`) --
   returns the git commit hash this binary was compiled from, baked in
   at build time via -DMONAD_BUILD_COMMIT. "unknown" if git was
   unavailable or the build wasn't from a repo. Pure (no `IO`), zero
   args, returns a `String` (char* = i64 in this backend's convention,
   same as `monad_process_id`). */
rt_str monad_build_commit(void) {
#ifdef MONAD_BUILD_COMMIT
    return RT_STR_WORD(MONAD_BUILD_COMMIT);
#else
    return RT_STR_WORD("unknown");
#endif
}

/* ─── Pointer FFI (`init/prelude.mo`'s `Ptr`) ──────────────────────── */

/* `Ptr.null : Ptr` -- the NULL pointer, for C functions whose callback
   argument is NULL (`SSL_set_verify` in motes/tls is the first caller). A
   `Ptr` value is its raw machine word, so the NULL word is the whole
   implementation. */
int64_t monad_ptr_null(void) {
    return 0;
}

/* `monad_ptr_minus_one` returns SQLite's fixed `SQLITE_TRANSIENT`
   sentinel, `(sqlite3_destructor_type)-1`. It takes NO argument and can
   return only that constant, so it cannot turn caller-supplied data into
   an arbitrary address. This is the IR-facing native convention: the
   uniform word is `i64` (`Ptr.minus_one` is a `#[native]`, not an extern). */
int64_t monad_ptr_minus_one(void) {
    return -1;
}

/* ─── ByteBuf (`std/bytebuf.mo`) ─────────────────────────────────────
   A flat byte buffer the C FFI can address: `SSL_read`/`SSL_write`
   (motes/tls) take a `void*` plus a length, and no other `std/` type
   exposes one.

   A `ByteBuf` value is a pointer to a `BufObj`: a GC-ALLOCATED block
   with its own `Header` kind (`MONAD_BUF_TAG`), an element kind, the
   element count, and the address of a 64-byte-aligned payload inside the
   same allocation. It is the u8 case (elem_kind 4) of the heap kind
   `plans/bootstrapping/mlir-codegen.md`'s `Buf E` generalises -- one
   `elem_kind` field apart -- so a kernel's `memref<Nxu8>` ABI and this
   buffer's `void*`-plus-length ABI are the same bytes.

   GC allocation is why `monad_bytebuf_free` is a deliberate no-op: a
   forgotten buffer is reclaimed, and a real `GC_free` on a word another
   live value still holds would be a use-after-free. The payload is
   allocated ATOMIC (it holds no pointers, exactly like every string
   buffer here), which is also what keeps the collector from scanning
   arbitrary bytes as addresses. `len` is recorded at construction and
   `to_list` CLAMPS to it, so nothing reads past what `alloc` reserved;
   `alloc` zero-fills so a round-trip test never depends on malloc's
   spare bytes. The list walks use the generated code's cons-chain
   conventions (tags 5/6), each head a byte as a raw word. */

typedef struct {
    Header         header;    /* refcount 1, tag MONAD_BUF_TAG */
    int64_t        elem_kind; /* 0=i64 1=f64 2=f32 3=i32 4=u8 */
    int64_t        len;       /* element count */
    unsigned char* payload;   /* 64-byte aligned; the round-up varies the
                                 offset, so it is stored, not recomputed */
} BufObj;

/* The payload begins at the first 64-byte boundary at or after the
   struct, inside ONE atomic allocation with `MONAD_BUF_ALIGN - 1` bytes
   of slack for the round-up. 64 is what a vectorised or coalesced load
   wants, and it makes "the allocated address is the aligned address"
   true by construction (mlir-codegen Decision 3); Boehm guarantees far
   less, hence the manual round-up rather than an aligned allocator. */
#define MONAD_BUF_ALIGN 64

/* Element kinds, indexed by `BufObj.elem_kind`. The values are the
   contract between this file, `std/src/buf.mo` and (eventually) the MLIR
   kernel ABI -- a `Buf F32` IS `memref<Nxf32>` because the payload is
   packed `float`s at this stride. Adding one means adding a `Buf.new_*`
   and its `get`/`set`, both here and in `codegen/src/natives.mo`. */
#define MONAD_ELEM_I64 0
#define MONAD_ELEM_F64 1
#define MONAD_ELEM_F32 2
#define MONAD_ELEM_I32 3
#define MONAD_ELEM_U8  4

/* Bytes per element. The payload size is `len * stride`, which is what
   makes the buffer a real `memref`: an `F32` element occupies four bytes,
   where an `Array`'s boxed field would occupy eight.

   EVERY kind is listed explicitly, `U8` included, and the `default` is the
   SMALLEST stride rather than the largest. `U8` falling through to a
   `default: return 8` was a real bug, found in review by RUNNING a u8
   `copy_into` rather than by reading this switch: the accessors
   (`get_u8`/`set_u8`) address ONE byte each, so the buffer disagreed with
   itself about its own element size. Both consequences were measured:

     * `Buf.copy_into dst off src` on u8 buffers mis-addressed -- a
       `memmove` to `dst->payload + off * 8`, into a payload whose elements
       sit at `off * 1`, so `Buf.copy_into dst 1 src` wrote to the wrong
       place and read back all zeros;
     * every u8 allocation was EIGHT TIMES its request, `ByteBuf`'s
       included, since `ByteBuf` is the u8 case and goes through the same
       `buf_new`.

   It was invisible here because the old `default` happened to be a
   *loadable* size: 8 is a valid stride for the other four kinds, so
   nothing failed loudly at this layer. That is why every kind is now
   named and the fallback is the SMALLEST stride -- an unknown kind can no
   longer silently over-allocate, and a new element kind has to be added
   here rather than inherited. */
static size_t buf_elem_size(int64_t kind) {
    switch (kind) {
        case MONAD_ELEM_I64:
        case MONAD_ELEM_F64: return 8;
        case MONAD_ELEM_I32:
        case MONAD_ELEM_F32: return 4;
        case MONAD_ELEM_U8:  return 1;
        default:             return 1;
    }
}

/* Every flat buffer in the runtime, `ByteBuf` included: ONE `BufObj`
   shape, `len` elements of `elem_kind` in a 64-byte-aligned atomic
   payload inside the same allocation. `ByteBuf` is the u8 case
   (`elem_kind` 4) and is now just a caller of this -- there is no second
   representation to keep in step.

   Atomic because the payload holds no pointers (the same reasoning as
   every string buffer here), which is also what keeps the collector from
   scanning float bit patterns as candidate addresses. 64-byte alignment
   makes "the allocated address is the aligned address" true by
   construction, which is the precondition the MLIR bare-pointer memref
   ABI needs (mlir-codegen Decision 3); Boehm guarantees far less, hence
   the manual round-up rather than an aligned allocator.

   A negative or huge `n` clamps rather than allocating: `n` is a Monad
   `I64` and negative literals are spellable, so `Buf.new_f32 -1` must be
   an empty buffer, not a wrap-around size. */
static BufObj* buf_new(int64_t n, int64_t elem_kind) {
    size_t stride = buf_elem_size(elem_kind);
    size_t len = n > 0 ? (size_t)n : 0;
    /* Overflow guard: `len * stride` must fit. A buffer larger than the
       address space is not a request this can honour, and silently
       wrapping would allocate something smaller than `len` claims --
       which every `get`/`set` bounds check would then be trusting. */
    if (len > (size_t)-1 / stride) len = 0;
    size_t bytes = len * stride;
    size_t size = sizeof(BufObj) + MONAD_BUF_ALIGN - 1 + bytes;
    if (size < bytes) return NULL;      /* sizeof + align overflowed */
    MONAD_STAT(MONAD_STAT_BYTEBUF, size);
    BufObj* obj = (BufObj*)RT_PTR(monad_region_alloc_atomic((rt_size)size));
    if (!obj) return NULL;
    obj->header.refcount = 1;
    obj->header.tag = MONAD_BUF_TAG;
    obj->header.flags = 0;
    obj->elem_kind = elem_kind;
    obj->len = (int64_t)len;
    obj->payload = (unsigned char*)(((uintptr_t)obj + sizeof(BufObj) + MONAD_BUF_ALIGN - 1)
                                    & ~(uintptr_t)(MONAD_BUF_ALIGN - 1));
    if (bytes) memset(obj->payload, 0, bytes);
    return obj;
}

/* The u8 case, kept as a name because fourteen existing call sites read
   better with it than with `buf_new(n, MONAD_ELEM_U8)`. */
static BufObj* bytebuf_new(int64_t n) {
    return buf_new(n, MONAD_ELEM_U8);
}

/* `IO.ByteBuf.alloc (n : I64) : IO ByteBuf` -- n zeroed bytes. A
   negative n clamps to 0 rather than allocating a huge size. */
static rt_word monad_bytebuf_alloc_impl(int64_t n) {
    return RT_WORD(bytebuf_new(n));
}

/* Count a `List U8` cons chain -- `monad_string_from_list`'s own walk,
   split out because `of_list` sizes the buffer before it copies. */
static int64_t byte_list_len(rt_word list) {
    int64_t n = 0;
    for (rt_word cur = list; cur && monad_get_tag_impl(cur) == 6; ) {
        n++;
        cur = monad_get_field_impl(cur, 1);
    }
    return n;
}

/* `IO.ByteBuf.of_list (xs : List U8) : IO ByteBuf` -- copy the list's
   bytes into a freshly sized buffer. */
static rt_word monad_bytebuf_of_list_impl(rt_word list) {
    int64_t n = byte_list_len(list);
    BufObj* obj = bytebuf_new(n);
    if (!obj) return RT_WORD(0);
    int64_t i = 0;
    for (rt_word cur = list; cur && monad_get_tag_impl(cur) == 6 && i < n; ) {
        obj->payload[i++] = (unsigned char)(RT_VALUE(monad_get_field_impl(cur, 0)) & 0xFF);
        cur = monad_get_field_impl(cur, 1);
    }
    return RT_WORD(obj);
}

/* `IO.ByteBuf.to_list (b : ByteBuf) (len : I64) : IO (List U8)` -- the
   first `len` bytes, built back-to-front so the list reads in memory
   order. A non-positive `len` yields
   `List.empty`; a `len` past what the buffer HOLDS clamps to it, so
   nothing reads out of bounds (the interpreter clamps identically --
   core_native.rs). */
static rt_word monad_bytebuf_to_list_impl(rt_word buf, int64_t len) {
    if (!buf || len <= 0) return alloc_constructor_impl(5, 0);  /* List.empty */
    BufObj* obj = (BufObj*)RT_PTR(buf);
    if (len > obj->len) len = obj->len;
    unsigned char* bytes = obj->payload;
    rt_word list = alloc_constructor_impl(5, 0);
    for (int64_t i = len - 1; i >= 0; i--) {
        Constructor* cons = (Constructor*)RT_PTR(alloc_constructor_impl(6, 2));
        if (!cons) break;
        cons->fields[0] = RT_FIELD((int64_t)bytes[i]);
        cons->fields[1] = RT_FIELD((int64_t)(intptr_t)list);
        list = RT_WORD(cons);
    }
    return list;
}

/* `bytebuf_to_string : ByteBuf -> I64 -> RawIO String` -- the first
   `len` bytes as a NUL-terminated GC string, clamped exactly as
   `monad_bytebuf_to_list` clamps (non-positive -> "", past the recorded
   length -> the recorded length). One memcpy instead of a cons cell per
   byte. A NUL inside the buffer survives the copy but, as with
   `monad_read_stdin_exact`'s bodies, ends the string for every
   strlen-based consumer. Returned raw; `raw_io_passthrough` wraps it. */
static void* monad_bytebuf_to_string_impl(rt_word buf, int64_t len) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    if (!obj || len < 0) len = 0;
    if (obj && len > obj->len) len = obj->len;
    char* out = (char*)RT_PTR(monad_region_alloc_atomic((rt_size)((size_t)len + 1)));
    if (!out) return NULL;
    if (len) memcpy(out, obj->payload, (size_t)len);
    out[len] = '\0';
    return out;
}

/* `bytebuf_of_string : String -> RawIO ByteBuf` -- a fresh buffer holding
   the string's bytes (without the NUL), `monad_bytebuf_of_list`'s shape
   from text. A NULL string is the empty buffer. */
static rt_word monad_bytebuf_of_string_impl(rt_str s) {
    char* str = RT_STR(s);
    size_t n = str ? strlen(str) : 0;
    BufObj* obj = bytebuf_new((int64_t)n);
    if (obj && n) memcpy(obj->payload, str, n);
    return RT_WORD(obj);
}

/* `bytebuf_truncate : ByteBuf -> I64 -> RawIO Unit` -- shrink the
   recorded length to `n`, clamped to `[0, len]`; the allocation stays as
   it is. Returned raw; `raw_io_passthrough` wraps it. */
static rt_word monad_bytebuf_truncate_impl(rt_word buf, int64_t n) {
    BufObj* obj = (BufObj*)RT_PTR(buf);
    if (obj) {
        if (n < 0) n = 0;
        if (n < obj->len) obj->len = n;
    }
    return alloc_constructor_impl(0, 0);
}

/* `bytebuf_copy_into : ByteBuf -> I64 -> ByteBuf -> RawIO ByteBuf` -- copy
   all of `src` into `dst` at `off`, clamped to `dst`'s length (never
   grows it); an offset outside `[0, dst->len]` copies nothing. `memmove`
   because `dst` and `src` may be the same buffer. Returns `dst`: the
   buffer is consumed and handed back, so a linear caller can thread it. */
static rt_word monad_bytebuf_copy_into_impl(rt_word dstw, int64_t off, rt_word srcw) {
    BufObj* dst = (BufObj*)RT_PTR(dstw);
    BufObj* src = (BufObj*)RT_PTR(srcw);
    if (dst && src && off >= 0 && off <= dst->len) {
        int64_t n = src->len < dst->len - off ? src->len : dst->len - off;
        if (n > 0) memmove(dst->payload + off, src->payload, (size_t)n);
    }
    return dstw;
}

/* `IO.ByteBuf.free (b : ByteBuf) : IO Unit` -- no-op (see the section
   comment); returns the Unit ctor like every `IO Unit` native. */
static rt_word monad_bytebuf_free_impl(rt_word buf) {
    (void)buf;
    return alloc_constructor_impl(0, 0);
}

/* `ByteBuf.ptr (b : ByteBuf) : Ptr` -- the payload address, which is
   what the FFI wants: the C function sees the bytes, not the object's
   header. */
static int64_t monad_bytebuf_ptr_impl(int64_t b) {
    return b ? (int64_t)(intptr_t)((BufObj*)RT_PTR(b))->payload : 0;
}

/* `ByteBuf.length (b : ByteBuf) : I64` -- the recorded element count. */
static int64_t monad_bytebuf_len_impl(int64_t b) {
    return b ? ((BufObj*)RT_PTR(b))->len : 0;
}

/* Read a pointer-sized out-parameter value from the START of a ByteBuf.
   This is `ByteBuf.take_ptr`'s backing native: the argument is the
   `BufObj` word, so the tag and recorded length are checkable, and a
   wrong-kind or too-short buffer returns 0 rather than reading past it.
   The Monad-level signature takes a `ByteBuf`, not an arbitrary `Ptr`. */
int64_t monad_bytebuf_take_ptr(int64_t buf) {
    BufObj* b = (BufObj*)RT_PTR(buf);
    if (!b || b->header.tag != MONAD_BUF_TAG || b->len < 8) return 0;
    return (int64_t)(intptr_t)(*(void**)b->payload);
}

rt_word monad_build_args(int argc, char** argv) {
    rt_word list = alloc_constructor_impl(5, 0);   /* List.empty */
    for (int i = argc - 1; i >= 0; i--) {
        Constructor* cons = (Constructor*)RT_PTR(alloc_constructor_impl(6, 2));
        /* head -- raw char*, matches string literals' own representation */
        cons->fields[0] = RT_FIELD((int64_t)(intptr_t)argv[i]);
        cons->fields[1] = RT_FIELD((int64_t)(intptr_t)list);
        list = RT_WORD(cons);
    }
    return list;
}


/* ─── i64 word ABI wrappers ───────────────────────────────────────────
   Codegen declares every one of these as `i64` parameters/returns. On
   LP64 `rt_word`/`rt_str` are the pointer types the implementations above
   use, so these are identity conversions and the native ABI is unchanged.
   On wasm32 they are the `int64_t` the emitted calls actually use; a
   pointer-typed definition would link with a signature mismatch warning
   (wasm-ld links anyway) and is invalid at run time. */

rt_word alloc_closure(rt_word entry, int64_t arity, int64_t env_size) {
    return alloc_closure_impl(entry, arity, env_size);
}
rt_void monad_closure_set_env(rt_word clos, int64_t idx, int64_t value) {
    monad_closure_set_env_impl(clos, idx, RT_FIELD(value));
    RT_VOID_RETURN;
}
int64_t monad_closure_get_env(rt_word clos, int64_t idx) {
    return RT_VALUE(monad_closure_get_env_impl(clos, idx));
}
int64_t apply_closure1(rt_word clos, int64_t a0) { return apply_closure1_impl(RT_PTR(clos), a0); }
int64_t apply_closure2(rt_word clos, int64_t a0, int64_t a1) { return apply_closure2_impl(RT_PTR(clos), a0, a1); }
int64_t apply_closure3(rt_word clos, int64_t a0, int64_t a1, int64_t a2) { return apply_closure3_impl(RT_PTR(clos), a0, a1, a2); }
int64_t apply_closure4(rt_word clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3) { return apply_closure4_impl(RT_PTR(clos), a0, a1, a2, a3); }
int64_t apply_closure5(rt_word clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4) { return apply_closure5_impl(RT_PTR(clos), a0, a1, a2, a3, a4); }
int64_t apply_closure6(rt_word clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5) { return apply_closure6_impl(RT_PTR(clos), a0, a1, a2, a3, a4, a5); }
int64_t apply_closure7(rt_word clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6) { return apply_closure7_impl(RT_PTR(clos), a0, a1, a2, a3, a4, a5, a6); }
int64_t apply_closure8(rt_word clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) { return apply_closure8_impl(RT_PTR(clos), a0, a1, a2, a3, a4, a5, a6, a7); }

rt_word alloc_constructor(int64_t tag, int64_t field_count) { return alloc_constructor_impl(tag, field_count); }
rt_word alloc_constructor_owned(int64_t tag, int64_t field_count) { return alloc_constructor_owned_impl(tag, field_count); }
rt_word alloc_string(rt_str data, int64_t length) { return alloc_string_impl(data, length); }
int64_t monad_get_tag(rt_word ptr) { return monad_get_tag_impl(ptr); }
rt_word monad_get_field(rt_word ptr, int64_t idx) { return monad_get_field_impl(ptr, idx); }
rt_void monad_set_field(rt_word ptr, int64_t idx, rt_word value) {
    monad_set_field_impl(ptr, idx, RT_FIELD(value));
    RT_VOID_RETURN;
}

rt_word monad_array_new(int64_t n, rt_word fill) { return monad_array_new_impl(n, fill); }
int64_t monad_array_len(rt_word a) { return monad_array_len_impl(a); }
rt_word monad_array_get(rt_word a, int64_t i) { return monad_array_get_impl(a, i); }
rt_word monad_array_get_or(rt_word a, int64_t i, rt_word fallback) {
    return monad_array_get_or_impl(a, i, fallback);
}
rt_word monad_array_with(rt_word a, int64_t i, rt_word v) { return monad_array_with_impl(a, i, v); }
rt_word monad_array_set_in_place(rt_word a, int64_t i, rt_word v) { return monad_array_set_in_place_impl(a, i, v); }
rt_word monad_array_freeze(rt_word b) { return monad_array_freeze_impl(b); }

rt_word monad_io_pure(int64_t a) { return monad_io_pure_impl(a); }
int64_t monad_io_bind(int64_t io_val, int64_t f) { return monad_io_bind_impl(io_val, f); }
int64_t monad_io_bind_guard(int64_t io_val) { return monad_io_bind_guard_impl(io_val); }

rt_word monad_cell_new(rt_word init) { return ref_new_impl(init); }
rt_word monad_cell_get(rt_word handle) { return ref_get_impl(handle); }
rt_word monad_cell_set(rt_word handle, rt_word v) { return ref_set_impl(handle, v); }
rt_word monad_cell_update(rt_word handle, rt_word f) { return ref_update_impl(handle, f); }
int64_t monad_cell_add_i64(rt_word handle, int64_t delta) { return ref_add_i64_impl(handle, delta); }

rt_word monad_view_new(rt_word init) { return view_new_impl(init); }
rt_word monad_view_get(rt_word handle) { return view_get_impl(handle); }
rt_word monad_view_payload(rt_word handle) { return view_payload_impl(handle); }
rt_word monad_view_set(rt_word handle, rt_word v) { return view_set_impl(handle, v); }
rt_word monad_view_free(rt_word handle) { return view_free_impl(handle); }

rt_word monad_slot_new(rt_word init) { return slot_new_impl(init); }
rt_word monad_slot_empty(void) { return slot_empty_impl(); }
rt_word monad_slot_take(rt_word handle) { return slot_take_impl(handle); }
rt_word monad_slot_fill(rt_word handle, rt_word v) { return slot_fill_impl(handle, v); }
rt_word monad_slot_peek(rt_word handle) { return slot_peek_impl(handle); }
rt_word monad_slot_free(rt_word handle) { return slot_free_impl(handle); }

int64_t monad_string_length(rt_str s) { return monad_string_length_impl(RT_STR(s)); }
int64_t monad_string_count_newlines(rt_str s, int64_t len) { return monad_string_count_newlines_impl(RT_STR(s), len); }
int64_t monad_string_trailing_chars(rt_str s, int64_t len) { return monad_string_trailing_chars_impl(RT_STR(s), len); }
rt_str monad_string_concat(rt_str a, rt_str b) { return RT_STR_WORD(monad_string_concat_impl(RT_STR(a), RT_STR(b))); }
int64_t monad_string_eq(rt_str a, rt_str b) { return monad_string_eq_impl(RT_STR(a), RT_STR(b)); }
int64_t monad_string_lt(rt_str a, rt_str b) { return monad_string_lt_impl(RT_STR(a), RT_STR(b)); }
int64_t monad_string_gt(rt_str a, rt_str b) { return monad_string_gt_impl(RT_STR(a), RT_STR(b)); }
rt_str monad_string_slice(rt_str s, int64_t start_in, int64_t len_in) { return RT_STR_WORD(monad_string_slice_impl(RT_STR(s), start_in, len_in)); }
rt_str monad_string_drop(int64_t n, rt_str s) { return RT_STR_WORD(monad_string_drop_impl(n, RT_STR(s))); }
int64_t monad_string_hash(rt_str s) { return monad_string_hash_impl(RT_STR(s)); }
rt_str monad_string_concat_list(rt_word parts) { return RT_STR_WORD(monad_string_concat_list_impl(parts)); }
rt_str monad_string_to_lowercase(rt_str s) { return RT_STR_WORD(monad_string_to_lowercase_impl(RT_STR(s))); }
rt_str monad_string_from_list(rt_word list) { return RT_STR_WORD(monad_string_from_list_impl(list)); }

/* ─── `Buf E` (`std/buf.mo`) ──────────────────────────────────────────
   The typed generalisation of `ByteBuf`: same `BufObj` heap kind, same
   64-byte-aligned atomic payload, but `elem_kind` says what the bytes ARE
   and `len` counts elements rather than bytes. A `Buf F32` is therefore
   literally `memref<Nxf32>` -- packed four-byte floats -- which is what
   lets a kernel take its `data_ptr` as a bare pointer with no conversion
   (plans/bootstrapping/mlir-codegen.md Decision 3).

   The boundary convention for element values follows the rest of the
   runtime's numeric natives: every argument and result is an `int64_t`
   WORD. For `I64`/`I32`/`U8` that word is the integer; for `F64` it is
   the double's bit pattern (`memcpy`, not a cast); for `F32` it is the
   f32-ROUNDED value held in a double, exactly the invariant
   `monad_f32_add` and its family already keep. So `Buf.get_f32` reads a
   `float` and widens it through `(double)`, and `Buf.set_f32` narrows to
   `float` before storing: the stored bytes are the single-precision
   value, and the word that comes back equals what went in.

   Every accessor BOUNDS-CHECKS and returns a zero element outside
   `[0, len)`. Two reasons: a Monad-side index is an `I64` and can be
   negative or past the end, and this is the one place a wrong index would
   otherwise read or write memory the buffer does not own. The interpreter
   clamps identically (core_native.rs), so a differential test on an
   out-of-range index agrees rather than diverging -- which is the whole
   value of having two backends. */

/* `Buf.length (b : Buf E) : I64` -- the element count, not the byte
   count. Wrong-kind or NULL gives 0. */
static int64_t monad_buf_len_impl(int64_t b) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!obj || obj->header.tag != MONAD_BUF_TAG) return 0;
    return obj->len;
}

/* `Buf.elem_kind (b : Buf E) : I64` -- which of the MONAD_ELEM_* kinds
   this buffer holds. Exposed because a kernel's derived `memref` element
   type is a function of it, and because a test wants to assert that
   `Buf.new_f32` really allocated an f32 buffer rather than a u8 one. */
static int64_t monad_buf_elem_kind_impl(int64_t b) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!obj || obj->header.tag != MONAD_BUF_TAG) return -1;
    return obj->elem_kind;
}

/* Shape shared by every `Buf.new_*`: allocate `n` zeroed elements of
   `elem_kind`. */
static rt_word buf_alloc_of(int64_t n, int64_t elem_kind) {
    return RT_WORD(buf_new(n, elem_kind));
}

static rt_word monad_buf_new_i64_impl(int64_t n) { return buf_alloc_of(n, MONAD_ELEM_I64); }
static rt_word monad_buf_new_f64_impl(int64_t n) { return buf_alloc_of(n, MONAD_ELEM_F64); }
static rt_word monad_buf_new_f32_impl(int64_t n) { return buf_alloc_of(n, MONAD_ELEM_F32); }
static rt_word monad_buf_new_i32_impl(int64_t n) { return buf_alloc_of(n, MONAD_ELEM_I32); }
static rt_word monad_buf_new_u8_impl(int64_t n)  { return buf_alloc_of(n, MONAD_ELEM_U8); }

/* Does `buf` hold `idx` as an element of `want_kind`? The single place
   the three checks live, so no accessor can forget one. A buffer of the
   WRONG element kind is rejected rather than reinterpreted: reading an
   `f32` buffer as `i64` would silently return two packed floats, and the
   Monad surface never needs it (`Buf.get_f32` takes a `Buf F32`). */
static int buf_elem_ok(BufObj* obj, int64_t idx, int64_t want_kind) {
    return obj && obj->header.tag == MONAD_BUF_TAG
        && obj->elem_kind == want_kind
        && idx >= 0 && idx < obj->len;
}

/* `Buf.get_i64` -- the I64 case, a straight word copy. */
static int64_t monad_buf_get_i64_impl(int64_t b, int64_t idx) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!buf_elem_ok(obj, idx, MONAD_ELEM_I64)) return 0;
    int64_t v;
    memcpy(&v, obj->payload + (size_t)idx * 8, sizeof v);
    return v;
}

/* `Buf.set_i64` -- clamps like every accessor; returns Unit. */
static rt_word monad_buf_set_i64_impl(int64_t b, int64_t idx, int64_t v) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (buf_elem_ok(obj, idx, MONAD_ELEM_I64)) {
        memcpy(obj->payload + (size_t)idx * 8, &v, sizeof v);
    }
    return alloc_constructor_impl(0, 0);
}

/* `Buf.get_f64` -- the payload word IS the double's bit pattern, which is
   both what `F64` means under this ABI and what a `memref<Nxf64>` kernel
   reads. No conversion, hence the straight memcpy. */
static int64_t monad_buf_get_f64_impl(int64_t b, int64_t idx) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!buf_elem_ok(obj, idx, MONAD_ELEM_F64)) return 0;
    int64_t bits;
    memcpy(&bits, obj->payload + (size_t)idx * 8, sizeof bits);
    return bits;
}

static rt_word monad_buf_set_f64_impl(int64_t b, int64_t idx, int64_t bits) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (buf_elem_ok(obj, idx, MONAD_ELEM_F64)) {
        memcpy(obj->payload + (size_t)idx * 8, &bits, sizeof bits);
    }
    return alloc_constructor_impl(0, 0);
}

/* `Buf.get_f32` / `Buf.set_f32`. The three representations must line up
   or the "round-trips identically under both runtimes" acceptance fails:
     * the WORD in/out is the f32-rounded value held in a double (this
       runtime's `F32` convention, see `monad_f32_unbits`);
     * the BYTES stored are the single-precision `float`, so a kernel
       reading `memref<Nxf32>` sees exactly the value Monad holds.
   `get` widens `float` back to double; `set` narrows before storing. So
   `set` then `get` returns the same word for anything already f32-exact,
   and for a wider double returns the f32 rounding -- which is what `F32`
   means here and what the interpreter does too. */
static int64_t monad_buf_get_f32_impl(int64_t b, int64_t idx) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!buf_elem_ok(obj, idx, MONAD_ELEM_F32)) return 0;
    float f;
    memcpy(&f, obj->payload + (size_t)idx * 4, sizeof f);
    double d = (double)f;
    int64_t bits;
    memcpy(&bits, &d, sizeof bits);
    return bits;
}

static rt_word monad_buf_set_f32_impl(int64_t b, int64_t idx, int64_t bits) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (buf_elem_ok(obj, idx, MONAD_ELEM_F32)) {
        double d;
        memcpy(&d, &bits, sizeof d);
        float f = (float)d;
        memcpy(obj->payload + (size_t)idx * 4, &f, sizeof f);
    }
    return alloc_constructor_impl(0, 0);
}

/* `Buf.get_i32` -- four bytes, SIGN-EXTENDED to the word, which is the
   same direction `emit_extern_param_cast` takes an `i32` return. */
static int64_t monad_buf_get_i32_impl(int64_t b, int64_t idx) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!buf_elem_ok(obj, idx, MONAD_ELEM_I32)) return 0;
    int32_t v;
    memcpy(&v, obj->payload + (size_t)idx * 4, sizeof v);
    return (int64_t)v;
}

static rt_word monad_buf_set_i32_impl(int64_t b, int64_t idx, int64_t v) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (buf_elem_ok(obj, idx, MONAD_ELEM_I32)) {
        int32_t n = (int32_t)v;
        memcpy(obj->payload + (size_t)idx * 4, &n, sizeof n);
    }
    return alloc_constructor_impl(0, 0);
}

/* `Buf.get_u8` -- one byte, zero-extended. */
static int64_t monad_buf_get_u8_impl(int64_t b, int64_t idx) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!buf_elem_ok(obj, idx, MONAD_ELEM_U8)) return 0;
    return (int64_t)obj->payload[idx];
}

static rt_word monad_buf_set_u8_impl(int64_t b, int64_t idx, int64_t v) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (buf_elem_ok(obj, idx, MONAD_ELEM_U8)) {
        obj->payload[idx] = (unsigned char)(v & 0xFF);
    }
    return alloc_constructor_impl(0, 0);
}

/* `Buf.data_ptr (b : Buf E) : Ptr` -- the payload address a kernel takes
   as a bare pointer. Package-private in `std/buf.mo` behind `with_ptr`,
   because a raw-memory escape hatch left open is a permanent hole; this
   is the only unsafe primitive the type needs.

   Wrong-kind gives 0 (NULL) rather than a pointer into a buffer whose
   element type the caller guessed wrong. */
static int64_t monad_buf_data_ptr_impl(int64_t b) {
    BufObj* obj = (BufObj*)RT_PTR(b);
    if (!obj || obj->header.tag != MONAD_BUF_TAG) return 0;
    return (int64_t)(intptr_t)obj->payload;
}

/* `buf_copy_into : Buf E -> I64 -> Buf E -> RawIO (Buf E)` -- `ByteBuf`'s
   gather, typed: copy every element of `src` into `dst` at `off`,
   clamped to `dst`'s remaining length (never grows it). Same element kind
   only; `memmove` because the two may be the same buffer.

   Byte counts come from `elem_kind`, so this cannot copy half an element,
   and it returns `dst` so a linear caller can thread it. */
static rt_word monad_buf_copy_into_impl(int64_t dstw, int64_t off, int64_t srcw) {
    BufObj* dst = (BufObj*)RT_PTR(dstw);
    BufObj* src = (BufObj*)RT_PTR(srcw);
    if (dst && src && dst->header.tag == MONAD_BUF_TAG && src->header.tag == MONAD_BUF_TAG
        && dst->elem_kind == src->elem_kind && off >= 0 && off <= dst->len) {
        int64_t n = src->len < dst->len - off ? src->len : dst->len - off;
        if (n > 0) {
            size_t stride = buf_elem_size(dst->elem_kind);
            memmove(dst->payload + (size_t)off * stride, src->payload, (size_t)n * stride);
        }
    }
    return RT_WORD(dstw);
}

rt_word monad_buf_new_i64(int64_t n) { return monad_buf_new_i64_impl(n); }
rt_word monad_buf_new_f64(int64_t n) { return monad_buf_new_f64_impl(n); }
rt_word monad_buf_new_f32(int64_t n) { return monad_buf_new_f32_impl(n); }
rt_word monad_buf_new_i32(int64_t n) { return monad_buf_new_i32_impl(n); }
rt_word monad_buf_new_u8(int64_t n)  { return monad_buf_new_u8_impl(n); }
int64_t monad_buf_len(int64_t b) { return monad_buf_len_impl(b); }
int64_t monad_buf_elem_kind(int64_t b) { return monad_buf_elem_kind_impl(b); }
int64_t monad_buf_get_i64(int64_t b, int64_t i) { return monad_buf_get_i64_impl(b, i); }
rt_word monad_buf_set_i64(int64_t b, int64_t i, int64_t v) { return monad_buf_set_i64_impl(b, i, v); }
int64_t monad_buf_get_f64(int64_t b, int64_t i) { return monad_buf_get_f64_impl(b, i); }
rt_word monad_buf_set_f64(int64_t b, int64_t i, int64_t v) { return monad_buf_set_f64_impl(b, i, v); }
int64_t monad_buf_get_f32(int64_t b, int64_t i) { return monad_buf_get_f32_impl(b, i); }
rt_word monad_buf_set_f32(int64_t b, int64_t i, int64_t v) { return monad_buf_set_f32_impl(b, i, v); }
int64_t monad_buf_get_i32(int64_t b, int64_t i) { return monad_buf_get_i32_impl(b, i); }
rt_word monad_buf_set_i32(int64_t b, int64_t i, int64_t v) { return monad_buf_set_i32_impl(b, i, v); }
int64_t monad_buf_get_u8(int64_t b, int64_t i) { return monad_buf_get_u8_impl(b, i); }
rt_word monad_buf_set_u8(int64_t b, int64_t i, int64_t v) { return monad_buf_set_u8_impl(b, i, v); }
int64_t monad_buf_data_ptr(int64_t b) { return monad_buf_data_ptr_impl(b); }
rt_word monad_buf_copy_into(int64_t dst, int64_t off, int64_t src) { return monad_buf_copy_into_impl(dst, off, src); }

rt_word monad_bytebuf_alloc(int64_t n) { return monad_bytebuf_alloc_impl(n); }
rt_word monad_bytebuf_of_list(rt_word list) { return monad_bytebuf_of_list_impl(list); }
rt_word monad_bytebuf_to_list(rt_word buf, int64_t len) { return monad_bytebuf_to_list_impl(buf, len); }
rt_str monad_bytebuf_to_string(rt_word buf, int64_t len) { return RT_STR_WORD(monad_bytebuf_to_string_impl(buf, len)); }
rt_word monad_bytebuf_of_string(rt_str s) { return monad_bytebuf_of_string_impl(s); }
rt_word monad_bytebuf_truncate(rt_word buf, int64_t n) { return monad_bytebuf_truncate_impl(buf, n); }
rt_word monad_bytebuf_copy_into(rt_word dst, int64_t off, rt_word src) { return monad_bytebuf_copy_into_impl(dst, off, src); }
rt_word monad_bytebuf_free(rt_word buf) { return monad_bytebuf_free_impl(buf); }
int64_t monad_bytebuf_ptr(int64_t b) { return monad_bytebuf_ptr_impl(b); }
int64_t monad_bytebuf_len(int64_t b) { return monad_bytebuf_len_impl(b); }
