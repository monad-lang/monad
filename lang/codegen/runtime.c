#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

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

void* monad_alloc(size_t size) {
    void* ptr = malloc(size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return ptr;
}

void monad_retain(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    atomic_fetch_add(&h->refcount, 1);
}

void monad_release(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    if (atomic_fetch_sub(&h->refcount, 1) == 1) {
        free(h);
    }
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

int64_t apply_closure1(void* clos, int64_t a0) {
    return ((Fn2)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0);
}
int64_t apply_closure2(void* clos, int64_t a0, int64_t a1) {
    return ((Fn3)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1);
}
int64_t apply_closure3(void* clos, int64_t a0, int64_t a1, int64_t a2) {
    return ((Fn4)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2);
}
int64_t apply_closure4(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3) {
    return ((Fn5)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3);
}
int64_t apply_closure5(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4) {
    return ((Fn6)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4);
}
int64_t apply_closure6(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5) {
    return ((Fn7)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5);
}
int64_t apply_closure7(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6) {
    return ((Fn8)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5, a6);
}
int64_t apply_closure8(void* clos, int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) {
    return ((Fn9)((Closure*)clos)->entry)((int64_t)(intptr_t)clos, a0, a1, a2, a3, a4, a5, a6, a7);
}

void* alloc_constructor(int64_t tag, int64_t field_count) {
    size_t size = sizeof(Constructor) + field_count * sizeof(void*);
    Constructor* c = (Constructor*)monad_alloc(size);
    if (c) {
        c->header.tag = 2;
        c->tag = tag;
        c->field_count = field_count;
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
    char* out = (char*)malloc((size_t)len + 1);
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
    char* out = (char*)malloc(la + lb + 1);
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
    char* out = (char*)malloc(len + 1);
    if (!out) return NULL;
    if (len) memcpy(out, s + start, len);
    out[len] = '\0';
    return out;
}

/* `#[native string_drop]` (init/string.mo's `String.drop`) -- same gap
   and same reference semantics as `monad_string_slice` above
   (`core/src/core_native.rs`'s `string_drop`/`SharedStr::drop_prefix`):
   drops the first `n` bytes (clamped to `[0, strlen(s)]`), never errors
   on an out-of-range `n`. */
char* monad_string_drop(int64_t n, char* s) {
    size_t slen = s ? strlen(s) : 0;
    size_t start = n < 0 ? 0 : (size_t)n;
    if (start > slen) start = slen;
    size_t len = slen - start;
    char* out = (char*)malloc(len + 1);
    if (!out) return NULL;
    if (len) memcpy(out, s + start, len);
    out[len] = '\0';
    return out;
}

char* monad_read_file(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (size < 0) { fclose(f); return NULL; }
    char* buf = (char*)malloc(size + 1);
    if (!buf) { fclose(f); return NULL; }
    size_t got = fread(buf, 1, size, f);
    fclose(f);
    if (got != (size_t)size) { free(buf); return NULL; }
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
    /* Exclude argv[0] (the binary's own path) -- matches the
       interpreter's own `run <file> <args...>` semantics (args passed to
       a compiled program's `main` are just the extra CLI args, not the
       program's own path), and makes an empty `args` list actually
       reachable (e.g. examples/hello.mo's "no arguments" fallback). */
    void* args = monad_build_args(argc - 1, argv + 1);
    return (int)main_monad(args);
}
