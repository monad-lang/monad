/// Standard library: `Buf E` -- a flat, unboxed, element-typed buffer.
///
/// This is the polymorphic generalisation of `ByteBuf`, and the two share
/// ONE heap kind (`BufObj`, `MONAD_BUF_TAG` in `runtime/src/runtime_core.c`):
/// an element kind, an element count, and a 64-byte-aligned atomic payload.
/// `ByteBuf` is the `u8` case; `Buf F32` is the case that matters here.
///
/// ## Why it is not `Array`
///
/// An `Array A` IS its backing constructor: one boxed 8-byte word per
/// element, from a `GC_malloc`'d block the collector scans for pointers
/// (`std/src/array.mo`'s representation note). That is the right shape for
/// a general-purpose sequence and the wrong one for a kernel argument: an
/// `F32` would occupy eight bytes instead of four, the collector would scan
/// float bit patterns as candidate addresses, and the address of the first
/// element would not be 64-byte aligned.
///
/// A `Buf E` is the other shape -- packed, typed, aligned, and invisible to
/// the collector -- so `Buf F32` genuinely IS `memref<Nxf32>` and a kernel
/// can take its payload address as a bare pointer with no conversion
/// (`plans/bootstrapping/mlir-codegen.md` Decision 3).
///
/// ## What is safe and what is not
///
/// Everything in this module except `data_ptr` is total: every index is
/// bounds-checked and an out-of-range access reads or writes nothing,
/// returning a zero element or leaving the buffer unchanged. That is
/// deliberately the same clamp the interpreter applies (`core_native.rs`),
/// so the two backends agree even on a wrong index -- which is the whole
/// point of having two.
///
/// `data_ptr` is the one unsafe primitive, and it is **not `pub`**. Raw
/// memory is reached only through `with_ptr`, which is the single place a
/// kernel launch can obtain an address; an escape hatch left open in a
/// dependently-typed language is a permanent hole. `with_ptr` needs a
/// kernel call to be useful, so the whole launch story arrives at once in
/// `plans/bootstrapping/mlir-codegen.md` Phase 2 -- until then `data_ptr`
/// is exercised only by the test that proves it returns the payload.
///
/// ## Element kinds, and the F32/U8 asymmetry
///
/// `I64`, `F64` and `F32` buffers are eight, eight and four bytes per
/// element; `I32` and `U8` are four and one. `get_f32`/`set_f32` store the
/// single-precision value in the payload and move it through the runtime's
/// `F32` boundary convention (an f32-rounded value held in a double), so
/// what a kernel reads from a `Buf F32` is exactly what Monad wrote.
///
/// `U8` is spelled as its own type here rather than reusing `ByteBuf`: one
/// heap kind, two surfaces, no conversion between them. Converting is
/// `Buf.copy_into` within a kind, or `to_list`/`from_list` across.
///
/// Values are opaque like `ByteBuf` and `FdStream`: never pattern-match,
/// compare or print one.
use std::array {Array}
use std::list {List.length}

/// A flat buffer of `len` elements, each of the kind its constructor
/// chose. Inhabited by its witness and built only by this module's
/// `new_*` natives -- there is no way to forge one.
pub type Buf E {
    buf_witness
}

// ─── constructors ────────────────────────────────────────────────────
//
// One native per element kind rather than one native taking a kind tag:
// the kind is a property of the TYPE, and a Monad caller must not be able
// to pass the wrong one. A negative count clamps to an empty buffer (the
// count is an `I64`, and negative literals are spellable).

#[native "buf_new_i64"]
priv def buf_new_i64_raw (n : I64) : RawIO (Buf I64)

#[native "buf_new_f64"]
priv def buf_new_f64_raw (n : I64) : RawIO (Buf F64)

#[native "buf_new_f32"]
priv def buf_new_f32_raw (n : I64) : RawIO (Buf F32)

#[native "buf_new_i32"]
priv def buf_new_i32_raw (n : I64) : RawIO (Buf I32)

#[native "buf_new_u8"]
priv def buf_new_u8_raw (n : I64) : RawIO (Buf U8)

/// `n` zeroed `I64` elements.
pub def Buf.new_i64 (n : I64) : IO (Buf I64) := IO.mk (buf_new_i64_raw n)

/// `n` zeroed `F64` elements.
pub def Buf.new_f64 (n : I64) : IO (Buf F64) := IO.mk (buf_new_f64_raw n)

/// `n` zeroed `F32` elements -- four bytes each, so this is the buffer a
/// `memref<Nxf32>` kernel takes.
pub def Buf.new_f32 (n : I64) : IO (Buf F32) := IO.mk (buf_new_f32_raw n)

/// `n` zeroed `I32` elements.
pub def Buf.new_i32 (n : I64) : IO (Buf I32) := IO.mk (buf_new_i32_raw n)

/// `n` zeroed bytes.
pub def Buf.new_u8 (n : I64) : IO (Buf U8) := IO.mk (buf_new_u8_raw n)

// ─── shape ───────────────────────────────────────────────────────────

// The natives take the BARE buffer and the public surface takes `Shared`.
// That split is not cosmetic and it is not optional: a `#[native]` whose
// parameter is declared `Shared (Buf E)` is handed the `Shared.of`
// CONSTRUCTOR BOX, not the `BufObj*` inside it, because `Shared` is an
// ordinary boxed single-constructor type with no unwrapping at the native
// boundary (`codegen/src/ctors.mo` has no builtin tag for it, and
// `parm_values_for` passes `LLVMValue.parm_` straight through). The first
// version of this module declared `buf_len (b : Shared (Buf E))` and every
// length read as 0 and every kind as -1 -- measured 2026-11-10, and it is
// why `std/src/io.mo`'s `ByteBuf` call sites all spell `Shared.get src`.
// So: unwrap in Monad, hand the native the payload.
//
// `Shared.get` is a no-op at run time (one field read), so this costs
// nothing, and it keeps the affine story intact -- a `Buf E` parameter
// could be read once, a `Shared (Buf E)` parameter any number of times.
#[native "buf_len"]
priv def buf_len_raw (b : Buf E) : I64

/// How many elements the buffer holds (its element count, not its byte
/// size -- `test_u8_length_is_element_count_not_bytes` pins that).
pub def Buf.length (b : Shared (Buf E)) : I64 := buf_len_raw (Shared.get b)

/// Which element kind this buffer holds, as the runtime's
/// `MONAD_ELEM_*` code (0=I64 1=F64 2=F32 3=I32 4=U8; -1 for something
/// that is not a `Buf`). Exposed for tests and for the diagnostic that
/// will derive a kernel's `memref` element type -- not for dispatch in
/// ordinary code, where the type parameter already says it.
#[native "buf_elem_kind"]
priv def buf_elem_kind_raw (b : Buf E) : I64

pub def Buf.elem_kind (b : Shared (Buf E)) : I64 := buf_elem_kind_raw (Shared.get b)

// ─── element access ──────────────────────────────────────────────────
//
// `get` is pure and returns the element; `set` is `IO` and returns Unit.
// Both are bounds-checked against the recorded element count AND the
// element kind, so reading a `Buf F32` as `I64` is impossible from Monad
// (the signature says `Buf F32`) and a forged wrong-kind value reads
// zero rather than two packed floats.

// The `get` accessors take `Shared (Buf E)`, not `Buf E`: a buffer is a
// mutable handle and therefore affine, so a bare `Buf E` parameter could
// be read exactly ONCE. "Read element 0, then read element 3" is the
// most ordinary thing a caller does with a buffer, and requiring
// `Shared.of` at every such site (as `std/src/io.mo` does for `ByteBuf`)
// makes the common case noisy. A shared handle is a read-only view by
// construction (`init/src/shared.mo`), which is exactly what `get`
// needs, and it costs nothing: `Shared.of` is one box, and the payload is
// untouched either way.
//
// The `set` accessors keep the ordinary `Buf E` and are `IO`-scoped,
// because a write is the mutation the affine rule is protecting.

#[native "buf_get_i64"]
priv def buf_get_i64_raw (b : Buf I64) (i : I64) : I64

pub def Buf.get_i64 (b : Shared (Buf I64)) (i : I64) : I64 :=
    buf_get_i64_raw (Shared.get b) i

#[native "buf_set_i64"]
priv def buf_set_i64_raw (b : Buf I64) (i : I64) (v : I64) : RawIO Unit

#[native "buf_get_f64"]
priv def buf_get_f64_raw (b : Buf F64) (i : I64) : F64

pub def Buf.get_f64 (b : Shared (Buf F64)) (i : I64) : F64 :=
    buf_get_f64_raw (Shared.get b) i

#[native "buf_set_f64"]
priv def buf_set_f64_raw (b : Buf F64) (i : I64) (v : F64) : RawIO Unit

#[native "buf_get_f32"]
priv def buf_get_f32_raw (b : Buf F32) (i : I64) : F32

pub def Buf.get_f32 (b : Shared (Buf F32)) (i : I64) : F32 :=
    buf_get_f32_raw (Shared.get b) i

#[native "buf_set_f32"]
priv def buf_set_f32_raw (b : Buf F32) (i : I64) (v : F32) : RawIO Unit

#[native "buf_get_i32"]
priv def buf_get_i32_raw (b : Buf I32) (i : I64) : I32

pub def Buf.get_i32 (b : Shared (Buf I32)) (i : I64) : I32 :=
    buf_get_i32_raw (Shared.get b) i

#[native "buf_set_i32"]
priv def buf_set_i32_raw (b : Buf I32) (i : I64) (v : I32) : RawIO Unit

#[native "buf_get_u8"]
priv def buf_get_u8_raw (b : Buf U8) (i : I64) : U8

pub def Buf.get_u8 (b : Shared (Buf U8)) (i : I64) : U8 :=
    buf_get_u8_raw (Shared.get b) i

#[native "buf_set_u8"]
priv def buf_set_u8_raw (b : Buf U8) (i : I64) (v : U8) : RawIO Unit

pub def Buf.set_i64 (b : Buf I64) (i : I64) (v : I64) : IO Unit :=
    IO.mk (buf_set_i64_raw b i v)

pub def Buf.set_f64 (b : Buf F64) (i : I64) (v : F64) : IO Unit :=
    IO.mk (buf_set_f64_raw b i v)

pub def Buf.set_f32 (b : Buf F32) (i : I64) (v : F32) : IO Unit :=
    IO.mk (buf_set_f32_raw b i v)

pub def Buf.set_i32 (b : Buf I32) (i : I64) (v : I32) : IO Unit :=
    IO.mk (buf_set_i32_raw b i v)

pub def Buf.set_u8 (b : Buf U8) (i : I64) (v : U8) : IO Unit :=
    IO.mk (buf_set_u8_raw b i v)

// ─── bulk ────────────────────────────────────────────────────────────

#[native "buf_copy_into"]
priv def buf_copy_into_raw (dst : Buf E) (offset : I64) (src : Buf E) : RawIO (Buf E)

/// Copy every element of `src` into `dst` starting at element `offset`.
/// One `memmove`, CLAMPED to `dst`'s remaining length -- this never grows
/// `dst`, and an offset outside `[0, Buf.length dst]` copies nothing.
/// Same element kind only; the runtime rejects a mismatch rather than
/// reinterpreting bytes.
///
/// Consumes and returns `dst` (view-types P2's shape, as
/// `ByteBuf.copy_into`): the caller threads the returned handle on rather
/// than mentioning the input twice, which is what the affine rule wants.
pub def Buf.copy_into (dst : Buf E) (offset : I64) (src : Buf E) : IO (Buf E) :=
    IO.mk (buf_copy_into_raw dst offset src)

/// `List F32` -> `Buf F32`: an O(n) unbox-and-pack, once, explicitly, and
/// visible in the source rather than hidden in an ABI. `Array` goes
/// through `Buf.from_list_f32 (Array.to_list a)`; there is no direct
/// `Array` entry point because a `Buf` is built by repeated writes and a
/// `List` is what `Array.to_list` already produces.
///
/// The buffer is written under `IO` and threaded on by RETURN VALUE
/// rather than reused across calls. That is not stylistic: `Buf` is an
/// affine mutable handle, so naming `b` twice is exactly the double-use
/// the affine rule refuses -- the same reason `ByteBuf.copy_into` returns
/// `dst` instead of taking it again.
///
/// `List` is affine too, but its own `List.cons` carries no constraint,
/// so the recursion below passes `xs` once per step.
def Buf.from_list_f32 (xs : List F32) : IO (Buf F32) := do {
    let n := List.length (Shared.get (Shared.of xs));
    let b <- Buf.new_f32 n;
    fill_f32 (Shared.of b) 0 xs
}

/// `#[shared]`-threaded, not `b` twice: `fill_f32 b i (List.cons x more)`
/// mentions `b` in both its head and its recursion, which is the
/// double-use the affine rule refuses. Taking the buffer as a `Shared`
/// handle costs one box for the whole walk and keeps the write path
/// linear -- the same shape `std/src/io.mo`'s chunk gatherer uses.
def fill_f32 (bs : Shared (Buf F32)) (i : I64) (rest : List F32) : IO (Buf F32) :=
    match rest {
        List.empty => IO.pure (Shared.get bs),
        List.cons x more => do {
            let _w <- Buf.set_f32 (Shared.get bs) i x;
            fill_f32 bs (i + 1) more
        },
    }

/// `Buf F32` -> `List F32`, one element per index. The buffer travels as
/// a `Shared` handle for the same affine reason `from_list_f32` gives:
/// every read is a separate use of the same buffer.
pub def Buf.to_list_f32 (b : Buf F32) : IO (List F32) := do {
    let s := Shared.of b;
    let n := Buf.length s;
    to_list_f32_from s 0 n
}

/// `#[terminating]`: the recursion descends an `I64` index toward a
/// constant bound. That is well-founded but not a structural subterm, so
/// the checker cannot see it -- the corpus standard for an index walk
/// (`std/src/map.mo` is full of them; 969 uses repo-wide).
#[terminating]
def to_list_f32_from (s : Shared (Buf F32)) (i : I64) (n : I64) : IO (List F32) :=
    if I64.lt i n
    then do {
        let rest <- to_list_f32_from s (i + 1) n;
        IO.pure (List.cons (Buf.get_f32 s i) rest)
    }
    else IO.pure List.empty

/// `Buf.data_ptr : Buf E -> Ptr` -- the payload address. The one unsafe
/// primitive in this module, and **not `pub`**: it is reachable only from
/// `with_ptr`, so raw memory never escapes to a caller who did not ask
/// for it by name.
#[native "buf_data_ptr"]
priv def Buf.data_ptr (b : Shared (Buf E)) : Ptr

/// Run `f` with the buffer's payload address, for a kernel call or a C
/// FFI function that writes into it. The address is valid only for the
/// duration of `f`, and only as long as `b` is live -- `Buf` is affine
/// and not `Copy`, so the type system keeps the buffer alive across the
/// call.
///
/// This is the scoped form the unsafe primitive is meant to be used
/// through; `data_ptr` itself stays private so there is no way to obtain
/// an address that outlives its scope by accident.
pub def Buf.with_ptr {A : Type} (b : Buf E) (f : Ptr -> A) : A :=
    f (Buf.data_ptr (Shared.of b))
