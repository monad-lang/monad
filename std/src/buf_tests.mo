/// Round-trip tests for `std/src/buf.mo` -- the typed `Buf E`.
///
/// A separate file for the same reason `bytebuf_tests.mo` is one:
/// `buf.mo` is not on `std/src/lib.mo`'s re-export hub, and a `#[test]`
/// inside a hub module is never attributed to a target and is silently
/// skipped.
///
/// These tests are the differential gate `plans/bootstrapping/
/// mlir-codegen.md` Phase 0.5 asks for: `from_list`/`to_list` must
/// round-trip IDENTICALLY under both runtimes. Run this file under
/// `monad test` (the self-hosted/compiled path) and under the interpreter,
/// and the same assertions must hold -- which is why every value here is
/// exact and hand-checkable rather than computed.
///
/// Two shape rules borrowed from `bytebuf_tests.mo`, both forced by the
/// lowering rather than chosen: list literals live in top-level defs, never
/// inside a do-block, and equality is a hand-rolled walk rather than `==`
/// on a list (that resolves a `[BEq ...]` instance at run time, which the
/// compiled backend does not honour).
///
/// The `F32` tests are the ones that matter most. An `F32` element is four
/// bytes in the payload but its boundary word is the f32-rounded value
/// held in a double, so there are three representations in play and any
/// two of them disagreeing shows up here.

use std::buf {
    Buf.copy_into, Buf.elem_kind, Buf.from_list_f32, Buf.get_f32, Buf.get_i64,
    Buf.get_u8, Buf.length, Buf.new_f32, Buf.new_i64, Buf.new_u8, Buf.set_f32,
    Buf.set_i64, Buf.set_u8, Buf.to_list_f32,
}

/// The `MONAD_ELEM_*` codes the runtime assigns, asserted against
/// `Buf.elem_kind`. Kept as named defs so a renumbering in
/// `runtime/src/runtime_core.c` fails a test with the code rather than
/// with a mystery value.
def elem_f32 : I64 := 2
def elem_i64 : I64 := 0
def elem_u8 : I64 := 4

// ─── F32: the three-representation case ──────────────────────────────

/// Four values that are all exactly representable in single precision, so
/// no test depends on a rounding decision.
def f32_values : List F32 := [1.0f32, 2.5f32, -3.75f32, 1024.0f32]

/// What a fresh `new_f32 4` reads back as -- the zero fill.
def f32_zeros : List F32 := [0.0f32, 0.0f32, 0.0f32, 0.0f32]

/// `new_f32` records its ELEMENT count and reports the f32 kind. This is
/// what makes `Buf F32` a `memref<Nxf32>` rather than a byte blob.
#[test]
def test_new_f32_length_and_kind : IO Bool := do {
    let b <- Buf.new_f32 4;
    let s := Shared.of b;
    return (I64.beq (Buf.length s) 4 && I64.beq (Buf.elem_kind s) elem_f32)
}

/// The headline round trip: a list into a buffer and back out unchanged.
/// `set_f32` narrows to `float` and `get_f32` widens back, so this only
/// passes if the payload really holds single-precision values.
#[test]
def test_f32_from_list_round_trips : IO Bool := do {
    let b <- Buf.from_list_f32 f32_values;
    let xs <- Buf.to_list_f32 b;
    return (f32_eq xs f32_values)
}

/// A fresh buffer is zero-filled, so every read before any write is 0.0.
/// `alloc` zero-filling is what lets a test not depend on malloc's spare
/// bytes.
#[test]
def test_new_f32_is_zero_filled : IO Bool := do {
    let b <- Buf.new_f32 4;
    let xs <- Buf.to_list_f32 b;
    return (f32_eq xs f32_zeros)
}

/// An index past the end reads 0.0 rather than reading past the payload,
/// and a negative index does the same. The compiled accessor clamps; the
/// interpreter clamps identically; this asserts both do.
#[test]
def test_f32_out_of_range_reads_zero : IO Bool := do {
    let b <- Buf.from_list_f32 f32_values;
    let s := Shared.of b;
    let past := Buf.get_f32 s 99;
    let under := Buf.get_f32 s (-1);
    return (F32.beq past 0.0f32 && F32.beq under 0.0f32)
}

/// A write out of range is a no-op: the in-range contents are untouched
/// and the length does not grow.
#[test]
def test_f32_out_of_range_write_is_noop : IO Bool := do {
    let b <- Buf.from_list_f32 f32_values;
    let s := Shared.of b;
    let _w <- Buf.set_f32 (Shared.get s) 99 42.0f32;
    let xs <- Buf.to_list_f32 (Shared.get s);
    return (f32_eq xs f32_values)
}

/// A single write then read at a known index -- the smallest thing that
/// proves the element addressing (not just the bulk path) is right.
#[test]
def test_f32_set_then_get : IO Bool := do {
    let b <- Buf.new_f32 4;
    let _w <- Buf.set_f32 b 2 (-3.75f32);
    let s := Shared.of b;
    let v := Buf.get_f32 s 2;
    return (F32.beq v (-3.75f32))
}

// ─── I64 ─────────────────────────────────────────────────────────────

/// I64 round-trips exactly, including a negative value and one that does
/// not fit in 32 bits -- the latter is what a wrong element stride would
/// truncate.
#[test]
def test_i64_round_trips : IO Bool := do {
    let b <- Buf.new_i64 4;
    let s := Shared.of b;
    let _a <- Buf.set_i64 (Shared.get s) 0 7;
    let _c <- Buf.set_i64 (Shared.get s) 1 (-7);
    let _d <- Buf.set_i64 (Shared.get s) 2 0;
    let _e <- Buf.set_i64 (Shared.get s) 3 4611686018427387904;
    return (I64.beq (Buf.get_i64 s 0) 7
        && I64.beq (Buf.get_i64 s 1) (-7)
        && I64.beq (Buf.get_i64 s 2) 0
        && I64.beq (Buf.get_i64 s 3) 4611686018427387904)
}

#[test]
def test_new_i64_length_and_kind : IO Bool := do {
    let b <- Buf.new_i64 5;
    let s := Shared.of b;
    return (I64.beq (Buf.length s) 5 && I64.beq (Buf.elem_kind s) elem_i64)
}

// ─── U8 ──────────────────────────────────────────────────────────────

/// The byte case: `0` and `255` are the bound values a sign error would
/// flip.
#[test]
def test_u8_round_trips : IO Bool := do {
    let b <- Buf.new_u8 3;
    let s := Shared.of b;
    let _a <- Buf.set_u8 (Shared.get s) 0 0u8;
    let _c <- Buf.set_u8 (Shared.get s) 1 65u8;
    let _d <- Buf.set_u8 (Shared.get s) 2 255u8;
    return (U8.beq (Buf.get_u8 s 0) 0u8
        && U8.beq (Buf.get_u8 s 1) 65u8
        && U8.beq (Buf.get_u8 s 2) 255u8)
}

#[test]
def test_new_u8_length_and_kind : IO Bool := do {
    let b <- Buf.new_u8 8;
    let s := Shared.of b;
    return (I64.beq (Buf.length s) 8 && I64.beq (Buf.elem_kind s) elem_u8)
}

/// Bytes have a one-byte stride, so eight of them are eight elements --
/// an `F32` buffer of the same element count would be 32 bytes. Asserting
/// `length` here (and `length`/`elem_kind` above) is how the stride is
/// observed from Monad, since there is no byte-count accessor.
#[test]
def test_u8_length_is_element_count_not_bytes : IO Bool := do {
    let b <- Buf.new_u8 8;
    let s := Shared.of b;
    return (I64.beq (Buf.length s) 8)
}

// ─── shape edge cases ────────────────────────────────────────────────

/// A negative length clamps to an empty buffer rather than wrapping to a
/// huge one. The count is an `I64` and negative literals are spellable, so
/// this is reachable from ordinary source.
#[test]
def test_new_f32_negative_length_is_empty : IO Bool := do {
    let b <- Buf.new_f32 (-1);
    let s := Shared.of b;
    return (I64.beq (Buf.length s) 0)
}

/// Zero elements is a valid buffer: `from_list` of an empty list makes
/// one, and reading it is the clamp path rather than a crash.
#[test]
def test_from_list_empty : IO Bool := do {
    let b <- Buf.from_list_f32 List.empty;
    let s := Shared.of b;
    let xs <- Buf.to_list_f32 (Shared.get s);
    return (I64.beq (List.length xs) 0 && I64.beq (Buf.length s) 0)
}

/// A buffer large enough to cross the 64-byte alignment boundary many
/// times: 100 f32 elements are 400 bytes, so the payload spans six
/// alignment regions. If the stride or the payload offset were wrong,
/// this is where it shows.
#[test]
def test_f32_large_set_and_get : IO Bool := do {
    let b <- Buf.new_f32 100;
    let _w <- Buf.set_f32 b 99 42.0f32;
    let s := Shared.of b;
    return (F32.beq (Buf.get_f32 s 99) 42.0f32 && I64.beq (Buf.length s) 100)
}

// ─── copy_into ───────────────────────────────────────────────────────

/// Copy a whole buffer into another at offset 0. `copy_into` returns the
/// destination (the consumed-and-returned handle), so the caller threads
/// it on rather than naming `dst` twice.
#[test]
def test_copy_into_whole_buffer : IO Bool := do {
    let dst <- Buf.new_f32 4;
    let src <- Buf.from_list_f32 f32_values;
    let d2 <- Buf.copy_into dst 0 src;
    let xs <- Buf.to_list_f32 d2;
    return (f32_eq xs f32_values)
}

/// An offset outside `[0, length dst]` copies nothing -- the destination
/// keeps its own contents (zeros). Out-of-range is a no-op, never an
/// error and never a partial write.
#[test]
def test_copy_into_bad_offset_is_noop : IO Bool := do {
    let dst <- Buf.new_f32 4;
    let src <- Buf.from_list_f32 f32_values;
    let d2 <- Buf.copy_into dst 99 src;
    let xs <- Buf.to_list_f32 d2;
    return (f32_eq xs f32_zeros)
}

/// `copy_into` at a NONZERO offset, on a kind whose stride is not 8. This
/// is the regression test for the review bug in `buf_elem_size`: `U8`
/// fell through to a `default: return 8`, so `buf_new` sized the payload
/// at 8 bytes per element while `get_u8`/`set_u8` addressed one byte each.
/// With the two disagreeing, this test's `off = 1` copied to
/// `payload + 1 * 8` -- past the two bytes the source actually wrote --
/// and read back all zeros. Every other copy test used `f32` (stride 4)
/// or `off = 0`, neither of which can see an 8-vs-1 disagreement, which is
/// exactly why the bug survived the first round: the gap was in the TEST
/// SHAPES, not in the C.
#[test]
def test_copy_into_u8_at_offset : IO Bool := do {
    let src0 <- Buf.new_u8 2;
    let src := Shared.of src0;
    let _ <- Buf.set_u8 (Shared.get src) 0 1u8;
    let _ <- Buf.set_u8 (Shared.get src) 1 2u8;
    let dst0 <- Buf.new_u8 4;
    // Both buffers through `Shared` handles: each is written and then read
    // by the copy, so each is mentioned more than once (the same shape
    // `test_u8_round_trips` uses for its single buffer).
    let dst := Shared.of dst0;
    let _ <- Buf.set_u8 (Shared.get dst) 3 9u8;
    let d2 <- Buf.copy_into (Shared.get dst) 1 (Shared.get src);
    let s := Shared.of d2;
    return (U8.beq (Buf.get_u8 s 0) 0u8
        && U8.beq (Buf.get_u8 s 1) 1u8
        && U8.beq (Buf.get_u8 s 2) 2u8
        && U8.beq (Buf.get_u8 s 3) 9u8)
}

// ─── helpers ─────────────────────────────────────────────────────────
//
// Hand-rolled walks, per this file's header: `==` on a list would resolve
// a `[BEq ...]` instance at run time, which the compiled backend does not
// honour.

/// Element-wise `F32` equality over two lists of the same length.
#[terminating]
def f32_eq (xs ys : List F32) : Bool :=
    match xs {
        List.empty => List.is_empty ys,
        List.cons x rest =>
            match ys {
                List.empty => false,
                List.cons y more => F32.beq x y && f32_eq rest more,
            },
    }
