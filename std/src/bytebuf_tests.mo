/// Round-trip tests for `std/src/bytebuf.mo`.
///
/// A separate file because `bytebuf.mo` deliberately stays off
/// `std/src/lib.mo`'s re-export hub: a `#[test]` inside one of the hub's
/// modules is never attributed to a target and is silently skipped (see
/// process.mo's foot note). Direct file, same discovery as
/// `sha256_tests.mo`.
///
/// Two shape rules the tests obey because lowering forces them, not for
/// style. List literals live in top-level defs, never inside a do-block
/// (the block desugars through `Monad.bind`, and a `FromListLiteral`
/// class call inside it desyncs the match queue -- the lowering
/// MatchTraversalMismatch). And equality is a hand-rolled walk over
/// `U8.beq`, never `==` on a list: that resolves a `[BEq U8]`-keyed
/// instance at run time, and constrained instance dispatch is exactly
/// what this backend does not honor (`unresolved global: BEq.beq`).

use std::bytebuf {ByteBuf.alloc, ByteBuf.free, ByteBuf.of_list, ByteBuf.to_list}
use std::list {List.length}

def empty_bytes : List U8 := List.empty

def one_byte : List U8 := [9u8]

/// An interior zero between non-zero bytes -- the case a
/// NUL-terminated-string implementation passes everything else on.
def interior_zero : List U8 := [65u8, 0u8, 66u8, 0u8, 67u8]

def three_bytes : List U8 := [1u8, 2u8, 3u8]

/// The first two of `three_bytes` -- what a `to_list b 2` must yield.
def first_two : List U8 := [1u8, 2u8]

/// `n` zero bytes.
#[terminating]
def zeros (n : I64) : List U8 :=
    if I64.beq n 0 then List.empty
    else List.cons 0u8 (zeros (n - 1))

/// Descending bytes whose low 8 bits are 0, 1, ..., n-1 -- varied
/// content, with a `0u8` at every multiple of 256.
#[terminating]
def ramp (n : I64) : List U8 :=
    if I64.beq n 0 then List.empty
    else List.cons (U32.to_u8 (I64.to_u32 (n - 1))) (ramp (n - 1))

/// Byte-wise structural equality, on the native `U8.beq` rather than a
/// `BEq` dispatch.
#[terminating]
def bytes_eq (xs ys : List U8) : Bool :=
    match xs {
        List.empty =>
            match ys {
                List.empty => true,
                List.cons _ _ => false
            },
        List.cons h t =>
            match ys {
                List.empty => false,
                List.cons h2 t2 => U8.beq h h2 && bytes_eq t t2
            }
    }

#[test]
def test_of_list_empty_round_trips : IO Bool := do {
    let b <- ByteBuf.of_list empty_bytes;
    let xs <- ByteBuf.to_list b 0;
    return (bytes_eq xs empty_bytes)
}

#[test]
def test_of_list_one_byte_round_trips : IO Bool := do {
    let b <- ByteBuf.of_list one_byte;
    let xs <- ByteBuf.to_list b 1;
    return (bytes_eq xs one_byte)
}

#[test]
def test_of_list_interior_zero_round_trips : IO Bool := do {
    let b <- ByteBuf.of_list interior_zero;
    let xs <- ByteBuf.to_list b 5;
    return (bytes_eq xs interior_zero)
}

#[test]
def test_of_list_4k_round_trips : IO Bool := do {
    let big : List U8 := ramp 4096;
    let b <- ByteBuf.of_list big;
    let xs <- ByteBuf.to_list b 4096;
    return (I64.beq (List.length xs) 4096 && bytes_eq xs big)
}

/// `to_list` reads only the first `len` bytes -- the whole point of the
/// parameter (`SSL_read` returns how many it wrote).
#[test]
def test_to_list_takes_only_len_bytes : IO Bool := do {
    let b <- ByteBuf.of_list three_bytes;
    let xs <- ByteBuf.to_list b 2;
    return (bytes_eq xs first_two)
}

#[test]
def test_to_list_zero_len_is_empty : IO Bool := do {
    let b <- ByteBuf.of_list three_bytes;
    let xs <- ByteBuf.to_list b 0;
    return (bytes_eq xs empty_bytes)
}

#[test]
def test_alloc_zero_fills : IO Bool := do {
    let b <- ByteBuf.alloc 16;
    let xs <- ByteBuf.to_list b 16;
    return (bytes_eq xs (zeros 16))
}

/// `free` must merely succeed; the buffer is unusable afterwards by
/// contract, so there is nothing observable left to assert.
#[test]
def test_free_succeeds : IO Bool := do {
    let b <- ByteBuf.alloc 4;
    let u <- ByteBuf.free b;
    return true
}