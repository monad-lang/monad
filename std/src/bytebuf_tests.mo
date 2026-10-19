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

use std::bytebuf {ByteBuf.alloc, ByteBuf.copy_into, ByteBuf.free, ByteBuf.length, ByteBuf.of_list, ByteBuf.of_string, ByteBuf.to_list, ByteBuf.to_string, ByteBuf.truncate}
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

/// The recorded length is what the buffer was created with -- `alloc`'s
/// `n` on one side, the list's length on the other.
#[test]
def test_length_after_alloc : IO Bool := do {
    let b <- ByteBuf.alloc 16;
    return (I64.beq (ByteBuf.length b) 16)
}

#[test]
def test_length_after_of_list : IO Bool := do {
    let b <- ByteBuf.of_list interior_zero;
    return (I64.beq (ByteBuf.length b) 5)
}

/// A negative `n` clamps to 0, and the recorded length follows the
/// clamp rather than the argument.
#[test]
def test_alloc_negative_length_is_zero : IO Bool := do {
    let b <- ByteBuf.alloc (-1);
    return (I64.beq (ByteBuf.length b) 0)
}

/// `to_list` clamps `len` to the recorded length, so over-asking returns
/// the whole buffer rather than reading past it. Both backends must agree
/// here: the compiled side over-read out of contract before the `BufObj`
/// carried a length, while the interpreter always clamped.
#[test]
def test_to_list_clamps_to_recorded_length : IO Bool := do {
    let b <- ByteBuf.of_list three_bytes;
    let xs <- ByteBuf.to_list b 99;
    return (bytes_eq xs three_bytes)
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
// ─── The text bridge: `of_string` / `to_string` ───

/// `"hé"`'s bytes: `h`, then `é` as its two UTF-8 bytes.
def he_bytes : List U8 := [104u8, 195u8, 169u8]

#[test]
def test_of_string_round_trips_through_to_string : IO Bool := do {
    let b <- ByteBuf.of_string "hello, world";
    let s <- ByteBuf.to_string b 12;
    let _ <- ByteBuf.free b;
    return (String.beq s "hello, world")
}

/// The length is BYTES, not characters, and the bytes are the UTF-8
/// encoding -- what a stream write of the string puts on the wire.
#[test]
def test_of_string_holds_the_utf8_bytes : IO Bool := do {
    let b <- ByteBuf.of_string "hé";
    let xs <- ByteBuf.to_list b 3;
    let n := ByteBuf.length b;
    let _ <- ByteBuf.free b;
    return (I64.beq n 3 && bytes_eq xs he_bytes)
}

#[test]
def test_to_string_of_utf8_bytes_is_the_text : IO Bool := do {
    let b <- ByteBuf.of_list he_bytes;
    let s <- ByteBuf.to_string b 3;
    let _ <- ByteBuf.free b;
    return (String.beq s "hé")
}

/// `len` past the recorded length clamps, exactly as `to_list`'s does.
#[test]
def test_to_string_clamps_len_to_the_buffer : IO Bool := do {
    let b <- ByteBuf.of_string "abc";
    let s <- ByteBuf.to_string b 100;
    let _ <- ByteBuf.free b;
    return (String.beq s "abc")
}

#[test]
def test_to_string_takes_only_len_bytes : IO Bool := do {
    let b <- ByteBuf.of_string "abcdef";
    let s <- ByteBuf.to_string b 2;
    let _ <- ByteBuf.free b;
    return (String.beq s "ab")
}

#[test]
def test_of_string_empty_is_a_zero_length_buffer : IO Bool := do {
    let b <- ByteBuf.of_string "";
    let s <- ByteBuf.to_string b 0;
    let n := ByteBuf.length b;
    let _ <- ByteBuf.free b;
    return (I64.beq n 0 && String.beq s "")
}

/// `truncate` keeps the first `n` bytes: both `length` and an over-long
/// `to_list` see only them -- what `Tls.read` relies on to hand back
/// exactly `SSL_read`'s count.
#[test]
def test_truncate_shrinks_length_and_contents : IO Bool := do {
    let b <- ByteBuf.of_list three_bytes;
    let _ <- ByteBuf.truncate b 2;
    let xs <- ByteBuf.to_list b 3;
    let len : I64 := ByteBuf.length b;
    let _ <- ByteBuf.free b;
    return (I64.beq len 2 && bytes_eq xs first_two)
}

/// An `n` past the length never grows the buffer; a negative one empties it.
#[test]
def test_truncate_clamps : IO Bool := do {
    let b <- ByteBuf.of_list three_bytes;
    let _ <- ByteBuf.truncate b 10;
    let grown : I64 := ByteBuf.length b;
    let _ <- ByteBuf.truncate b (0 - 1);
    let emptied : I64 := ByteBuf.length b;
    let _ <- ByteBuf.free b;
    return (I64.beq grown 3 && I64.beq emptied 0)
}

/// `copy_into` gathers two buffers into one at their running offsets --
/// `IO.read_file`'s chunk join.
#[test]
def test_copy_into_gathers_buffers : IO Bool := do {
    let a <- ByteBuf.of_list first_two;
    let b <- ByteBuf.of_list three_bytes;
    let dst <- ByteBuf.alloc 5;
    let _ <- ByteBuf.copy_into dst 0 a;
    let _ <- ByteBuf.copy_into dst 2 b;
    let xs <- ByteBuf.to_list dst 5;
    let _ <- ByteBuf.free a;
    let _ <- ByteBuf.free b;
    let _ <- ByteBuf.free dst;
    return (bytes_eq xs [1u8, 2u8, 1u8, 2u8, 3u8])
}

/// A copy that would run past `dst` is clamped, and an out-of-range
/// offset copies nothing; `dst` never grows.
#[test]
def test_copy_into_clamps : IO Bool := do {
    let src <- ByteBuf.of_list three_bytes;
    let dst <- ByteBuf.alloc 4;
    let _ <- ByteBuf.copy_into dst 2 src;
    let _ <- ByteBuf.copy_into dst 9 src;
    let _ <- ByteBuf.copy_into dst (0 - 1) src;
    let xs <- ByteBuf.to_list dst 9;
    let len : I64 := ByteBuf.length dst;
    let _ <- ByteBuf.free src;
    let _ <- ByteBuf.free dst;
    return (I64.beq len 4 && bytes_eq xs [0u8, 0u8, 1u8, 2u8])
}
