// ffi_example / bytebuf_ffi_test — `ByteBuf.ptr` driven through real
// libc calls, the offline half of the buffer's contract that nothing
// else in the corpus exercises: `motes/tls`'s SSL_read/SSL_write prove
// the FFI can address a buffer, but only inside the env-gated network
// suite (MONAD_TLS_NETWORK_TESTS), so an ordinary sweep run never
// touches the pointer path at all. memset writes through the address,
// strlen reads it, memcpy crosses two of them — all against
// `std/src/bytebuf.mo`'s own natives, no fixture source.
//
// Like ffi_link_test.mo this file needs the self-hosted binary: the
// interpreter has no C bridge and no `bytebuf_ptr` arm, so under
// `cargo run -- test` every test here reports `unknown native` and the
// file FAILs — the compiled sweep is the gate that runs it.
//
// Shape rules inherited from std/src/bytebuf_tests.mo: list literals
// live in top-level defs (a FromListLiteral call inside a do-block
// desyncs the lowering), and byte equality is a hand-rolled `U8.beq`
// walk, never a `BEq` dispatch.

use lib::libc {memcpy, memset, strlen_ptr}
use std::bytebuf {ByteBuf.alloc, ByteBuf.free, ByteBuf.length, ByteBuf.of_list, ByteBuf.ptr, ByteBuf.to_list}

def memset_filled : List U8 := [65u8, 65u8, 65u8, 65u8]

/// The interior-zero pattern from std/src/bytebuf_tests.mo — the case
/// that separates a byte buffer from a C string, copied between two
/// buffers through the FFI below.
def interior_zero : List U8 := [65u8, 0u8, 66u8, 0u8, 67u8]

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

/// memset WRITES through `ByteBuf.ptr` — C at the far end of the
/// address, `ByteBuf.to_list` reading it back. The recorded length is
/// asserted here too, since `ptr` now hands out the payload of the very
/// object that carries it.
#[test]
def test_memset_writes_through_ptr : IO Bool := do {
    let buf <- ByteBuf.alloc 4;
    let _ := memset (ByteBuf.ptr buf) (I64.to_i32 65) 4u64;
    let xs <- ByteBuf.to_list buf 4;
    let n := ByteBuf.length buf;
    ByteBuf.free buf;
    return (bytes_eq xs memset_filled && I64.beq n 4)
}

/// strlen READS through `ByteBuf.ptr` — the buffer's last byte is
/// alloc's zero-fill, so C sees a NUL-terminated string of exactly the
/// three bytes memset wrote.
#[test]
def test_strlen_reads_through_ptr : IO Bool := do {
    let buf <- ByteBuf.alloc 4;
    let _ := memset (ByteBuf.ptr buf) (I64.to_i32 66) 3u64;
    let n := strlen_ptr (ByteBuf.ptr buf);
    ByteBuf.free buf;
    return (I64.beq n 3)
}

/// memcpy crosses TWO `Ptr` params buffer-to-buffer, and an interior
/// 0u8 survives the round trip byte-exactly — the property TLS records
/// depend on, which a C-string-shaped copy would corrupt.
#[test]
def test_memcpy_interior_zero_between_bufs : IO Bool := do {
    let src <- ByteBuf.of_list interior_zero;
    let dst <- ByteBuf.alloc 5;
    let _ := memcpy (ByteBuf.ptr dst) (ByteBuf.ptr src) 5u64;
    let xs <- ByteBuf.to_list dst 5;
    ByteBuf.free src;
    ByteBuf.free dst;
    return (bytes_eq xs interior_zero)
}