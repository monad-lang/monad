// std / cstring -- copy foreign-owned text and byte runs into Monad values.
//
// A C library returns `char*`/`void*` pointing into memory IT owns
// (SQLite's `errmsg`/`column_text`, an OpenSSL name, ...). Declaring such a
// function as returning Monad `String` would alias that memory -- a
// compiled `String` is a raw `char*` -- so the caller copies through a
// `ByteBuf` first. This module owns that copy so drivers do not each
// re-declare libc.
//
// Memory-safety contract (AGENTS.md, Memory Safety): the source `p` is a
// pointer that came from a foreign API, `n` is the byte count that SAME
// API reported (`strlen`, `sqlite3_column_bytes`, ...), and the
// destination is a fresh `ByteBuf` of exactly that size. `memcpy` is not
// exposed -- the two externs below are package-private, and the public
// API only ever returns owned Monad values.
//
// Compiled backend only, like `ByteBuf.ptr`: the Rust host ignores
// `#[extern "c"]` and has no raw addresses.

use lib::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.ptr,
    ByteBuf.to_list, ByteBuf.to_string}

// `n` is `I64`, not `size_t`/`U64`: it is a 64-bit register on every
// supported native target and the callers' counts (`strlen`,
// `I32.to_i64`) are I64.
#[extern "c" {link_name := "strlen"}]
def cstring_strlen (s : Ptr) : I64

#[extern "c" {link_name := "memcpy"}]
def cstring_memcpy (dst : Ptr) (src : Ptr) (n : I64) : RawIO Ptr

with CString {
    /// Copy a NUL-terminated C string into a Monad `String`.
    pub def read (p : Ptr) : IO String := do {
        let n := cstring_strlen p;
        CString.read_or_empty p n
    }

    /// Copy exactly `n` bytes (may contain NULs) into a Monad `String`.
    pub def read_n (p : Ptr) (n : I64) : IO String := do {
        let buf <- ByteBuf.alloc n;
        let _ <- IO.mk (cstring_memcpy (ByteBuf.ptr buf) p n);
        let s <- ByteBuf.to_string buf n;
        let _ <- ByteBuf.free buf;
        return s
    }

    /// Copy exactly `n` bytes into a `List U8`; `n` may be zero.
    pub def bytes (p : Ptr) (n : I64) : IO (List U8) := do {
        if n < 1 then return List.empty else CString.bytes_n p n
    }

    def read_or_empty (p : Ptr) (n : I64) : IO String :=
        if n < 1 then IO.pure "" else CString.read_n p n

    def bytes_n (p : Ptr) (n : I64) : IO (List U8) := do {
        let buf <- ByteBuf.alloc n;
        let _ <- IO.mk (cstring_memcpy (ByteBuf.ptr buf) p n);
        let xs <- ByteBuf.to_list buf n;
        let _ <- ByteBuf.free buf;
        return xs
    }
}
