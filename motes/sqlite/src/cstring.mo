// monad-sqlite / cstring -- copy SQLite-owned text and blobs into Monad
// values before the next SQLite call can invalidate them.
//
// `sqlite3_errmsg`, `sqlite3_column_name`, `sqlite3_column_text` and
// `sqlite3_column_blob` return pointers into memory owned by the
// connection/statement. Declaring one of those as a Monad `String` would
// alias that memory (a compiled `String` is a raw `char*`); this module
// copies through a `ByteBuf` instead.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.ptr,
    ByteBuf.to_list, ByteBuf.to_string}
use lib::ffi {sqlite_memcpy, sqlite_strlen}

with CString {
    /// Copy a NUL-terminated C string into a Monad `String`.
    pub def read (p : Ptr) : IO String := do {
        let n := sqlite_strlen p;
        CString.read_or_empty p n
    }

    /// Copy exactly `n` bytes (may contain NULs) into a Monad `String`.
    pub def read_n (p : Ptr) (n : I64) : IO String := do {
        let buf <- ByteBuf.alloc n;
        let _ := sqlite_memcpy (ByteBuf.ptr buf) p n;
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
        let _ := sqlite_memcpy (ByteBuf.ptr buf) p n;
        let xs <- ByteBuf.to_list buf n;
        let _ <- ByteBuf.free buf;
        return xs
    }
}
