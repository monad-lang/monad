/// Standard library: `ByteBuf` -- a flat byte buffer the C FFI can
/// address (`SSL_read`/`SSL_write` in motes/tls take a `void*` plus a
/// length; nothing else in `std/` exposes one).
///
/// A `ByteBuf` records its length: `length` is the byte count it was
/// created with, and `to_list`'s `len` is clamped to that, so an
/// over-large `len` cannot read past the allocation. Give `to_list`
/// `SSL_read`'s return to read only what actually came back. Values are
/// opaque like `Socket` (std/io.mo): never pattern-match, compare or
/// print one.
///
/// Compiled, a `ByteBuf` is the heap kind `plans/bootstrapping/
/// mlir-codegen.md`'s `Buf E` generalises ("a fourth heap kind"): a
/// block carrying its element kind (u8), its length, and a
/// 64-byte-aligned atomic payload. `ByteBuf` is that kind's u8 case, so
/// the buffer an FFI function sees is already the memory a kernel
/// `memref` would. `free` is a deliberate no-op there -- Boehm reclaims a
/// forgotten buffer, and a real free on a word another live value holds
/// would be a use-after-free.
///
/// The two backends hold different words and values never cross between
/// them. Interpreted, it is a registry id (the `Fiber`/`Scope` handle
/// convention, core_native.rs) whose length is its `Vec`'s, and `free`
/// really drops it. `ptr` hands out the raw address and so exists only
/// compiled -- under the interpreter forcing it fails `unknown native:
/// bytebuf_ptr`.

pub type ByteBuf {
  bytebuf
}

/// Allocate `n` zeroed bytes.
#[native "bytebuf_alloc"]
pub def ByteBuf.alloc (n : I64) : IO ByteBuf

/// The raw address of the payload, for FFI functions that write into or
/// read out of it. Compiled backend only (see the module doc).
#[native "bytebuf_ptr"]
pub def ByteBuf.ptr (b : ByteBuf) : Ptr

/// How many bytes the buffer was created with.
#[native "bytebuf_len"]
pub def ByteBuf.length (b : ByteBuf) : I64

/// Copy `xs` into a fresh buffer.
#[native "bytebuf_of_list"]
pub def ByteBuf.of_list (xs : List U8) : IO ByteBuf

/// The first `len` bytes of the buffer as a list, clamped to the buffer's
/// own length.
#[native "bytebuf_to_list"]
pub def ByteBuf.to_list (b : ByteBuf) (len : I64) : IO (List U8)

/// Release the buffer (a no-op under the compiled GC backend).
#[native "bytebuf_free"]
pub def ByteBuf.free (b : ByteBuf) : IO Unit

/// The first `len` bytes of the buffer as a `String`, clamped to the
/// buffer's own length exactly as `to_list` is -- one copy, where
/// `String.from_list (ByteBuf.to_list ...)` would build and walk a cons
/// cell per byte. Bytes that are not valid UTF-8 come back lossily
/// (U+FFFD) under the interpreter, whose `String` must be UTF-8; the
/// compiled backend copies them verbatim.
pub def ByteBuf.to_string (b : ByteBuf) (len : I64) : IO String :=
  IO.mk (bytebuf_to_string b len)

/// Copy `s`'s bytes into a fresh buffer -- `of_list`'s shape, from text.
pub def ByteBuf.of_string (s : String) : IO ByteBuf :=
  IO.mk (bytebuf_of_string s)

#[native "bytebuf_to_string"]
priv def bytebuf_to_string (b : ByteBuf) (len : I64) : RawIO String

#[native "bytebuf_of_string"]
priv def bytebuf_of_string (s : String) : RawIO ByteBuf
