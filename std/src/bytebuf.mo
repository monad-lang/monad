/// Standard library: `ByteBuf` -- a flat byte buffer the C FFI can
/// address (`SSL_read`/`SSL_write` in motes/tls take a `void*` plus a
/// length; nothing else in `std/` exposes one).
///
/// A `ByteBuf` records no length: `to_list`'s `len` is the count the
/// CALLER knows (`SSL_read`'s return), and must not exceed what was
/// allocated or written. Values are opaque like `Socket` (std/io.mo):
/// never pattern-match, compare or print one.
///
/// The two backends hold different words and values never cross between
/// them. Compiled, it is the raw pointer to a GC-allocated buffer, so
/// `free` is a deliberate no-op there (Boehm reclaims a forgotten
/// buffer; a real free on a word another live value holds would be a
/// use-after-free). Interpreted, it is a registry id (the `Fiber`/
/// `Scope` handle convention, core_native.rs) and `free` really drops
/// it. `ptr` hands out the raw address and so exists only compiled --
/// under the interpreter forcing it fails `unknown native:
/// bytebuf_ptr`.

type ByteBuf {
  bytebuf
}

/// Allocate `n` zeroed bytes.
#[native "bytebuf_alloc"]
def ByteBuf.alloc (n : I64) : IO ByteBuf

/// The raw address of the buffer, for FFI functions that write into or
/// read out of it. Compiled backend only (see the module doc).
#[native "bytebuf_ptr"]
def ByteBuf.ptr (b : ByteBuf) : Ptr

/// Copy `xs` into a fresh buffer.
#[native "bytebuf_of_list"]
def ByteBuf.of_list (xs : List U8) : IO ByteBuf

/// The first `len` bytes of the buffer as a list.
#[native "bytebuf_to_list"]
def ByteBuf.to_list (b : ByteBuf) (len : I64) : IO (List U8)

/// Release the buffer (a no-op under the compiled GC backend).
#[native "bytebuf_free"]
def ByteBuf.free (b : ByteBuf) : IO Unit