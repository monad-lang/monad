/// Standard library: `ByteBuf` -- a flat byte buffer the C FFI can
/// address (`SSL_read`/`SSL_write` in motes/tls take a `void*` plus a
/// length; nothing else in `std/` exposes one).
///
/// A `ByteBuf` records its length: `length` is the byte count it was
/// created with (or later `truncate`d to), and `to_list`'s `len` is
/// clamped to that, so an over-large `len` cannot read past the
/// allocation. `truncate` a buffer to `SSL_read`'s return to keep only
/// what actually came back. Values are opaque like `FdStream`
/// (std/stream.mo): never pattern-match, compare or print one.
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

#[native "bytebuf_alloc"]
priv def bytebuf_alloc_raw (n : I64) : RawIO ByteBuf

/// Allocate `n` zeroed bytes.
pub def ByteBuf.alloc (n : I64) : IO ByteBuf := IO.mk (bytebuf_alloc_raw n)

/// The raw address of the payload, for FFI functions that write into or
/// read out of it. Compiled backend only (see the module doc).
#[native "bytebuf_ptr"]
pub def ByteBuf.ptr (b : ByteBuf) : Ptr

/// Read the pointer-sized word at the start of the buffer, for a C
/// function that returns a handle through an out-parameter. The buffer
/// must hold at least 8 bytes; a shorter one yields the NULL word instead
/// of reading past its payload. Compiled backend only, like `ptr`: the
/// interpreter has no raw addresses.
///
/// This is the typed alternative to a general `load(ptr)` helper. The
/// argument is a `ByteBuf`, so no arbitrary address can be supplied, and
/// the runtime checks the buffer's kind and length.
#[native "bytebuf_take_ptr"]
pub def ByteBuf.take_ptr (b : ByteBuf) : Ptr

/// How many bytes the buffer holds: its creation size, or what
/// `truncate` cut it to.
#[native "bytebuf_len"]
pub def ByteBuf.length (b : ByteBuf) : I64

#[native "bytebuf_of_list"]
priv def bytebuf_of_list_raw (xs : List U8) : RawIO ByteBuf

/// Copy `xs` into a fresh buffer.
pub def ByteBuf.of_list (xs : List U8) : IO ByteBuf :=
  IO.mk (bytebuf_of_list_raw xs)

#[native "bytebuf_to_list"]
priv def bytebuf_to_list_raw (b : ByteBuf) (len : I64) : RawIO (List U8)

/// The first `len` bytes of the buffer as a list, clamped to the buffer's
/// own length.
pub def ByteBuf.to_list (b : ByteBuf) (len : I64) : IO (List U8) :=
  IO.mk (bytebuf_to_list_raw b len)

#[native "bytebuf_free"]
priv def bytebuf_free_raw (b : ByteBuf) : RawIO Unit

/// Release the buffer (a no-op under the compiled GC backend).
pub def ByteBuf.free (b : ByteBuf) : IO Unit := IO.mk (bytebuf_free_raw b)

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

/// Shrink the recorded length to `n`, keeping the first `n` bytes; `n`
/// is clamped to `[0, length]`, so this never grows a buffer. The
/// allocation itself is unchanged -- the bytes past `n` just stop
/// being part of it.
pub def ByteBuf.truncate (b : ByteBuf) (n : I64) : IO Unit :=
  IO.mk (bytebuf_truncate b n)

/// Copy all of `src` into `dst` starting at byte `offset` -- one memmove.
/// Clamped to `dst`'s length, so this never grows `dst`; an offset
/// outside `[0, length dst]` copies nothing. Gathering chunks into one
/// buffer this way is how `IO.read_file` decodes a file ONCE rather than
/// chunk by chunk (a character split across two chunks would otherwise
/// decode as U+FFFD under the interpreter).
pub def ByteBuf.copy_into (dst : ByteBuf) (offset : I64) (src : ByteBuf) : IO Unit :=
  IO.mk (bytebuf_copy_into dst offset src)

#[native "bytebuf_to_string"]
priv def bytebuf_to_string (b : ByteBuf) (len : I64) : RawIO String

#[native "bytebuf_of_string"]
priv def bytebuf_of_string (s : String) : RawIO ByteBuf

#[native "bytebuf_truncate"]
priv def bytebuf_truncate (b : ByteBuf) (n : I64) : RawIO Unit

#[native "bytebuf_copy_into"]
priv def bytebuf_copy_into (dst : ByteBuf) (offset : I64) (src : ByteBuf) : RawIO Unit
