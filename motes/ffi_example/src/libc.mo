// ffi-example / libc — Phase 2 of `plans/implementations/c-rust-ffi.md`.
//
// Declarative bindings for a handful of libc / libm symbols. Each def is
// attributed `#[extern "c" ...]` (NOT `@[...]` — the syntax used by
// the rest of Monad, e.g. `#[native "..."]` and `#[test]`); the
// SELF-HOSTED compiler binds any C symbol by name at LINK time
// (`link_name` picks the symbol, and no compiler edit is needed for a
// new one) — there is no eval-path FFI to register a symbol with.
//
// The Rust host has no C bridge and warns (`extern_attr_warnings`) that
// it is ignoring these.
//
// Note what is NOT here: no `lib := "m"` for `sin`. A declaration names
// the symbol to bind and, with `link_name`, which symbol that is --
// which LIBRARY it lives in is a build fact about this mote, declared
// once in `mote.toml` as `[link] libs = ["m"]`.

#[extern "c"]
def puts (s : String) : I32

#[extern "c" {link_name := "strlen"}]
def strlen (s : String) : I64

// Here for `ffi_link_test.mo`, and for what it is the only way to say: a
// NEGATIVE `I32` from C, so the sign of a narrow return is observable at
// run time (`abs` of it, and `I32.to_string` of it). `puts` returns an
// `I32` too, but only a non-negative one; `I32.beq` was of no help when
// this comment was written -- `i32_eq` was unwired on the self-hosted
// side -- but it is now (runtime/src/natives.mo), and the corpus still
// has no `I32` literal to compare against, so `to_string` remains the
// observable.
#[extern "c"]
def atoi (s : String) : I32

#[extern "c"]
def abs (x : I32) : I32

// `memset`/`memcpy`/`strlen_ptr` take a `Ptr` — a raw address the
// self-hosted `ByteBuf.ptr` hands out (`bytebuf_ffi_test.mo` is the
// proof). The `size_t` counts come through as `U64`, the fallback
// `bitcast i64` param path `SSL_ctrl_host`'s `larg` already took.
#[extern "c"]
def memset (s : Ptr) (c : I32) (n : U64) : Ptr

#[extern "c"]
def memcpy (dest : Ptr) (src : Ptr) (n : U64) : Ptr

#[extern "c" {link_name := "strlen"}]
def strlen_ptr (s : Ptr) : I64

#[extern "c"]
def sin (x : F64) : F64