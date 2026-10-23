/// Regression test for the `RawIO` box on a GENERIC extern
/// (`return_is_raw_io`, `lang/codegen/emit.mo`).
///
/// Every `#[extern "c"]` def declared `RawIO A` gets exactly one
/// `monad_io_pure` box in its generated wrapper, so it composes with
/// `IO.mk` like a `RawIO` native. The check used to step past only EXPLICIT
/// binders; on an implicit type parameter (`{A : Type}`) it read the whole
/// quantifier, whose head is `pi`, not `RawIO` -- so the wrapper returned the
/// raw word unboxed and `Monad_IO_bind` then read field 0 of that word as if
/// it were a constructor.
///
/// Found while wiring `web_wasm.Keep`, whose whole point is an extern over
/// an implicit type parameter (a `Ref A` through an opaque slot); there the
/// unboxed word surfaced as a silent `0`, not a crash.
///
/// The fixture extern binds libc's `strlen` with an implicit `A` inferred
/// from its argument, which is the exact shape that was broken.
use lang::codegen::test::e2e_harness {compile_source_run_expect}

#[test]
def test_generic_rawio_extern_is_boxed : IO Bool :=
    let source := r#"#[extern "c" {link_name := "strlen"}]
def generic_strlen {A : Type} (s : A) : RawIO I64

def main (args : List String) : IO I64 := do {
    let n <- IO.mk (generic_strlen "abcd");
    return n
}
"# in
    compile_source_run_expect source "test_generic_rawio_extern_is_boxed" 4
