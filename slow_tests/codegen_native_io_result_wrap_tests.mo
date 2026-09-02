/// Regression tests for `needs_io_wrap` (`lang/codegen/emit.mo`):
/// `IO.read_file`/`IO.file_exists`'s raw call result must be wrapped in a
/// real `IO.io`-tagged constructor before it can be used as an `IO` value,
/// same as `IO.println`/`IO.write_file` already were.
///
/// `is_void_native` was previously the ONLY signal deciding whether a
/// native op's result needed this wrap, conflating "the C function is
/// declared `void`" (true for `print_str`/`write_file`) with "the Monad
/// type is `IO _`" (also true for `read_file`/`file_exists`, which return
/// a real `char*`, not void). `read_file`/`file_exists`'s raw call result
/// was used AS-IS wherever an `IO` value was expected -- `Monad_IO_bind`'s
/// own generated body calls `monad_get_field(io_val, 0)` on it, misreading
/// the raw pointer as if it were a tagged constructor object.
///
/// Found while verifying `implementations/2026-08-29-native-io-op-non-
/// exhaustive-match-crash.md`'s own regression test more thoroughly than a
/// bare crash-freedom check: binding a native call's result via `<-` and
/// merely IGNORING it compiled/ran fine (no consumer ever touches the
/// mis-shaped value), but using it in ANY way afterward (a call argument,
/// a comparison) segfaulted or returned a silently wrong value --
/// confirmed pre-existing (unrelated to `write_file`) via `git worktree`
/// bisection, filed as
/// `implementations/2026-08-29-native-bind-result-use-crash.md`, then
/// root-caused and fixed here.
use io {IO}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// Binds `IO.read_file`'s result via `<-` and then ACTUALLY USES it
/// (passed as a real function argument, compared against a literal) --
/// the exact shape that used to segfault (or, for pure-value consumers,
/// silently misbehave) before `read_file`'s result was `IO.io`-wrapped.
#[test]
def test_read_file_bind_result_used_downstream : IO Bool :=
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let path := "/tmp/monad_e2e/io_result_wrap_fixture.txt";
    let content := "needs io wrap";
    IO.write_file_native path content;
    let read_back <- IO.read_file_native path;
    let matched := String.beq read_back content;
    let result := if matched then 1 else 0;
    return result
}
"# in
    compile_source_run_expect source "test_read_file_bind_result_used_downstream" 1

// NOTE: an equivalent `IO.file_exists` test was attempted here (same
// shape, `Bool`-producing instead of `String`-producing, to exercise
// `needs_io_wrap` for a different inner type) but found a SEPARATE,
// pre-existing, deeper bug: `monad_file_exists` (`lang/codegen/runtime.c`)
// returns a raw C string literal ("1" or NULL), not a real heap-allocated
// Bool constructor via `alloc_constructor` -- so `if exists then ... else
// ...` (which reads the value's TAG via `monad_get_tag`, expecting a
// genuine boxed Bool object) reads garbage from whatever address that
// static string happens to be at, not a real tag. Confirmed via direct
// repro: `IO.file_exists` on a file that genuinely exists still took the
// `else` branch. Unrelated to `needs_io_wrap`/this fix -- the IO-wrapping
// itself is correct either way, the INNER value it wraps is wrong. Not
// yet filed as its own dated plan; out of scope here.
