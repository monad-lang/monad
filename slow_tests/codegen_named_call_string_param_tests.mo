/// Regression test for the named-call spread that a String-typed
/// parameter silently stole (the rung-3 blocker: v29 could `check`
/// itself but `monad compile` returned 1 without reaching codegen).
///
/// `callee { param := value, ... }` is named-call sugar: the literal's
/// field names are the CALLEE's own parameter names, spread across its
/// curried application. `type_check_app` only tried that spread in its
/// argument-check ERROR branch, and `try_type_check_def_call`'s own
/// fast path committed even earlier -- both on the assumption that an
/// unannotated struct literal fails to check against an ordinary
/// parameter type. It doesn't: `type_check_struct_lit` takes the
/// expected type's FIRST constructor and walks the CONSTRUCTOR's
/// params, producing `Option.none` for each one the literal doesn't
/// mention and ignoring every literal field the constructor doesn't
/// declare -- so a literal whose fields don't overlap AT ALL still
/// "checks" fine, vacuously.
///
/// A `String` parameter is exactly that trap: `String` is an inductive
/// whose first constructor is `of_bytes (List U8)` (init/prelude.mo),
/// so `{ file_path := ..., ... }` resolved to an EMPTY
/// `String.of_bytes` -- `alloc_constructor(18, 0)` -- passed as ONE
/// argument to a partial-application shim of the real arity. The
/// callee never ran. Confirmed in the self-compiled v29's own IR at
/// three sites (`compile_file_codegen`, `run_test_loop_codegen`),
/// which is why `monad compile` exited 1 silently.
///
/// Both paths now consult `struct_literal_arg_matches_expected`
/// (`lang/typecheck/infer.mo`, mirroring the reference compiler's
/// function of the same name): a literal whose fields aren't all
/// declared by the expected type's own constructor doesn't count as a
/// successful ordinary check, so the named-call spread gets its turn.
///
/// These compile through the self-hosted backend and RUN the binary, so
/// a regression reproduces as the real miscompile (the callee's body
/// never executing) rather than an IR-shape mismatch.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The exact failing shape: first parameter typed `String`. Pre-fix the
/// callee never ran and the program exited 1; the fix makes it a real
/// saturated call returning 7.
#[test]
def test_named_call_string_first_param : IO Bool :=
    let source := r#"use io {IO}
open IO {println}
def getv (file_path : String) (b : I64) : IO I64 := do {
    println file_path;
    return b
}
def main (args : List String) : IO I64 := do {
    let r <- getv { file_path := "hello", b := 7 };
    return r
}
"# in
    compile_source_run_expect source "test_named_call_string_first_param" 7

/// The general form of the same trap: the callee's first parameter is
/// any USER struct type whose own fields don't overlap the literal's
/// (`Inner { q, z }` vs the call's `inner`/`m`). `String` is just the
/// case the compiler itself hit -- every registered inductive is a
/// trap, since `type_check_struct_lit` never compares field names at
/// all. Pre-fix this compiled to an empty `Inner` and exited 1 without
/// running the callee.
#[test]
def test_named_call_struct_first_param : IO Bool :=
    let source := r#"use io {IO}
struct Inner {
    q : I64,
    z : I64,
}
def getv (inner : Inner) (m : I64) : IO I64 := do {
    return (I64.add inner.q m)
}
def main (args : List String) : IO I64 := do {
    let i : Inner := { q := 2, z := 0 };
    let r <- getv { inner := i, m := 5 };
    return r
}
"# in
    compile_source_run_expect source "test_named_call_struct_first_param" 7

/// Non-String params must keep working exactly as before -- their
/// expected type isn't a registered inductive, so the literal's own
/// check genuinely fails and the spread always fired. Pins that the
/// guard didn't change the path that already worked.
#[test]
def test_named_call_plain_params_unchanged : IO Bool :=
    let source := r#"use io {IO}
def add3 (a : I64) (b : I64) (c : I64) : I64 := I64.add (I64.add a b) c
def main (args : List String) : IO I64 := do {
    let r : I64 := add3 { a := 1, b := 2, c := 3 };
    return r
}
"# in
    compile_source_run_expect source "test_named_call_plain_params_unchanged" 6
