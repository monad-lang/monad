/// Regression tests for the String phi-merge type-mismatch fix
/// (`plans/implementations/2026-08-28-string-value-representation-
/// unification.md`) and the adjacent `String.length` native-wiring gap
/// found while chasing it.
///
/// Before the fix, `Literal.str` (`lang/codegen/emit.mo`) compiled a
/// string literal to a raw `LLVMValue.global_` (`ptr i8_`), while every
/// COMPUTED String (`String.concat`, a boxed field, ...) is `i64`-typed.
/// A literal and a computed string meeting at the same `phi` (an `if`
/// or `match` branch merge) produced a `phi` whose declared type matched
/// one branch but whose OTHER incoming operand kept the mismatched type
/// -- `llc: global variable reference must have pointer type`. Fixed by
/// normalizing a literal's value to `i64` (via a new `ptrtoint`
/// `LLVMValue`/`LLVMInstruction`) at its own construction site. Ordinary
/// CALLS (not `phi`) already tolerate a literal-vs-computed type
/// mismatch via `llc`'s own lenient callee-pointer-bitcast handling
/// (confirmed via direct inspection of real generated IR) -- `phi` is
/// the one construct with zero tolerance for it, so that's the only site
/// that needed a real fix.
///
/// These tests write real `.mo` source to disk and drive it through the
/// SAME pipeline `lang/main.mo`'s own `compile_file_codegen` uses,
/// following `test_closure_capture_e2e.mo`'s `compile_source_run_expect`
/// convention (reused verbatim below) -- real parsing/typechecking/
/// desugaring needs to run to reach the actual bug shape.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The exact minimal repro from the plan doc: a recursive `if` whose
/// `then` branch computes a String (`String.concat`) and whose `else`
/// branch is a bare literal (`""`). Before the fix, `llc` rejected this
/// outright. Verified via `String.length` of the merged result (3
/// recursive concats of a 1-char separator => length 3) rather than
/// `String.beq` -- `if String.beq a b then ...` hits a separate,
/// PRE-EXISTING, unrelated segfault (confirmed via a baseline check
/// against this repo's unmodified HEAD: `String.beq` was never a
/// recognized native comparison for `ensure_i1_cond`'s "is this
/// condition already a genuine i1" fast path, so it falls through to
/// unboxing a boxed Bool that isn't shaped the way that path expects --
/// out of scope here, not introduced by this fix).
#[test]
def test_string_literal_if_phi_merge : IO Bool :=
    let source := r#"use io {IO}
def spaces (n : I64) : String :=
    if I64.gt n 0
    then String.concat " " (spaces (n - 1))
    else ""
def main (args : List String) : IO I64 :=
    IO.io (String.length (spaces 3))
"# in
    compile_source_run_expect source "test_string_literal_if_phi_merge" 3

/// A literal used directly as a whole `if` branch (no recursion, no
/// `String.concat` on that side) merged against a DIFFERENT literal on
/// the other side -- both branches are `global_`-shaped, so this shape
/// already worked before the fix (both sides end up the SAME type); kept
/// as a baseline so a future regression can't silently reintroduce a
/// literal-vs-literal phi failure while only guarding the mixed case
/// above.
#[test]
def test_string_literal_both_branches_phi_merge : IO Bool :=
    let source := r#"use io {IO}
def pick (b : Bool) : String := if b then "yes" else "no"
def main (args : List String) : IO I64 :=
    IO.io (String.length (pick true))
"# in
    compile_source_run_expect source "test_string_literal_both_branches_phi_merge" 3

/// `String.length` (std/string.mo) had no entry in `native_runtime_fn_
/// name` (`lang/codegen/emit.mo`) -- same "confirmed as a real gap"
/// shape as `string_concat`'s own doc comment there: a `#[native
/// string_length]` def with no real body silently compiled to the
/// generic "return Unit" stub, discarding its argument entirely and
/// returning a bogus heap address instead of a length. Found via a
/// direct repro (`String.length "abc"` printed a garbage number instead
/// of 3) while building out this file's other tests.
#[test]
def test_string_length_native_wiring : IO Bool :=
    let source := r#"use io {IO}
def main (args : List String) : IO I64 :=
    IO.io (String.length "abc")
"# in
    compile_source_run_expect source "test_string_length_native_wiring" 3
