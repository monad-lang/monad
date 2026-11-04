/// Regression tests for the closure free-variable-capture fix
/// (`plans/implementations/2026-08-28-codegen-closure-free-var-capture.md`).
///
/// `compile_db_lam_ir` (`lang/codegen/emit.mo`) lifts a nested `Term.lam`
/// (every do-notation continuation is exactly this shape -- `let x <- e1;
/// e2` desugars to `Monad.bind e1 (\x -> e2)`, `lang/types.mo`'s
/// `desugar_do_inner`) into a brand-new, independent top-level LLVM
/// function. Before this fix, `alloc_closure` was always called with an
/// EMPTY capture list, so any reference inside the lifted body to a name
/// bound in the ENCLOSING function (e.g. an earlier do-statement's own
/// bound name) silently resolved to a register that belongs to the outer
/// function and doesn't exist inside the lifted one -- `llc: use of
/// undefined value`.
///
/// These tests write real `.mo` source to disk and drive it through the
/// SAME pipeline `cli/src/main.mo`'s own `compile_file_codegen` uses
/// (`load_file_modules` -> `compile_loaded_modules_to_ir` -> `emit_module`
/// -> `llc`/`clang`), rather than hand-building a `Term`/`Def` AST --
/// do-notation desugaring, dictionary-passing promotion, and typeclass
/// call resolution all need to run for real to reach the actual bug (a
/// hand-built AST would have to fake all of that, and would risk testing
/// a shape that doesn't match what the parser/desugarer actually produce).
///
/// A plain `let x := 5 in ...` does NOT reach `compile_db_lam_ir` at all
/// -- `try_compile_let_beta_db` beta-reduces it to a literal/direct
/// binding in the SAME function, so it would falsely "pass" even against
/// the pre-fix buggy code. Only a genuine monadic bind (`let x <- e1; e2`,
/// or an escaping first-class lambda) forces real lambda-lifting, which is
/// why every test below uses `<-`, not `:=`.
open IO {println}
use lib::codegen::test::e2e_harness {compile_source_run_expect}

/// Primary regression test: `b`'s own bind-continuation transitively
/// captures `a` from the enclosing lifted lambda. Uses `I64.add`
/// directly (not `+`) to isolate the closure-capture fix from an
/// unrelated, pre-existing `HAdd`/typeclass-dispatch gap for the plain
/// operator form. Expect 5 + 10 = 15.
#[test]
def test_bind_capture : IO Bool :=
    let source :=
        "def main (args : List String) : IO I64 := do {\n" ++
        "    let a <- IO.pure 5;\n" ++
        "    let b <- IO.pure 10;\n" ++
        "    return (I64.add a b)\n" ++
        "}\n"
    in
    compile_source_run_expect source "test_bind_capture" 15

/// 3-level nesting: transitive capture must compose across more than
/// one level (`c`'s continuation captures both `a` and `b`, each
/// itself captured one level down from where it was originally bound).
/// Expect 1 + 2 + 3 = 6.
#[test]
def test_bind_capture_3level : IO Bool :=
    let source :=
        "def main (args : List String) : IO I64 := do {\n" ++
        "    let a <- IO.pure 1;\n" ++
        "    let b <- IO.pure 2;\n" ++
        "    let c <- IO.pure 3;\n" ++
        "    return (I64.add (I64.add a b) c)\n" ++
        "}\n"
    in
    compile_source_run_expect source "test_bind_capture_3level" 6

/// Sibling-lambda regression test: a plain `let n := 5` (beta-reduced
/// inline, NOT lifted) followed by a NESTED do-block (`if verbose then
/// do { println ... } else return unit`, itself producing its own
/// lifted lambda for its trailing `pure hole` continuation) followed by
/// a SECOND, later statement that references `n` (also lifted, as
/// every do-notation continuation is). `compile_db_lam_ir` resets its
/// own ctx's `locals` to compile a lifted function's body in isolation
/// (`ctx_reset_locals`) -- but was returning that RESET ctx straight
/// back to its caller instead of restoring the caller's own original
/// locals (`ctx_restore_locals`), so `n`'s binding was silently lost
/// from the enclosing function's own ctx the moment the FIRST nested
/// lambda (the `if`'s own do-block) finished compiling -- the SECOND
/// lambda (`return n`) then couldn't find `n` as a local at all (not
/// merely failing to capture it -- `n` resolved as an unknown GLOBAL
/// name and silently miscompiled into a bogus 0-arg call,
/// `llc: use of undefined value '@n'`). This exact shape --
/// `compile_loaded_modules_to_ir`'s own `if verbose then do {...}
/// else return unit;` pattern, repeated across several successive
/// stages -- is what blocked `bootstrap compile cli/src/main.mo monad`'s
/// own self-compile. Expect 5 (verbose=false, so `n` survives
/// untouched through the discarded `if`/`else` branch).
#[test]
def test_sibling_lambda_preserves_outer_locals : IO Bool :=
    let source :=
        "open IO {println}\n" ++
        "def helper (verbose : Bool) : IO I64 := do {\n" ++
        "    let n := 5;\n" ++
        "    if verbose then do {\n" ++
        "        println \"hi\"\n" ++
        "    } else return unit;\n" ++
        "    return n\n" ++
        "}\n" ++
        "def main (args : List String) : IO I64 := helper false\n"
    in
    compile_source_run_expect source "test_sibling_lambda_preserves_outer_locals" 5

/// A nested constrained call as an ARGUMENT whose parameter type is still
/// abstract (`m : M A`) must still receive its dictionary: the outer
/// call's return direction (`IO I64`) has to seed the substitution BEFORE
/// the argument is checked. Without it, `inner 41` is checked against the
/// abstract `M A`, cannot resolve `[Monad M]`, and compiles to a partial
/// application waiting for a dictionary (the `HtmlT.map` driver SIGSEGV
/// in oak's `html_t_tests`).
#[test]
def test_nested_constrained_arg_carries_the_expectation : IO Bool :=
    let source :=
        "def outer [Monad M] {A B : Type} (f : A -> B) (m : M A) : M B :=\n" ++
        "    Monad.bind m (fn (a : A) => Monad.pure (f a))\n" ++
        "def inner [Monad M] {A : Type} (a : A) : M A := Monad.pure a\n" ++
        "def run : IO I64 := outer (fn (n : I64) => n) (inner 41)\n" ++
        "def main (args : List String) : IO I64 := run\n"
    in
    compile_source_run_expect source "test_nested_constrained_arg_carries_the_expectation" 41

/// A dictionary-capturing closure stored in a CONSTRUCTOR (the
/// `dict-capturing-closure-segfault` reproduction): `holder_pure`'s
/// leading `[Monad M]` dictionary becomes a `__dict_Monad` parameter, and
/// the lambda it stores captures it. The compiled backends used to
/// resolve that dictionary to the prelude's catch-all bridge
/// (`Monad (M I I)`) and crash applying its mismatched layout (native
/// SIGSEGV, web trap); the lambda's env was always correct.
/// `holder_pure 42` ignores its `x` argument and returns 42, so the exit
/// code is the verdict.
#[test]
def test_dict_capture_in_constructor : IO Bool :=
    let source :=
        "type Holder (M : Type -> Type) A {\n" ++
        "    holder (f : A -> M A)\n" ++
        "}\n" ++
        "def holder_pure [Monad M] {A : Type} (a : A) : Holder M A :=\n" ++
        "    Holder.holder (fn (x : A) => Monad.pure a)\n" ++
        "def holder_run [Monad M] {A : Type} (h : Holder M A) (a : A) : M A :=\n" ++
        "    match h { Holder.holder f => f a }\n" ++
        "def main (args : List String) : IO I64 := do {\n" ++
        "    let h : Holder IO I64 := holder_pure 42;\n" ++
        "    holder_run h 1\n" ++
        "}\n"
    in
    compile_source_run_expect source "test_dict_capture_in_constructor" 42

/// Shim-path regression test: a top-level (arity>0) def referenced as a
/// first-class VALUE -- passed to another function and applied
/// indirectly via `apply_closureN` -- must still work once
/// `apply_closureN` uniformly expects every boxed entry to accept a
/// leading `self` param. `add_one`'s own DIRECT-call signature (unused
/// in this program, but exercised implicitly by every other top-level
/// def in the whole corpus) must stay untouched, so this only passes if
/// `build_closure_shim_func`'s forwarding shim (not `add_one`'s own
/// entry point) is what actually gets boxed and invoked here.
/// Deliberately avoids `List`/`Option`/`+` machinery (all of which hit
/// unrelated, pre-existing gaps -- `List.cons`'s own constructor
/// wrapper isn't reachable via this minimal-corpus compile path, and
/// `+`'s `HAdd` dispatch has a separate gap) by hand-writing a tiny
/// `apply_fn`/`add_one` pair: `apply_fn add_one 8` must produce 9.
#[test]
def test_shim_boxed_def_as_value : IO Bool :=
    let source :=
        "def add_one (x : I64) : I64 := I64.add x 1\n" ++
        "def apply_fn (f : I64 -> I64) (x : I64) : I64 := f x\n" ++
        "def main (args : List String) : IO I64 :=\n" ++
        "    IO.pure (apply_fn add_one 8)\n"
    in
    compile_source_run_expect source "test_shim_boxed_def_as_value" 9
