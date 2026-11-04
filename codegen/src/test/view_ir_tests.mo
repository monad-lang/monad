/// IR-shape gate for view-types P2's fused do-bind
/// (`try_compile_view_bind_db`, `codegen/src/emit.mo`).
///
/// A `Cell` accessor costs three allocations on the boxed path
/// (`RawIO.io`, `IO.mk`, and the `Pair` the C runtime builds). The
/// fusion lowers the two shapes a real program uses -- a do-bind whose
/// initializer is a Cell accessor, with a continuation that consumes the
/// result immediately -- straight to the native call:
/// `monad_view_payload` for a `get` (the handle rides through unchanged),
/// and the direct native for `new`/`set`/`free`. These tests are the
/// only thing that proves the box is GONE; a runtime test would pass on
/// both paths.
///
/// The escaping-pair test is the control: it must keep the boxed
/// `Cell.get` call, so a matcher that silently stopped matching (or one
/// that matched too much) fails here rather than shipping.
///
/// Every assertion is on `main_monad`'s OWN text, never the whole
/// module: the compiler emits the `view_get_raw` wrapper (and the
/// `Copy I64` dictionary) regardless of reachability, so a module-wide
/// "no monad_view_get" check would be false by construction.
use lib::test::e2e_harness {
  compile_source_ir, compile_source_run_expect, ir_function,
}
use lib::emit {check_contains}
open IO {println}

/// Every Cell operation in the fused shape, in one do-block. `main`'s
/// own exit code is the value read back (42).
def fused_source : String :=
    "use init::view {Cell}\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    let c0 <- Cell.new 41;\n"
    ++ "    let p <- Cell.get c0;\n"
    ++ "    match p {\n"
    ++ "        Pair.pair x c1 => do {\n"
    ++ "            let c2 <- Cell.set c1 (I64.add x 1);\n"
    ++ "            let p2 <- Cell.get c2;\n"
    ++ "            match p2 {\n"
    ++ "                Pair.pair y c3 => do {\n"
    ++ "                    let _ <- Cell.free c3;\n"
    ++ "                    return y\n"
    ++ "                },\n"
    ++ "            }\n"
    ++ "        },\n"
    ++ "    }\n"
    ++ "}\n"

/// The pair ESCAPES to another def, so the do-bind cannot be fused.
def escaping_source : String :=
    "use init::view {Cell}\n"
    ++ "def finish (p : Pair I64 (Cell I64)) : IO I64 :=\n"
    ++ "    match p {\n"
    ++ "        Pair.pair w c => do {\n"
    ++ "            let _ <- Cell.free c;\n"
    ++ "            return w\n"
    ++ "        },\n"
    ++ "    }\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    let c0 <- Cell.new 42;\n"
    ++ "    let p <- Cell.get c0;\n"
    ++ "    finish p\n"
    ++ "}\n"

#[test]
def test_fused_cell_binds_emit_the_native_calls : IO Bool := do {
    let ir <- compile_source_ir fused_source "view_fused_ir";
    match ir {
        Result.err e => do {
            println ("view_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "main_monad";
            return (check_contains hot "call i64 @monad_view_payload(i64 "
                && check_contains hot "call i64 @monad_view_new(i64 "
                && check_contains hot "call i64 @monad_view_set(i64 "
                && check_contains hot "call i64 @monad_view_free(i64 ")
        },
    }
}

/// The fused path must not call the boxed read (the `Cell.get` wrapper,
/// which is what actually reaches `monad_view_get`), must not allocate
/// the `Pair` (`Pair` is tag 15, arity 2), and must not lift a single
/// closure: inlining every continuation is what keeps the whole program
/// in `main_monad`.
#[test]
def test_fused_cell_binds_keep_no_boxed_get_or_pair : IO Bool := do {
    let ir <- compile_source_ir fused_source "view_fused_nobox_ir";
    match ir {
        Result.err e => do {
            println ("view_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "main_monad";
            return (Bool.not (check_contains hot "@\"init.view::Cell.get\"(")
                && Bool.not (check_contains hot "alloc_constructor(i64 15, i64 2)")
                && Bool.not (check_contains hot "call i64 @alloc_closure"))
        },
    }
}

/// Control: an escaping pair keeps the boxed `Cell.get` wrapper.
#[test]
def test_escaping_pair_keeps_the_boxed_get : IO Bool := do {
    let ir <- compile_source_ir escaping_source "view_boxed_ir";
    match ir {
        Result.err e => do {
            println ("view_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "main_monad";
            return (check_contains hot "@\"init.view::Cell.get\"("
                && Bool.not (check_contains hot "monad_view_payload"))
        },
    }
}

/// Both lowerings must compute the same answer -- the fused IR is a
/// shape change, not a semantics change.
#[test]
def test_fused_and_boxed_agree : IO Bool := do {
    let fused <- compile_source_run_expect fused_source "view_fused_run" 42;
    let boxed <- compile_source_run_expect escaping_source "view_boxed_run" 42;
    return (fused && boxed)
}
