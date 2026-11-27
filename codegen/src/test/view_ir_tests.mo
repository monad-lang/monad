/// IR-shape gate for view-types P2's fused `let`
/// (`try_compile_view_bind_db`, `codegen/src/emit.mo`).
///
/// A `Cell` accessor costs one `Pair` allocation on the boxed path (the C
/// runtime builds it for `get`). The fusion lowers the shape a real
/// program uses -- a `let` whose initializer is a Cell accessor, with a
/// continuation that consumes the result immediately (for `get`, a match
/// on the pair) -- straight to the native call: `monad_view_payload` for
/// a `get` (the handle rides through unchanged), and the direct native
/// for `new`/`set`/`free`. These tests are the only thing that proves the
/// box is GONE; a runtime test would pass on both paths.
///
/// The accessors themselves are PURE (`init/src/view.mo`): the native
/// mutates only the handle it consumes and returns, so the old `RawIO.io`
/// and `IO.mk` boxes are gone from every path, fused or not. What is left
/// to fuse is the `Pair`.
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
use lib::test::support {check_contains}
open IO {println}

/// Every Cell operation in the fused shape, in one do-block. `main`'s
/// own exit code is the value read back (42).
def fused_source : String :=
    "use init::view {Cell}\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    let c0 := Cell.new 41;\n"
    ++ "    let p := Cell.get c0;\n"
    ++ "    match p {\n"
    ++ "        Pair.pair x c1 => do {\n"
    ++ "            let c2 := Cell.set c1 (I64.add x 1);\n"
    ++ "            let p2 := Cell.get c2;\n"
    ++ "            match p2 {\n"
    ++ "                Pair.pair y c3 => do {\n"
    ++ "                    let _ := Cell.free c3;\n"
    ++ "                    return y\n"
    ++ "                },\n"
    ++ "            }\n"
    ++ "        },\n"
    ++ "    }\n"
    ++ "}\n"

/// The pair ESCAPES to another def, so the `get` cannot be fused.
def escaping_source : String :=
    "use init::view {Cell}\n"
    ++ "def finish (p : Pair I64 (Cell I64)) : I64 :=\n"
    ++ "    match p {\n"
    ++ "        Pair.pair w c => let _ := Cell.free c in w,\n"
    ++ "    }\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    let c0 := Cell.new 42;\n"
    ++ "    let p := Cell.get c0;\n"
    ++ "    return (finish p)\n"
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

// ── Slice: the six natives reach the compiled backend ───────────────
//
// `Slice` has no fused lowering in v1 -- `split` returns two handles and
// `get` returns a `Result` -- so what needs pinning is that every one of
// the six `monad_slice_*` targets is CALLED. A missing `natives.mo` entry
// fails the call-target gate at compile time and a missing
// `runtime_declarations` entry fails linking; this one compile covers
// both, and the run half pins that the wiring computes.

/// A program that exercises all six `Slice` natives and answers 102:
/// 99 (the `set` wrote it) plus 1 (the left half's first element) plus 2
/// (its length).
def slice_source : String :=
    "use init::view {Slice}\n"
    ++ "def read_mid (s : Slice 3 I64) : I64 :=\n"
    ++ "    match Slice.get s 1 {\n"
    ++ "        Result.ok p => match p {\n"
    ++ "            Pair.pair v s1 => let _ := Slice.free s1 in v,\n"
    ++ "        },\n"
    ++ "        Result.err s1 => let _ := Slice.free s1 in 0 - 2,\n"
    ++ "    }\n"
    ++ "def set_and_read (xs : List I64) : I64 :=\n"
    ++ "    match Slice.of_list xs 3 {\n"
    ++ "        Result.ok s => match Slice.set s 1 99 {\n"
    ++ "            Result.ok s1 => read_mid s1,\n"
    ++ "            Result.err s1 => let _ := Slice.free s1 in 0 - 3,\n"
    ++ "        },\n"
    ++ "        Result.err _e => 0 - 4,\n"
    ++ "    }\n"
    ++ "def split_halves (s : Slice 4 I64) : I64 :=\n"
    ++ "    match Slice.split_at s 2 {\n"
    ++ "        Result.ok p => match p {\n"
    ++ "            Pair.pair l r => match Slice.length l {\n"
    ++ "                Pair.pair llen l1 => match Slice.get l1 0 {\n"
    ++ "                    Result.ok q => match q {\n"
    ++ "                        Pair.pair v l2 =>\n"
    ++ "                            let _l := Slice.free l2 in\n"
    ++ "                            let _r := Slice.free r in\n"
    ++ "                            I64.add v llen,\n"
    ++ "                    },\n"
    ++ "                    Result.err l2 =>\n"
    ++ "                        let _l := Slice.free l2 in\n"
    ++ "                        let _r := Slice.free r in\n"
    ++ "                        0 - 5,\n"
    ++ "                },\n"
    ++ "            },\n"
    ++ "        },\n"
    ++ "        Result.err s1 => let _ := Slice.free s1 in 0 - 6,\n"
    ++ "    }\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    let p := Slice.of_list [1, 2, 3, 4] 4;\n"
    ++ "    match p {\n"
    ++ "        Result.ok s => do {\n"
    ++ "            let c := set_and_read [0, 0, 0];\n"
    ++ "            let h := split_halves s;\n"
    ++ "            return (I64.add c h)\n"
    ++ "        },\n"
    ++ "        Result.err _e => do { return 0 },\n"
    ++ "    }\n"
    ++ "}\n"

#[test]
def test_slice_ops_emit_all_six_native_calls : IO Bool := do {
    let ir <- compile_source_ir slice_source "slice_ir";
    match ir {
        Result.err e => do {
            println ("slice_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text =>
            return (check_contains text "call i64 @monad_slice_of_list(i64 "
                && check_contains text "call i64 @monad_slice_length(i64 "
                && check_contains text "call i64 @monad_slice_get(i64 "
                && check_contains text "call i64 @monad_slice_set(i64 "
                && check_contains text "call i64 @monad_slice_split(i64 "
                && check_contains text "call i64 @monad_slice_free(i64 "),
    }
}

/// The same program through the compiled backend.
#[test]
def test_slice_program_runs : IO Bool :=
    compile_source_run_expect slice_source "slice_run" 102
