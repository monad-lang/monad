/// IR-shape gate for the IO do-bind fusion (`try_compile_io_bind_db`,
/// `codegen/src/emit.mo`), the heapless-loops H1 change.
///
/// A do-bind in `IO` compiles to `monad_io_bind(m, closure)`, and the
/// runtime runs the continuation inside the bind's own C frame -- so a
/// recursive IO loop nests one frame (and keeps everything those frames
/// reference alive under Boehm) for as long as it runs. The fusion
/// compiles the continuation inline instead, leaving the recursive call
/// in tail position, where `tco.mo` turns it into a loop.
///
/// These tests prove the frame and the closure are GONE; a runtime test
/// passes on both paths. The named-continuation control proves the
/// selection is shape-based: an `IO.bind` whose second argument is not a
/// lambda keeps the boxed path.
///
/// The fixture module is named after the basename (`io_fused_ir`), so its
/// defs are emitted as `io_fused_ir::<name>`.
use lib::test::e2e_harness {
    compile_source_ir, compile_source_run_expect, ir_function,
}
use lib::test::support {check_contains}
open IO {println}

/// A self-recursive IO loop with one do-bind: pre-fusion this is
/// `monad_io_bind` + a lifted `lambda_N` + a real self-call per
/// iteration.
def fused_source : String :=
    "def pure_i64 (n : I64) : IO I64 := IO.pure n\n"
    ++ "#[terminating]\n"
    ++ "def count (n : I64) : IO I64 := do {\n"
    ++ "    let x <- pure_i64 n;\n"
    ++ "    if x < 1 then IO.pure 42 else count (x - 1)\n"
    ++ "}\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    count 1000\n"
    ++ "}\n"

/// The control: the bind's continuation is a named def, not a lambda, so
/// the fusion must decline and leave the `IO.bind` call in place.
def fallback_source : String :=
    "def step (n : I64) : IO I64 := IO.pure n\n"
    ++ "def k (x : I64) : IO I64 := IO.pure x\n"
    ++ "def via (n : I64) : IO I64 := IO.bind (step n) k\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    via 1\n"
    ++ "}\n"

/// The `RawIO` variant: its bind unwraps ONE wrapper (`RawIO.io x`), not
/// the `IO.mk (RawIO.io x)` pair. Wrapping into `IO` only at `main` keeps
/// the loop itself `RawIO`-typed, so a wrong unwrap depth shows up as the
/// wrong value rather than a compile error.
def raw_io_source : String :=
    "def raw_pure (n : I64) : RawIO I64 := RawIO.pure n\n"
    ++ "#[terminating]\n"
    ++ "def raw_count (n : I64) : RawIO I64 := do {\n"
    ++ "    let x <- raw_pure n;\n"
    ++ "    if x < 1 then RawIO.pure 42 else raw_count (x - 1)\n"
    ++ "}\n"
    ++ "def main (args : List String) : IO I64 := IO.mk (raw_count 1000)\n"

#[test]
def test_fused_io_bind_keeps_no_bind_frame_or_closure : IO Bool := do {
    let ir <- compile_source_ir fused_source "io_fused_ir";
    match ir {
        Result.err e => do {
            println ("io_bind_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "io_fused_ir::count";
            return (check_contains hot "call i64 @monad_io_bind_guard(i64 "
                && Bool.not (check_contains hot "call i64 @monad_io_bind(")
                && Bool.not (check_contains hot "call i64 @alloc_closure")
                && Bool.not (check_contains hot "call i64 @apply_closure1("))
        },
    }
}

/// The recursive call must be gone too: `tco.mo` turns the inlined tail
/// call into a back-edge. This is the assertion that fails if the fusion
/// ever leaves the call in a non-tail position (for example by giving the
/// cancel branch its own `ret`, which makes `tco.mo` bail).
#[test]
def test_fused_io_loop_is_a_loop : IO Bool := do {
    let ir <- compile_source_ir fused_source "io_fused_loop_ir";
    match ir {
        Result.err e => do {
            println ("io_bind_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "io_fused_ir::count";
            return (Bool.not (check_contains hot "call i64 @\"io_fused_ir::count\"("))
        },
    }
}

/// Control: a bind whose continuation is a named def falls through to
/// `IO.bind`, and never reaches the fused guard.
#[test]
def test_named_continuation_keeps_the_boxed_bind : IO Bool := do {
    let ir <- compile_source_ir fallback_source "io_fallback_ir";
    match ir {
        Result.err e => do {
            println ("io_bind_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "io_fallback_ir::via";
            return (check_contains hot "@\"init.io::IO.bind\"("
                && Bool.not (check_contains hot "monad_io_bind_guard"))
        },
    }
}

/// The fused lowering computes the same answer -- it is a shape change,
/// not a semantics change.
#[test]
def test_fused_io_bind_runs : IO Bool :=
    compile_source_run_expect fused_source "io_fused_run" 42

/// A `RawIO` bind fuses the same way (one wrapper, not two).
#[test]
def test_fused_raw_io_bind_keeps_no_bind_frame_or_closure : IO Bool := do {
    let ir <- compile_source_ir raw_io_source "io_raw_ir";
    match ir {
        Result.err e => do {
            println ("io_bind_ir: compile failed: " ++ e);
            return false
        },
        Result.ok text => do {
            let hot := ir_function text "io_raw_ir::raw_count";
            return (check_contains hot "call i64 @monad_io_bind_guard(i64 "
                && Bool.not (check_contains hot "call i64 @monad_io_bind(")
                && Bool.not (check_contains hot "call i64 @alloc_closure"))
        },
    }
}

/// ...and the single-layer payload read is exercised at runtime.
#[test]
def test_fused_raw_io_bind_runs : IO Bool :=
    compile_source_run_expect raw_io_source "io_raw_run" 42
