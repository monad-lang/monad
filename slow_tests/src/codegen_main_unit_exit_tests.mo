/// Regression tests for `main`'s own exit code.
///
/// `unwrap_io_return_blocks` (`codegen/src/emit.mo`) reads field 0 of
/// `main`'s returned `IO` box and returns it, because the C runtime's
/// `int main()` casts whatever it gets straight to `int`. That is right for
/// an `IO I64` and wrong for an `IO Unit`: `Unit` is its own zero-field
/// allocation, so the exit code became the low byte of a heap pointer --
/// 144 on one machine, 96 on another, from the same source, never 0
/// (`plans/implementations/2026-10-04-main-unit-return-exits-garbage-code.md`,
/// found at a TODO app's first milestone: a hello-world mote).
///
/// `main : IO Unit` is what nearly every program declares, so these rows
/// cover the common case and the scalar case that must not regress with it.
/// The harness compares the process's real exit status, which is the whole
/// point -- no IR-shape assertion can see this.
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// The reported shape, verbatim: output correct, exit code garbage.
#[test]
def test_main_io_unit_exits_zero : IO Bool :=
    let source := r#"open IO {println}
def main (args : List String) : IO Unit := println "hi"
"# in
    compile_source_run_expect source "test_main_io_unit_exits_zero" 0

/// The guard that keeps `IO Unit` from being fixed by returning 0 for every
/// `main`: an `IO I64` still exits the value its source names.
#[test]
def test_main_io_i64_still_returns_its_value : IO Bool :=
    let source := r#"open IO {println}
def main (args : List String) : IO I64 := do {
    println "hi";
    return 7
}
"# in
    compile_source_run_expect source "test_main_io_i64_still_returns_its_value" 7
