/// The heapless-loops exit criterion: a plain recursive IO loop runs in
/// constant native stack under a SMALL stack, with no `IO.iterate`.
///
/// Before the IO do-bind fusion (`lang/src/codegen/emit.mo`'s
/// `try_compile_io_bind_db`), each iteration went through
/// `monad_io_bind`, which calls the continuation inside its own C frame,
/// so a 1,000,000-iteration loop could never finish under 2 MiB -- it
/// would SIGSEGV (exit 139) long before. After the fusion the recursive
/// call is in tail position and `tco.mo` rewrites it into a back-edge,
/// so the same binary exits with the loop's own answer (42).
///
/// The stack is set through `MONAD_STACK_BYTES`, read by the C runtime's
/// `monad_stack_bytes()` when it spawns `main_monad`'s thread (the value
/// is clamped to 1 MiB..1 GiB). 2 MiB is far below what one frame per
/// iteration needs.
///
/// This test builds and runs a real binary (via the shared e2e harness),
/// so it belongs in `slow_tests/`.
open IO {println}
use lang::codegen::test::e2e_harness {compile_source_run_stack_expect}

def loop_source : String :=
    "def pure_i64 (n : I64) : IO I64 := IO.pure n\n"
    ++ "#[terminating]\n"
    ++ "def count (n : I64) : IO I64 := do {\n"
    ++ "    let x <- pure_i64 n;\n"
    ++ "    if x < 1 then IO.pure 42 else count (x - 1)\n"
    ++ "}\n"
    ++ "def main (args : List String) : IO I64 := do {\n"
    ++ "    count 1000000\n"
    ++ "}\n"

#[test]
def test_million_iteration_io_loop_under_a_two_mib_stack : IO Bool := do {
    let ok <- compile_source_run_stack_expect loop_source "heapless_io_loop" 2097152 42;
    return ok
}
