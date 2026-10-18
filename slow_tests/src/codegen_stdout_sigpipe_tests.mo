/// Regression tests for a compiled program whose stdout reader goes
/// away (`prog | head`).
///
/// `runtime.c`'s `main` ignores SIGPIPE so that a write to a vanished
/// pipe or socket peer comes back as an EPIPE the caller can see. No
/// stdio write checks its result, so the process's OWN stdout then lost
/// the signal death it relied on: an endless printer piped into `head`
/// never stopped. `stdio_die_on_epipe` restores the old behaviour for
/// stdio. These rows run the binary as `bin | head -n 1` and compare the
/// BINARY's exit status.
use lang::codegen::test::e2e_harness {compile_source_run_piped_expect}

/// Far more output than a pipe buffer holds, so the writes that follow
/// head's exit fail with EPIPE: the binary must die of SIGPIPE (141),
/// not run to the end and exit 0.
#[test]
def test_println_into_a_closed_pipe_dies_of_sigpipe : IO Bool :=
    let source := r#"open IO {println}
#[terminating]
def spam (n : I64) : IO Unit :=
    if n > 200000 then IO.pure Unit.unit
    else do { println "y"; spam (n + 1) }
def main (args : List String) : IO Unit := spam 0
"# in
    compile_source_run_piped_expect source "test_println_into_a_closed_pipe_dies_of_sigpipe" 141

/// The guard: output that fits before head's exit is still a clean 0.
#[test]
def test_one_line_into_head_still_exits_zero : IO Bool :=
    let source := r#"open IO {println}
def main (args : List String) : IO Unit := println "only"
"# in
    compile_source_run_piped_expect source "test_one_line_into_head_still_exits_zero" 0
