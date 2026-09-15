/// Regression tests for the native `take_while` scan pathology that
/// blocked rung 2 (`v29 check lang/main.mo`): the parser's scanner was
/// MUTUAL tail recursion (`take_while_loop`/`take_while_check`), which
/// the self-hosted backend's `apply_self_tco` can not rewrite (self-
/// recursion only -- mutual would need LLVM `musttail`), so every
/// compiled binary paid two real stack frames per input char and a
/// ~225KB scan blew the 8MB stack at ~11K chars (measured: a
/// 22.7K-frame alternating backtrace, rsp pinned at the stack guard
/// page). At the same time `monad_string_drop` malloc-copied the whole
/// REMAINING input on every step -- O(n^2) copies, ~2.4GB leaked for
/// one whole-file pass -- which is what OOM-killed `check lang/main.mo`
/// at 30GB.
///
/// Fixes under test (all three only matter once the program is
/// COMPILED -- the Rust interpreter's shared_str views and its own
/// deep-recursion stack never saw any of this):
///   1. `take_while_loop` restructured to self-recursion
///      (`lang/parser/combinators.mo`) -- now `apply_self_tco` turns
///      it into a loop back-edge, constant stack for any input.
///   2. `monad_string_drop` zero-copy (`lang/codegen/runtime.c`) -- a
///      pointer bump, O(1) and leak-free per step.
///   3. `is_empty` via `String.get s 0` + `monad_string_get`'s
///      `i == 0` fast path (`lang/parser/core.mo`,
///      `lang/codegen/runtime.mo`) -- without it every step ran a
///      full `strlen` of the remaining input, O(n^2) pure CPU.
///
/// The test scans a 33,805-byte string (~3x the measured pre-fix
/// stack limit, and enough pre-fix copying to leak hundreds of MB):
/// a regression reproduces as a SIGSEGV exit (139) or OOM/timeout
/// rather than the expected exit code. Full consumption leaves
/// `rest` empty, so the exit is 100; any truncation leaves a rest
/// whose length makes the exit differ from 100 (the input length is
/// deliberately NOT a multiple of 256 so `exit = 100 + rest` mod 256
/// can't alias the success value).
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The always-true whole-input scan: pre-fix this is exactly the
/// per-char mutual-recursion + whole-remainder-copy loop, at ~3x the
/// input size that SIGSEGV'd the pre-fix binary.
#[test]
def test_take_while_tco_large_scan : IO Bool :=
    let source := r#"use io {IO}
open IO {println}
use lang.parser.combinators {take_while}

def always_true (s : String) : Bool := I64.beq (String.length s) (String.length s)

def main (args : List String) : IO I64 := do {
    let s0 : String := "012345678901234567890123456789012";
    let s1 : String := String.concat s0 s0;
    let s2 : String := String.concat s1 s1;
    let s3 : String := String.concat s2 s2;
    let s4 : String := String.concat s3 s3;
    let s5 : String := String.concat s4 s4;
    let s6 : String := String.concat s5 s5;
    let s7 : String := String.concat s6 s6;
    let s8 : String := String.concat s7 s7;
    let s9 : String := String.concat s8 s8;
    let s10 : String := String.concat s9 s9;
    let big : String := String.concat s10 "0123456789abc";
    match take_while always_true big {
        ParseResult.success rest consumed =>
            do {
                println ("rest " ++ I64.to_string (String.length rest) ++ " consumed " ++ I64.to_string (String.length consumed));
                return (I64.add 100 (String.length rest))
            },
        ParseResult.fail e => do { println "parse failed"; return 1 },
    }
}
"# in
    compile_source_run_expect source "test_take_while_tco_large_scan" 100