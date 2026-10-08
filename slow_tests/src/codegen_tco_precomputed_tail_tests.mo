/// Regression tests for the TCO site finder's cross-block bug.
///
/// A block whose `ret` (or merge phi) consumed a self-call's value that
/// was `assign`ed in a DOMINATING block was rewritten into a loop
/// back-edge, but the call itself was never removed (its `assign` lives
/// in another block), so every loop iteration re-ran the whole recursive
/// suffix: the `let tail := f rest in match ... { arm => tail }` shape
/// went from O(n) to O(2^n). `qualify`'s `unresolvable_names`/
/// `unresolved_messages` have exactly this shape, and a whole-program
/// closure with ~28 ambiguous names paid ~2^28 recursive calls per
/// module -- a compiled `monad test cli/src/tests/main_tests.mo` never
/// finished, which is what blew the sweep's budget (measured pre-fix:
/// exact x2 per list element, 827us at 16 elements to 3.5s at 28).
///
/// The fix: a site is only recorded when the call's own `assign` lives
/// in the same block as the `ret`/phi pair consuming it. A pre-computed
/// value is returned as-is -- free. Genuine self tail-calls still get
/// the loop rewrite (`codegen_take_while_tco_tests` covers those).
///
/// Without the fix the first test does not fail fast -- it runs 2^64
/// recursive calls, so a regression reproduces as a sweep timeout
/// instead of the expected exit code, the same class as the take_while
/// test's SIGSEGV-or-timeout signature.
open IO {println}
use lang::codegen::test::e2e_harness {compile_source_run_expect}

/// The precomputed-tail shape at a depth where O(2^n) is hopeless but
/// O(n) is instant: post-fix 64 elements resolve in microseconds.
#[test]
def test_tco_precomputed_tail_not_exponential : IO Bool :=
    let source := r#"def depth (b : Bool) (xs : List I64) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _n rest =>
            let tail := depth b rest in
            match b {
                Bool.true => tail,
                Bool.false => I64.add tail 1
            }
    }

#[terminating]
def upto (n : I64) (acc : List I64) : List I64 :=
    if I64.lt n 1 then acc else upto (I64.sub n 1) (List.cons n acc)

def main (args : List String) : IO I64 := do {
    return (depth Bool.true (upto 64 List.empty))
}
"# in
    compile_source_run_expect source "test_tco_precomputed_tail" 0

/// The arm that USES the precomputed value still computes correctly:
/// `depth` with `b := Bool.false` counts the list, so the rebuilt value
/// must reach the exit code intact.
#[test]
def test_tco_precomputed_tail_value_correct : IO Bool :=
    let source := r#"def depth (b : Bool) (xs : List I64) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _n rest =>
            let tail := depth b rest in
            match b {
                Bool.true => tail,
                Bool.false => I64.add tail 1
            }
    }

#[terminating]
def upto (n : I64) (acc : List I64) : List I64 :=
    if I64.lt n 1 then acc else upto (I64.sub n 1) (List.cons n acc)

def main (args : List String) : IO I64 := do {
    return (I64.add 100 (depth Bool.false (upto 10 List.empty)))
}
"# in
    compile_source_run_expect source "test_tco_precomputed_tail_value" 110