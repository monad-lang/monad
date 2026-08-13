//! End-to-end test for Phase 5
//! (`plans/implementations/core-term-closure-evaluator.md`): a real
//! program that actually uses arithmetic/comparison/`if` — the
//! `length`/`Stack`/`Nat` program in `core_eval_integration_test.rs`
//! (Phase 4) deliberately avoided this, since native execution wasn't
//! wired up yet. Runs the exact same `fib`/`List`-class-dispatch source
//! `core/benches/kernel_eval_bench.rs` uses, so a later benchmark can
//! compare apples to apples.

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

// `eval_core_program` (Phase 6) is exactly this test's own former
// hand-assembled pipeline (`check_all_modules_capturing_core` ->
// `lower_program` -> `force_global`, re-checking the whole `init`
// package through the capturing checker every call — see its own doc
// comment in `lib.rs` for why) now exposed as a public entry point, so
// this test uses it directly rather than duplicating it.
fn run(source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top("'native_e2e_test");
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// `if`/`==`/`-`/`+` (via `HAdd.add`/`HSub.sub`/`BEq.beq`'s dictionary
/// projection down to `i64_add`/`i64_sub`/`i64_eq` natives), plus
/// self-recursion through `Global` — the exact source
/// `kernel_eval_bench.rs`'s `ARITHMETIC_RECURSION` benchmark uses.
const FIB: &str = r#"
use init

#[terminating]
def fib (n : I64) : I64 :=
    if n == 0
    then 0
    else if n == 1
    then 1
    else (fib (n - 1)) + (fib (n - 2))

def main : I64 := fib 10
"#;

#[test]
fn phase5_evaluates_real_arithmetic_end_to_end() {
  // fib(10) = 55 -- exercises `if`, `==`, `-`, `+`, and recursion all
  // going through real natives, not hand-built IR.
  assert_eq!(as_i64(&run(FIB)), 55);
}

/// `List`-based class dispatch, matching `kernel_eval_bench.rs`'s
/// `CLASS_DISPATCH` benchmark -- proves constructors (`List.cons`/
/// `empty`), `match`, and arithmetic/comparison natives all compose
/// correctly in one program.
const CLASS_DISPATCH: &str = r#"
use init

#[terminating]
def build_list (n : I64) : List I64 :=
    if n == 0
    then List.empty
    else List.cons n (build_list (n - 1))

#[terminating]
def count_eq (target : I64) (xs : List I64) : I64 :=
    match xs {
        List.cons hd tl =>
            if hd == target
            then 1 + (count_eq target tl)
            else count_eq target tl,
        List.empty => 0
    }

def main : I64 := count_eq 3 (build_list 10)
"#;

#[test]
fn phase5_evaluates_list_class_dispatch_end_to_end() {
  // build_list 10 = [10,9,...,1], target 3 appears exactly once.
  assert_eq!(as_i64(&run(CLASS_DISPATCH)), 1);
}

/// `String.beq`/`String.drop`, matching the string-handling shape of
/// `kernel_eval_bench.rs`'s `PARSER_COMBINATOR_SHAPED` benchmark.
const STRING_OPS: &str = r#"
use init

#[terminating]
def count_down (s : String) : I64 :=
    if String.beq s ""
    then 0
    else 1 + (count_down (String.drop 1 s))

def main : I64 := count_down "hello"
"#;

#[test]
fn phase5_evaluates_string_natives_end_to_end() {
  assert_eq!(as_i64(&run(STRING_OPS)), 5);
}

/// Regression test for a real Phase 7 bug: matching the exact
/// `PARSER_COMBINATOR_SHAPED` source `core/benches/core_eval_bench.rs`
/// uses, first found when that benchmark crashed with
/// `UnresolvedAtom`. Root cause: `chain`'s own body matches on `step
/// n s`'s result (`Step.ok`/`Step.stop`) but never otherwise names
/// `Step` — the checker's `desugar_struct_literals` captured the
/// match's resolved inductive atom into `CoreProgram::match_resolutions`
/// (`core_check.rs`) without also ensuring that same atom was reachable
/// from `chain`'s own per-def `atom_paths` map (which is normally
/// populated purely by walking literal `Free(atom)` nodes in the term —
/// and `Step` never appears as one in `chain`'s body, only inside the
/// separately-captured match resolution). Fixed by inserting the
/// resolved atom's path into `atom_paths` at the exact point it's
/// resolved, in `desugar_struct_literals`'s own `Match` arm.
const PARSER_COMBINATOR_SHAPED: &str = r#"
use init

type Step {
    ok (rest : String) (n : I64),
    stop (rest : String)
}

#[partial]
def skip_one (s : String) : String :=
    if String.beq s ""
    then s
    else String.drop 1 s

#[partial]
def step (label : I64) (s : String) : Step :=
    if String.beq s ""
    then Step.stop s
    else Step.ok (skip_one s) label

#[terminating]
def chain (n : I64) (s : String) : I64 :=
    match step n s {
        Step.ok rest label => label + (chain (label + 1) rest),
        Step.stop _ => n
    }

def input : String :=
    "the quick brown fox jumps over the lazy dog the quick brown fox jumps over the lazy dog"

def main : I64 := chain 0 input
"#;

#[test]
fn phase7_evaluates_parser_combinator_shaped_program_end_to_end() {
  // `input` is 87 chars; `chain` sums labels 0..=87 -> 87*88/2 = 3828.
  assert_eq!(as_i64(&run(PARSER_COMBINATOR_SHAPED)), 3828);
}

/// Regression test for a real Phase 8 bug, found running `init`'s own
/// real test corpus through `run_parity_tests` (`core_parity.rs`):
/// `"a" ++ "b" == "ab"` (`init/test_constraints.mo`'s `test_append_string`)
/// combines two class methods, `Append.append` nested inside `BEq.beq`'s
/// own first argument. `lower_term`'s generic `App` case (fun-then-arg,
/// one level at a time) reaches `BEq`'s dict-projection `Match` node --
/// sitting at the spine's base, i.e. innermost `fun` -- before ever
/// lowering `Append`'s call nested in `arg` position, but the checker's
/// `try_resolve_class_method` (`core_check.rs`) captures a class
/// method's own resolution AFTER desugaring its spine's arguments
/// (args-first, self-last, the same convention `if`/`match`/`let`
/// already follow) -- desyncing the queue for any expression combining
/// two class methods this way. Fixed via `dict_projection_spine`
/// (`lower_core_ir.rs`), recognizing this exact shape and lowering
/// arguments before the head.
const NESTED_CLASS_METHODS: &str = r#"
use init

def main : I64 := if "a" ++ "b" == "ab" then 1 else 0
"#;

#[test]
fn phase8_evaluates_nested_class_method_calls_end_to_end() {
  assert_eq!(as_i64(&run(NESTED_CLASS_METHODS)), 1);
}

/// Regression test for a second real Phase 8 bug, found the same way as
/// the one above but one level deeper: `test_foldr_foldl_equiv`
/// (`init/foldable_tests.mo`, `init/foldable_tests_fold.mo`) combines
/// *two separate* class-method calls, each itself needing the
/// speculative-redo treatment (its own class param isn't pinned by any
/// earlier argument), sequentially via nested `let`s. `try_resolve_
/// class_method`'s redo step used to always splice its own recaptured
/// entries onto the very FRONT of the queue -- correct for the FIRST
/// such call in a chain (nothing precedes it yet), but wrong for any
/// LATER one: a preceding sibling call's own (already correctly
/// positioned) captures were already sitting at the front, and got
/// shoved to the back of the SECOND call's own entries instead of
/// staying put. Fixed by splicing at the queue's length from the moment
/// THIS call started (`queue_len_at_entry`, `core_check.rs`), not
/// always `0` (`MetaContext::splice_match_resolutions`, `core_unify.rs`).
/// Reproduced here with only base `init`-package classes (`BEq`/
/// `Append`) rather than `Foldable` (which lives in `init.foldable`, a
/// separate module `run()`'s limited module set below can't reach) --
/// the exact same trigger shape: two sequential `let`-bound class-method
/// calls, each on its own needing the redo (its own class param, `A`
/// for `BEq`, is pinned only once its own first argument is checked,
/// never earlier), combined afterward.
const SEQUENTIAL_CLASS_METHOD_LETS: &str = r#"
use init

def main : I64 :=
    let x : Bool := "a" ++ "b" == "ab" in
    let y : Bool := "c" ++ "d" == "cd" in
    if x then (if y then 1 else 0) else 0
"#;

#[test]
fn phase8_evaluates_sequential_class_method_lets_end_to_end() {
  assert_eq!(as_i64(&run(SEQUENTIAL_CLASS_METHOD_LETS)), 1);
}
