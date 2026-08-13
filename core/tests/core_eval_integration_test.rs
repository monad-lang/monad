//! End-to-end test for Phase 4
//! (`plans/implementations/core-term-closure-evaluator.md`): a real,
//! recursive Monad program, run through the full pipeline —
//! `check_all_modules_capturing_core` (Phase 0) -> `lower_program`
//! (Phase 2) -> `core_eval::force_global`/`eval` (Phase 4) — checked
//! against the actual expected result, not just "it didn't error."
//!
//! Deliberately avoids native arithmetic (`+`/`-`/`==` all end up
//! dictionary-projected to a *native* call, and native *execution* is
//! Phase 5's job, not yet wired up here — see `core_eval.rs`'s doc
//! comment) — `length` below recurses over one inductive (`Stack`) and
//! builds another (`Nat`) purely via constructors and `match`, so it
//! exercises recursion, closures, and constructor-tag dispatch working
//! together on a real, checked, lowered program without depending on
//! anything Phase 5 hasn't built yet.

use monad_core::core_check_module::check_all_modules_capturing_core;
use monad_core::core_eval::force_global;
use monad_core::core_value::{GlobalCache, GlobalTable, Value};
use monad_core::term::ModulePath;
use monad_core::term::module::{default_modules, load_decls_from_text_with_path};

const SOURCE: &str = r#"
use init

type Stack {
    cons (head : I64) (tail : Stack),
    empty
}

type Nat {
    zero,
    succ (n : Nat)
}

#[terminating]
def length (xs : Stack) : Nat :=
    match xs {
        cons _ tail => Nat.succ (length tail),
        empty => Nat.zero
    }

def three_stack : Stack :=
    Stack.cons 1 (Stack.cons 2 (Stack.cons 3 Stack.empty))

def main : Nat := length three_stack
"#;

/// Counts the `Nat.succ` nesting depth of a `Value::Con` chain, asserting
/// it bottoms out at `Nat.zero`'s tag (0, its only-declared-before-`succ`
/// position — see the `type Nat { zero, succ(n) }` declaration order).
fn nat_depth(v: &Value) -> u32 {
  match v {
    Value::Con { tag: 0, args } if args.is_empty() => 0,
    Value::Con { tag: 1, args } if args.len() == 1 => 1 + nat_depth(&args[0]),
    other => panic!("expected a Nat-shaped Con chain, got {other:?}"),
  }
}

#[test]
fn phase4_evaluates_a_real_recursive_program_end_to_end() {
  let loaded = default_modules().expect("default_modules");
  let path = ModulePath::top("'eval_e2e_test");
  let decls = load_decls_from_text_with_path(SOURCE, &Default::default()).expect("parse");
  let prelude_path = ModulePath::top("'prelude");
  let prelude_text = include_str!("../../init/prelude.mo");
  let prelude_decls =
    load_decls_from_text_with_path(prelude_text, &Default::default()).expect("parse prelude");

  let program = check_all_modules_capturing_core(
    &[(prelude_path, prelude_decls), (path.clone(), decls)],
    &loaded,
  )
  .expect("check_all_modules_capturing_core");

  let lowered = monad_core::lower_core_ir::lower_program(&program).expect("lower_program");

  let main_path = monad_core::term::mpt("main");
  let main_idx = lowered
    .index_of(&main_path)
    .expect("expected `main` to have a global slot");
  assert!(
    !lowered.skipped.iter().any(|(p, _)| *p == main_path),
    "expected `main` to lower successfully, but it was skipped: {:?}",
    lowered.skipped
  );

  let natives = monad_core::core_value::NativeTable::from_lowered(&lowered);
  let globals = GlobalTable::new(lowered.globals);
  let mut cache = GlobalCache::new(globals.len());
  let result = force_global(main_idx, &globals, &natives, &mut cache)
    .unwrap_or_else(|e| panic!("evaluating `main` failed: {e}"));

  // `three_stack` has 3 elements -> `length` should be `Nat.succ
  // (Nat.succ (Nat.succ Nat.zero))`, depth 3 -- proving real recursion
  // (Global self-reference through a Lam, not a false cycle -- see
  // core_eval.rs's own unit tests for the isolated version of this
  // check) and real constructor-tag dispatch worked correctly together
  // on an actual checked-and-lowered program, not just hand-built IR.
  assert_eq!(nat_depth(&result), 3, "expected length(three_stack) == 3");

  // Forcing `main` again must hit the memoized cache entry directly
  // (see `GlobalCache`) rather than re-evaluating or erroring.
  let result2 = force_global(main_idx, &globals, &natives, &mut cache).unwrap();
  assert_eq!(nat_depth(&result2), 3);
}
