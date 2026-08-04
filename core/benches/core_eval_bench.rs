//! Benchmarks for the `CoreTerm`-closure evaluator (`core/src/core_eval.rs`
//! + friends, reached via `check_all_modules_capturing_core` ->
//! `lower_program` -> `force_global`), gated behind the `core-eval` Cargo
//! feature. Same three workloads as `eval_bench.rs` (the tree-walker
//! baseline) so the two can be compared directly — see
//! `plans/implementations/core-term-closure-evaluator.md`, Phase 7.
//!
//! Unlike `eval_bench.rs` (whose timed closure includes a fresh
//! `type_check` of just the target module's own `main` term, since the
//! rest of the `init` package was already checked once outside the timed
//! section by `default_modules()`), this benchmark's setup phase does the
//! ENTIRE `check_all_modules_capturing_core` + `lower_program` pass.
//! `check_all_modules_capturing_core` re-checks the whole `init` package
//! through the NEW capturing checker every time it's called — see
//! `eval_core_program`'s own doc comment in `lib.rs` for why
//! (`default_modules()`'s already-checked copy of `init` never populates a
//! `CoreProgram` on its own). Timing that 8-module recheck inside the loop
//! would measure typechecker cost, not evaluator cost — exactly what this
//! benchmark exists to isolate. Only `force_global` (with a fresh,
//! unmemoized `GlobalCache` per batch, so no iteration can piggyback on
//! another's memoized globals) is timed.

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use monad_core::core_check_module::check_all_modules_capturing_core;
use monad_core::core_eval::force_global;
use monad_core::core_value::{GlobalCache, GlobalTable, NativeTable};
use monad_core::lower_core_ir::{LoweredProgram, lower_program};
use monad_core::term::module::{
  default_modules, init_package_sources, load_decls_from_text_with_path,
};
use monad_core::term::{ModulePath, mpt};

fn bench_core_eval(c: &mut Criterion, name: &str, source: &str) {
  let path = ModulePath::top("'bench");
  c.bench_function(name, |b| {
    b.iter_batched(
      || -> (u32, LoweredProgram) {
        let loaded = default_modules().expect("default_modules");
        let decls = load_decls_from_text_with_path(source, &Default::default()).expect("parse");
        let mut modules: Vec<_> = init_package_sources()
          .expect("init_package_sources")
          .into_iter()
          .map(|(p, text)| {
            let d = load_decls_from_text_with_path(&text, &Default::default())
              .unwrap_or_else(|e| panic!("parse {p}: {e}"));
            (p, d)
          })
          .collect();
        modules.push((path.clone(), decls));

        let program = check_all_modules_capturing_core(&modules, &loaded)
          .expect("check_all_modules_capturing_core");
        let lowered = lower_program(&program).expect("lower_program");
        let main_idx = lowered.index_of(&mpt("main")).expect("main not found");
        (main_idx, lowered)
      },
      |(main_idx, lowered)| {
        let natives = NativeTable::from_lowered(&lowered);
        let globals = GlobalTable::new(lowered.globals);
        let mut cache = GlobalCache::new(globals.len());
        force_global(main_idx, &globals, &natives, &mut cache)
          .unwrap_or_else(|e| panic!("core eval error: {e}"))
      },
      BatchSize::SmallInput,
    )
  });
}

const ARITHMETIC_RECURSION: &str = r#"
use init

@[terminating]
def fib (n : I64) : I64 :=
    if n == 0
    then 0
    else if n == 1
    then 1
    else (fib (n - 1)) + (fib (n - 2))

def main : I64 := fib 22
"#;

const CLASS_DISPATCH: &str = r#"
use init

@[terminating]
def build_list (n : I64) : List I64 :=
    if n == 0
    then List.empty
    else List.cons n (build_list (n - 1))

@[terminating]
def count_eq (target : I64) (xs : List I64) : I64 :=
    match xs {
        List.cons hd tl =>
            if hd == target
            then 1 + (count_eq target tl)
            else count_eq target tl,
        List.empty => 0
    }

def main : I64 := count_eq 100 (build_list 300)
"#;

const PARSER_COMBINATOR_SHAPED: &str = r#"
use init

// Mirrors lang/parser.mo's combinator style: many tiny functions, each
// consuming a String prefix and returning a small wrapped result, chained
// through a long sequence of calls rather than a single loop.
type Step {
    ok (rest : String) (n : I64),
    stop (rest : String)
}

@[partial]
def skip_one (s : String) : String :=
    if String.beq s ""
    then s
    else String.drop 1 s

@[partial]
def step (label : I64) (s : String) : Step :=
    if String.beq s ""
    then Step.stop s
    else Step.ok (skip_one s) label

@[terminating]
def chain (n : I64) (s : String) : I64 :=
    match step n s {
        Step.ok rest label => label + (chain (label + 1) rest),
        Step.stop _ => n
    }

def input : String :=
    "the quick brown fox jumps over the lazy dog the quick brown fox jumps over the lazy dog"

def main : I64 := chain 0 input
"#;

fn arithmetic_recursion(c: &mut Criterion) {
  bench_core_eval(c, "core_arithmetic_recursion", ARITHMETIC_RECURSION);
}

fn class_dispatch(c: &mut Criterion) {
  bench_core_eval(c, "core_class_dispatch", CLASS_DISPATCH);
}

fn parser_combinator_shaped(c: &mut Criterion) {
  bench_core_eval(c, "core_parser_combinator_shaped", PARSER_COMBINATOR_SHAPED);
}

criterion_group!(
  benches,
  arithmetic_recursion,
  class_dispatch,
  parser_combinator_shaped
);
criterion_main!(benches);
