//! Benchmarks for the tree-walking evaluator (`core/src/eval.rs`), used as
//! a baseline for comparison against the `EvalTerm`/kernel evaluator (see
//! `plans/implementations/two-term-kernel.md` and the plan file this
//! benchmark suite was built for). Three workloads, each targeting a
//! specific bottleneck identified in the tree-walker:
//!
//! - `arithmetic_recursion`: a tight recursive function with no typeclass
//!   dispatch — isolates whole-body-substitution cost (no environments,
//!   `eval.rs::substitute`).
//! - `class_dispatch`: repeated `BEq.beq` (`==`) calls over a list —
//!   isolates uncached-per-call typeclass instance resolution
//!   (`eval.rs::eval_app`'s `find_instance`/`InstanceKey` path).
//! - `parser_combinator_shaped`: many small, deeply-chained function calls
//!   threading a `String` — mirrors the shape of `lang/parser.mo`'s
//!   combinator style, which historically caused a severe (>10min per
//!   test) blowup under the (never-merged-to-this-branch) `EvalTerm`
//!   kernel evaluator's `resolve_const` deep-clone bug. Not the literal
//!   `lang/parser.mo` file (avoids fragile on-disk module-loading paths
//!   inside a benchmark), but the same architectural shape: many tiny
//!   functions, each returning a small wrapped result, called in a deep
//!   chain.

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use monad_core::eval::r#type::type_check;
use monad_core::eval::{EvalOptions, eval};
use monad_core::term::module::{Scope, default_modules, load_module_from_text};
use monad_core::term::{Hole, ModulePath, mpt};

/// Evaluate `checked_term` against a fresh `default_modules()` scope built
/// from `source`. We rebuild the scope per benchmark invocation (outside
/// the timed section, via `iter_batched`'s setup closure) since `Scope`
/// borrows from `LoadedModules`/`GlobalScope` and criterion's closures
/// need owned, self-contained setup per batch.
fn bench_eval(c: &mut Criterion, name: &str, source: &str) {
  let path = ModulePath::top("'bench");
  c.bench_function(name, |b| {
    b.iter_batched(
      || {
        let mut loaded = default_modules().expect("default_modules");
        load_module_from_text(source, &path, &mut loaded).expect("load_module_from_text");
        let module = loaded.get_module(&path).expect("module not loaded").clone();
        let def = module
          .get_def(&mpt("main"))
          .expect("main not found")
          .value();
        let term = def.term.clone();
        (loaded, term)
      },
      |(loaded, main_term)| {
        let loaded_scopes = loaded.scopes();
        let global = loaded_scopes.global(&path).expect("scope not built");
        let scope: Scope = global.scope();
        let (checked, _typ) = type_check(main_term, Hole, &scope)
          .unwrap_or_else(|e| panic!("type error: {e}"))
          .to_tuple();
        eval(checked, &scope, &EvalOptions::default()).unwrap_or_else(|e| panic!("eval error: {e}"))
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
  bench_eval(c, "arithmetic_recursion", ARITHMETIC_RECURSION);
}

fn class_dispatch(c: &mut Criterion) {
  bench_eval(c, "class_dispatch", CLASS_DISPATCH);
}

fn parser_combinator_shaped(c: &mut Criterion) {
  bench_eval(c, "parser_combinator_shaped", PARSER_COMBINATOR_SHAPED);
}

criterion_group!(
  benches,
  arithmetic_recursion,
  class_dispatch,
  parser_combinator_shaped
);
criterion_main!(benches);
