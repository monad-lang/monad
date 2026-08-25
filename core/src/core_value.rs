//! `Value`/`Env` — the runtime representation the closure-based evaluator
//! (Phase 4) reduces `CoreIr` to. Phase 3 of
//! `plans/implementations/core-term-closure-evaluator.md`.
//!
//! This is the direct fix for `EvalTerm`'s substitution-based design: a
//! `Lam` evaluates to a `Value::Closure` that *captures* its environment
//! by reference (an O(1) `Arc` clone, no tree copy), and applying it
//! *extends* that environment with one new binding (again O(1)) instead
//! of rewriting the body — there is no `subst`/`shift` function anywhere
//! in this file, and there never needs to be one.
//!
//! **`Env` uses `Arc`, not `Rc`.** The plan's own Phase 3 sketch flagged
//! this as an open question ("does `run_tests_parallel` need to share
//! `Env` across threads?") and tentatively favored `Rc`. Decided the
//! other way: `Value`/`Closure`s are exactly the kind of thing that can
//! end up shared across threads in this codebase (`run_tests_parallel`,
//! any future parallel evaluation), and retrofitting `Rc -> Arc` later
//! would touch every closure/environment call site — cheaper to pay the
//! (small, atomic-refcount) `Arc` cost from the start than to risk a
//! `Send`/`Sync` wall discovered after the fact. `Value`/`Env` carry no
//! interior mutability, so they're `Send + Sync` automatically once
//! every field is.
//!
//! **Global memoization is an explicit parameter, not interior-mutable
//! state on `GlobalTable`.** The plan originally sketched
//! `GlobalTable { defs, resolved: Vec<OnceCell<Value>> }`, but this
//! module instead keeps `GlobalTable` a plain, immutable view over a
//! `lower_core_ir::LoweredProgram`, and puts the memoized results in a
//! separate `GlobalCache` that callers create and thread through
//! `eval`/`apply`/`force_global` themselves (see `core_eval.rs`, Phase
//! 4). This avoids `OnceCell` and its specific reentrancy semantics
//! entirely — `GlobalCache::force` below implements its own explicit
//! "already forcing" check instead, which produces a clear
//! `CoreEvalError` on a genuine cycle rather than either panicking or
//! silently looping forever.

use std::sync::Arc;

use crate::lower_core_ir::{GlobalDef, LoweredProgram, WellKnownCtors};
use crate::term::Identifier;

/// Shared handle to a lexical environment frame — always used behind an
/// `Arc`, never bare, so capturing one (closure creation) and extending
/// one (function application) are both O(1): a refcount bump plus one
/// small allocation, never a clone of anything already in the chain.
pub type EnvRef = Arc<Env>;

/// A persistent (immutable, shared-tail) cons-list environment, indexed
/// the same way `CoreIr::Local`/`CoreTerm::Bound` are: 0 = innermost
/// (most recently bound). Chosen over an indexable persistent vector
/// (e.g. the `im` crate's `Vector`) deliberately: this workspace has no
/// persistent-collection dependency today, capture/extend are O(1)
/// either way, and even this representation's O(depth) lookup
/// (`Env::get` walks the chain) is a large win over the tree-walker's
/// name-based `Scope` lookup it replaces, since parameter-nesting depth
/// in practice is small. Revisit only if profiling after the evaluator
/// (Phase 4) is in place shows lookup depth actually matters — swapping
/// the representation only touches this file.
#[derive(Debug)]
pub enum Env {
  Nil,
  Cons(Value, EnvRef),
}

impl Env {
  pub fn nil() -> EnvRef {
    Arc::new(Env::Nil)
  }

  /// O(1): one `Arc` allocation for the new frame, one `Arc::clone`
  /// (atomic refcount bump) to share the existing chain as its tail —
  /// `v` is the only value actually moved/cloned by the caller, not the
  /// chain.
  pub fn extend(env: &EnvRef, v: Value) -> EnvRef {
    Arc::new(Env::Cons(v, env.clone()))
  }

  /// O(depth): walks the chain to the `idx`-th frame from the front.
  /// Returns `None` for an out-of-range index — a lowering bug (a
  /// `Local` index with no matching binder), not a normal runtime
  /// condition, so callers should treat it as an internal-error case,
  /// not a recoverable one.
  pub fn get(env: &EnvRef, idx: u32) -> Option<&Value> {
    let mut cur = env;
    let mut remaining = idx;
    loop {
      match cur.as_ref() {
        Env::Nil => return None,
        Env::Cons(v, tail) => {
          if remaining == 0 {
            return Some(v);
          }
          remaining -= 1;
          cur = tail;
        }
      }
    }
  }
}

/// A runtime value. Distinct from `CoreIr` (the compiled syntax it's
/// reduced from) on purpose — conflating "compiled code" and "runtime
/// value" in one type (as `EvalTerm` does) is part of what enabled the
/// bare-`Const`-not-forced bug found earlier in this project's `EvalTerm`
/// work: a value here is always already in normal form, never a
/// still-to-be-reduced expression.
#[derive(Debug, Clone)]
pub enum Value {
  /// Scalar literals reuse `core_ir::IrLit` directly rather than a
  /// separate `RuntimeLit` type — a literal has no substructure that
  /// needs a distinct "compiled" vs. "value" representation the way
  /// `Lam`/`App` do (that's exactly the distinction `Closure` exists
  /// for), so a second, parallel scalar type would just be duplication.
  Lit(crate::core_ir::IrLit),
  /// What a `Lam` evaluates to: the still-unevaluated body plus the
  /// environment it closes over, captured by reference (`EnvRef`, O(1)).
  Closure {
    body: crate::core_ir::IrRef,
    env: EnvRef,
  },
  /// A fully- or partially-applied constructor. `args.len() <= arity`
  /// (arity itself lives on the `CoreIr::Con`/`GlobalDef::Constructor`
  /// node that produced this, not duplicated here); application appends
  /// to `args` left-to-right (`CoreTerm`'s own `App`/`Bound` are ordinary
  /// left-to-right de-Bruijn application, so no out-of-order slot
  /// addressing is ever needed — see `lower_core_ir.rs`'s `lower_con`
  /// doc comment).
  ///
  /// `args` is `Arc`-wrapped, not a bare `Vec`, so `Value::clone()` is
  /// O(1) (a refcount bump) rather than a deep recursive copy of the
  /// whole structure — a list/tree/map/record value is nested `Con`s
  /// (e.g. `cons head tail`, `tail` itself a `Con`), and every ordinary
  /// variable read (`Env::get(...).cloned()`, `GlobalCache::get`'s
  /// `v.clone()`, both `core_eval.rs`) used to pay a full
  /// O(current-structure-size) clone — `O(N)+O(N-1)+...+O(1) = O(N²)`
  /// across a linear recursive walk of an N-element structure, the same
  /// shape `shared_str.rs`'s `SharedStr` already fixed for strings
  /// specifically. Confirmed the dominant cost (~90% of eval time, via
  /// `to_vec`/drop_glue/allocator churn under callgrind) for ADT-heavy
  /// workloads — see `plans/implementations/value-con-arc-wrap-
  /// optimization.md`. Mutating sites (`core_eval.rs`'s incremental
  /// application, `eval/meta_reflect.rs`'s reification helpers) use
  /// `Arc::make_mut` (copy-on-write) — cheap in the common case since a
  /// `Value` about to receive another argument or be destructured is
  /// essentially never aliased at that exact moment.
  Con {
    tag: u32,
    args: std::sync::Arc<Vec<Value>>,
  },
  /// A native/builtin call with some but not all of its arguments
  /// supplied yet. Same `Arc`-wrapped `args` rationale as `Con` above.
  PartialNtv {
    native_id: u32,
    args: std::sync::Arc<Vec<Value>>,
  },
}

/// A read-only view over a lowered program's global slots — exactly
/// `lower_core_ir::LoweredProgram::globals`, wrapped so `core_eval.rs`
/// doesn't need to reach into that module directly. Carries no
/// memoization state of its own; see `GlobalCache`.
pub struct GlobalTable {
  globals: Vec<GlobalDef>,
}

impl GlobalTable {
  pub fn new(globals: Vec<GlobalDef>) -> Self {
    Self { globals }
  }

  pub fn get(&self, idx: u32) -> Option<&GlobalDef> {
    self.globals.get(idx as usize)
  }

  pub fn len(&self) -> usize {
    self.globals.len()
  }

  pub fn is_empty(&self) -> bool {
    self.globals.is_empty()
  }
}

/// Native name + arity table, plus the well-known constructor tags native
/// execution needs (`lower_core_ir::WellKnownCtors` — resolved directly
/// from `CoreProgram.inductives` at `lower_program` time, NOT from which
/// constructors happen to have been interned as `Global` slots: a
/// fully-applied constructor like the surface `true`/`false` literals
/// compiles straight to a `CoreIr::Con` node, never touching `Global` at
/// all, so a `LoweredProgram`-slot-based lookup would come up empty for
/// exactly the constructors native execution needs most — `Bool.true`/
/// `Bool.false`, for every comparison native's boolean result). Everything
/// `core_native::exec_native` reads is bundled into one immutable,
/// resolved-once parameter here, the same "explicit parameter, not
/// interior-mutable state" shape as `GlobalTable`/`GlobalCache` above.
/// Unlike `GlobalCache`, `NativeTable` has no mutable state at all (a
/// native's arity/well-known tags never change once resolved), so
/// there's no cache counterpart to it.
pub struct NativeTable {
  names: Vec<Identifier>,
  arities: Vec<u32>,
  pub well_known: WellKnownCtors,
}

impl NativeTable {
  /// Build a `NativeTable` directly from its parts — the general
  /// constructor; `from_lowered` (the ordinary, real-program path) is a
  /// thin wrapper over this.
  pub fn new(names: Vec<Identifier>, arities: Vec<u32>, well_known: WellKnownCtors) -> Self {
    Self {
      names,
      arities,
      well_known,
    }
  }

  pub fn from_lowered(lowered: &LoweredProgram) -> Self {
    Self {
      names: lowered.natives.clone(),
      arities: lowered.native_arities.clone(),
      well_known: lowered.well_known.clone(),
    }
  }

  pub fn name(&self, id: u32) -> Option<&Identifier> {
    self.names.get(id as usize)
  }

  /// A native's fixed arity — `0` for an out-of-range id (an internal
  /// lowering bug, same convention `GlobalTable::get` leaves callers to
  /// handle via `Option`/an explicit error, not a panic).
  pub fn arity(&self, id: u32) -> u32 {
    self.arities.get(id as usize).copied().unwrap_or(0)
  }
}

/// One global slot's memoization state. `InProgress` exists purely to
/// turn a genuine reference cycle into a clear, immediate error instead
/// of an infinite loop or a stack overflow — see this module's doc
/// comment for why this replaces `OnceCell::get_or_try_init`'s built-in
/// reentrancy behavior rather than relying on it.
#[derive(Debug, Clone)]
enum Slot {
  Empty,
  InProgress,
  Done(Value),
}

/// Explicit, caller-owned cache of forced global values — one slot per
/// `GlobalTable` entry, sized to match it. Passed as an ordinary `&mut`
/// parameter through `eval`/`apply`/`force_global` (Phase 4) rather than
/// embedded as interior-mutable state on `GlobalTable` itself: no
/// `OnceCell`, no interior mutability at all, and the caller decides the
/// cache's lifetime (e.g. one per top-level evaluation, or one shared
/// across many, its choice — not baked into the table).
pub struct GlobalCache {
  slots: Vec<Slot>,
  /// When true, `core_eval.rs`'s `fire_or_accumulate` refuses to dispatch
  /// any native not on `core_native::is_pure_native`'s allowlist (and
  /// blocks `await_fiber`, checked the same way) — used by
  /// `core/src/eval/meta_compile.rs` to run macro-expansion-time "meta"
  /// evaluation in a sandbox with no IO/concurrency, per
  /// `plans/review-and-reduce-the-greedy-nest.md`. `false` (via `new`,
  /// every pre-existing call site) is the ordinary, unrestricted program
  /// evaluator — zero behavior change there.
  pure_only: bool,
}

impl GlobalCache {
  pub fn new(len: usize) -> Self {
    Self {
      slots: vec![Slot::Empty; len],
      pure_only: false,
    }
  }

  /// Same as `new`, but natives are restricted to `core_native::is_pure_native`'s
  /// allowlist for the lifetime of this cache — see the `pure_only` field
  /// doc comment.
  pub fn new_pure(len: usize) -> Self {
    Self {
      slots: vec![Slot::Empty; len],
      pure_only: true,
    }
  }

  pub fn is_pure_only(&self) -> bool {
    self.pure_only
  }

  /// Already-forced value for `idx`, if any — an O(1) clone (never a
  /// re-evaluation), since every `Value` variant is cheap to clone
  /// (`Closure` clones an `Arc`/`Arc` pair; `Con`/`PartialNtv` clone their
  /// `args` as a single `Arc` refcount bump, not the structure itself).
  pub fn get(&self, idx: u32) -> Option<&Value> {
    match self.slots.get(idx as usize) {
      Some(Slot::Done(v)) => Some(v),
      _ => None,
    }
  }

  /// Mark `idx` as currently being forced — returns `Err` if it already
  /// was (a genuine cycle: some global's own evaluation transitively
  /// depends on its own not-yet-computed value). Callers (`core_eval.rs`'s
  /// `force_global`) call this before evaluating a slot's body and
  /// `store` after.
  pub fn begin(&mut self, idx: u32) -> Result<(), CoreEvalCycle> {
    match self.slots.get(idx as usize) {
      Some(Slot::InProgress) => Err(CoreEvalCycle { idx }),
      _ => {
        self.slots[idx as usize] = Slot::InProgress;
        Ok(())
      }
    }
  }

  pub fn store(&mut self, idx: u32, value: Value) {
    self.slots[idx as usize] = Slot::Done(value);
  }

  /// Release `idx`'s `InProgress` marker back to `Empty` after its
  /// evaluation failed — called by `core_eval.rs`'s `force_global` on
  /// every error path. Without this, a slot that fails once (an
  /// `UnresolvedGlobal`, a native arg error, ...) stays `InProgress`
  /// forever: nothing ever calls `store` to move it to `Done`, so any
  /// LATER, unrelated attempt to force the same slot (a real scenario —
  /// e.g. `core_parity.rs` shares one `GlobalCache` across every
  /// discovered test in a file, and two different tests can easily
  /// share a common helper global) sees `InProgress` and reports a
  /// spurious `CoreEvalCycle`, masking whatever the real, deterministic
  /// error actually was. Resetting to `Empty` lets a later force retry
  /// from scratch — for a genuine failure this reproduces the same real
  /// error again (evaluation here has no external mutable state to make
  /// it non-deterministic), just without the cycle-detector's false
  /// positive standing in the way.
  pub fn fail(&mut self, idx: u32) {
    self.slots[idx as usize] = Slot::Empty;
  }
}

/// A global slot was still `InProgress` when it was referenced again —
/// see `GlobalCache::begin`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CoreEvalCycle {
  pub idx: u32,
}

/// Compile-time proof of this module's thread-safety claim — if a future
/// change adds interior mutability (an `Rc`, a `Cell`, ...) to `Value`,
/// `Env`, or `GlobalTable`, this fails to compile instead of silently
/// losing `Send`/`Sync`.
const _ASSERT_SEND_SYNC: fn() = || {
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<Value>();
  assert_send_sync::<Env>();
  assert_send_sync::<GlobalTable>();
  assert_send_sync::<NativeTable>();
};

#[cfg(test)]
mod tests {
  use super::*;
  use crate::core_ir::IrLit;
  use crate::term::NumSuffix;

  fn lit(v: i64) -> Value {
    Value::Lit(IrLit::Num(v, NumSuffix::I64))
  }

  #[test]
  fn test_env_nil_get_is_none() {
    let env = Env::nil();
    assert!(Env::get(&env, 0).is_none());
  }

  #[test]
  fn test_env_extend_and_get_innermost_first() {
    let env = Env::nil();
    let env = Env::extend(&env, lit(1)); // bound first, will be Local(1) once another is pushed
    let env = Env::extend(&env, lit(2)); // bound last, is Local(0) -- innermost
    assert!(matches!(
      Env::get(&env, 0),
      Some(Value::Lit(IrLit::Num(2, _)))
    ));
    assert!(matches!(
      Env::get(&env, 1),
      Some(Value::Lit(IrLit::Num(1, _)))
    ));
    assert!(Env::get(&env, 2).is_none());
  }

  #[test]
  fn test_env_extend_does_not_disturb_shared_tail() {
    // Two branches extending the SAME base environment must not see
    // each other's bindings -- this is the whole point of a persistent
    // (not in-place-mutated) structure.
    let base = Env::extend(&Env::nil(), lit(0));
    let branch_a = Env::extend(&base, lit(1));
    let branch_b = Env::extend(&base, lit(2));
    assert!(matches!(
      Env::get(&branch_a, 0),
      Some(Value::Lit(IrLit::Num(1, _)))
    ));
    assert!(matches!(
      Env::get(&branch_b, 0),
      Some(Value::Lit(IrLit::Num(2, _)))
    ));
    assert!(matches!(
      Env::get(&base, 0),
      Some(Value::Lit(IrLit::Num(0, _)))
    ));
  }

  #[test]
  fn test_global_cache_starts_empty() {
    let cache = GlobalCache::new(3);
    assert!(cache.get(0).is_none());
    assert!(cache.get(1).is_none());
  }

  #[test]
  fn test_global_cache_store_and_get() {
    let mut cache = GlobalCache::new(2);
    cache.begin(0).expect("first begin should succeed");
    cache.store(0, lit(42));
    assert!(matches!(cache.get(0), Some(Value::Lit(IrLit::Num(42, _)))));
    assert!(cache.get(1).is_none());
  }

  #[test]
  fn test_global_cache_detects_reentrant_cycle() {
    let mut cache = GlobalCache::new(1);
    cache.begin(0).expect("first begin should succeed");
    // A second `begin` on the same still-in-progress slot is exactly the
    // "some global's value transitively depends on itself" case.
    assert_eq!(cache.begin(0), Err(CoreEvalCycle { idx: 0 }));
  }

  #[test]
  fn test_global_table_basic_access() {
    let table = GlobalTable::new(vec![
      GlobalDef::Constructor { tag: 0, arity: 2 },
      GlobalDef::Unresolved(crate::term::mpt("Foo.bar")),
    ]);
    assert_eq!(table.len(), 2);
    assert!(matches!(
      table.get(0),
      Some(GlobalDef::Constructor { tag: 0, arity: 2 })
    ));
    assert!(matches!(table.get(1), Some(GlobalDef::Unresolved(_))));
    assert!(table.get(2).is_none());
  }
}
