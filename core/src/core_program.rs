//! Whole-program retention of checked `CoreTerm`s — Phase 0 of
//! `plans/implementations/core-term-closure-evaluator.md`.
//!
//! `CoreTerm` bodies don't normally survive past a single def's
//! type-check call: `check_one_def_new`/`check_one_instance_new`
//! (`core_check_module.rs`) build a fully-checked `body_c: CoreTerm`,
//! then immediately raise it back to `Term` and discard it. `CoreProgram`
//! is an additive, opt-in accumulator that callers can thread through
//! `type_check_module_decls_new_inner` (via `Option<&mut CoreProgram>`)
//! to capture that `CoreTerm` before it's thrown away, along with the
//! per-def `atom_paths` needed to resolve its `Free(Atom)` occurrences,
//! and the match-arm/inductive/instance metadata a `CoreTerm -> IR`
//! lowering pass (Phase 2) needs but which the checker only computes
//! transiently.
//!
//! Nothing in this file changes checker behavior — every existing call
//! site keeps passing `None` and pays zero extra cost.

use crate::core_term::{Atom, CoreTerm};
use crate::term::{Identifier, ModulePath};
use crate::{AtomPathMap, Map};

/// One checked def's pre-`raise_core` `CoreTerm` body, plus what's needed
/// to resolve its `Free(Atom)` occurrences to durable global paths.
///
/// `atom_paths` is specific to *this* def's own check (each def's peeled
/// Forall params/dictionary params mint their own atoms — see
/// `check_one_def_new`'s doc comments) — do not assume it's shared or
/// valid for any other def's `term`/`typ`.
#[derive(Debug, Clone)]
pub struct CheckedCoreDef {
  pub term: CoreTerm,
  pub typ: CoreTerm,
  pub atom_paths: AtomPathMap,
}

/// One constructor's name and field count (arity) — enough to build a
/// `core_ir::Con` for a fully- or partially-applied reference without
/// needing the checker's own field-*type* bookkeeping (`StructFields`),
/// which a lowering pass never needs.
#[derive(Debug, Clone)]
pub struct CoreConstructorInfo {
  pub name: Identifier,
  pub arity: u32,
}

/// A registered inductive's constructors, in declaration order — order
/// *is* the constructor's tag, matching the convention `lower.rs`/
/// `eval_term.rs`'s recursor-compilation already uses. Built directly
/// from surface `Decl::Type` data, not from `register_inductive`'s
/// internal `StructFields` bookkeeping — nothing here needs field
/// *types*, just names, arities, and (for a single-constructor "struct"
/// inductive) field order.
#[derive(Debug, Clone, Default)]
pub struct CoreInductiveInfo {
  pub constructors: Vec<CoreConstructorInfo>,
  /// The sole constructor's field names, in declaration order — only
  /// present for a single-constructor ("struct-shaped") inductive, since
  /// only those can appear as a `CoreLit::StructLit`/`StructUpdate`
  /// (keyed by field name, unordered) that a lowering pass needs to
  /// re-order into an ordinary positional `Con`.
  pub struct_field_names: Option<Vec<Identifier>>,
}

/// One `instance` declaration's dictionary shape: which class it
/// implements, and the durable path of each checked method body, in the
/// class's declared method order (`class_method_order`, the same order
/// `check_one_instance_new` already assembles its `Term::Con` in). A
/// `CoreTerm -> IR` lowering pass reconstructs the dictionary value
/// on demand from these method paths (each independently present in
/// `CoreProgram::defs`, since `check_one_instance_new` captures each
/// method through an ordinary `check_one_def_new` call) — no separate
/// `CoreTerm::Con` for the instance itself is captured or needed here.
#[derive(Debug, Clone)]
pub struct CoreInstanceInfo {
  pub class_name: ModulePath,
  pub method_paths: Vec<ModulePath>,
}

/// Whole-program accumulator. See module doc comment.
#[derive(Debug, Clone, Default)]
pub struct CoreProgram {
  /// Every captured def/instance-method body, keyed by its durable
  /// global path — a top-level def's own `name`, or (for an instance's
  /// method) `instance.name().append([method_name])`, which is unique
  /// per instance since ordinary method `Def`s are parsed with a bare,
  /// non-instance-qualified name (`impls_map` collision risk otherwise —
  /// see the plan's Phase 0 section).
  pub defs: Map<ModulePath, CheckedCoreDef>,
  pub inductives: Map<ModulePath, CoreInductiveInfo>,
  pub instances: Map<ModulePath, CoreInstanceInfo>,
  /// Each def's own `Match`/`if` resolutions, keyed by that def's
  /// capture path, **in left-to-right visitation order** — re-deriving
  /// the resolved inductive from constructor names alone is provably
  /// ambiguous (e.g. `List`/`Vec` both declare a bare `cons`
  /// constructor), so the checker's own resolution must be captured, but
  /// it can't be keyed by the scrutinee's own content: `check`/`infer`
  /// open enclosing binders (`Bound` -> a fresh `Free` atom) before
  /// recursing into a body, so the scrutinee captured during checking is
  /// structurally different from the closed (`Bound`-indexed) scrutinee
  /// in the final, stored `CoreTerm` (confirmed empirically — every
  /// captured scrutinee is `Free(atom)`, never `Bound(_)`). Instead,
  /// resolutions for one def are recorded in the same order
  /// `check`/`infer` visits that def's `Match`/`if` nodes, and a
  /// lowering pass must consume them in that same order (a `VecDeque`/
  /// `pop_front` per def) — see
  /// `core_check_module.rs::check_one_def_new` (which drains
  /// `MetaContext::take_match_resolutions` once per def, right after
  /// that def's own `check`/`infer` call, so entries from different defs
  /// never interleave) and `lower_core_ir.rs::lower_match`.
  pub match_resolutions: Map<ModulePath, Vec<(Vec<Identifier>, Atom)>>,
}

impl CoreProgram {
  pub fn new() -> Self {
    Self::default()
  }
}
