//! The unifier for `CoreTerm` — Phase 1 of
//! `plans/implementations/typechecker-de-bruijn-core.md`.
//!
//! This replaces what `core/src/eval/type.rs` calls `FreeVars`/
//! `match_resolve_type`/`match_resolve_type_inner`/`compare_types`, but
//! keyed by unique metavariable identity (`MetaId`) instead of bare
//! `Identifier` name — the actual fix for the "two independently-scoped
//! generic type parameters that happen to share a name get conflated" bug
//! class documented in the plan.
//!
//! Tested here in isolation against hand-built `CoreTerm` fixtures only —
//! no parser, no lowering pass, no wiring into the real type checker yet
//! (that's Phases 2-4).

use crate::Map;
use crate::core_term::{
  Atom, AtomTable, CoreConstructor, CoreLit, CoreMatchCase, CoreNative, CoreTerm, MetaId, open_at,
  open_with,
};
use crate::term::{Identifier, ModulePath};

// ---------------------------------------------------------------------------
// MetaContext — the unifier's mutable state, keyed by MetaId, never a name
// ---------------------------------------------------------------------------

/// A single mutable substitution map for unification metavariables, plus
/// the type each metavariable was created at (needed to re-attach a
/// `Forall` binder for it at generalization). Every metavariable created
/// via `fresh_meta` has a globally-unique `MetaId` — two calls can never
/// collide, even across what would previously have been two independent
/// `match_resolve_type` invocations sharing a name-keyed map.
#[derive(Debug, Default)]
pub struct MetaContext {
  solved: Map<MetaId, CoreTerm>,
  meta_types: Map<MetaId, CoreTerm>,
  /// Global-name → `Atom` interning table (see `core_term::AtomTable`'s
  /// doc comment) — owned here, an explicit parameter's worth, rather
  /// than a process-wide `OnceLock`, since `MetaContext` is already
  /// threaded as the first argument through virtually every
  /// `core_check`/`core_check_module` function that could need to intern
  /// a name (`primitive_type`, an instance's own atom, ...), so piggy-
  /// backing on it here avoids adding a SEPARATE parameter to every one
  /// of those signatures just for this. `core_check_module.rs`'s
  /// registration phase runs BEFORE any `MetaContext` exists, so it
  /// builds its OWN `AtomTable` first and hands it to
  /// `new_with_atoms` once checking begins — the same table, continued,
  /// not a second independent one.
  atoms: AtomTable,
  /// Opt-in capture of each `Match`/`if` node's resolved inductive
  /// `Atom`, keyed by `(scrutinee, case names)` rather than traversal
  /// position — see `core_program::CoreProgram::match_resolutions`'s doc
  /// comment for why. `None` (the default, `Self::default()`) means
  /// capture is off and `record_match_resolution` is a no-op — every
  /// existing caller that never calls `enable_match_capture` pays
  /// nothing extra.
  match_resolutions: Option<Vec<(Vec<Identifier>, Atom)>>,
}

impl MetaContext {
  pub fn new() -> Self {
    Self::default()
  }

  /// Like `new`, but continuing an `AtomTable` a caller already built
  /// (e.g. `core_check_module.rs`'s registration phase, which must
  /// intern names before any `MetaContext` exists) instead of starting a
  /// fresh, empty one — so a name registered before checking began and
  /// the same name referenced again during checking still resolve to the
  /// identical `Atom`.
  pub fn new_with_atoms(atoms: AtomTable) -> Self {
    Self {
      atoms,
      ..Self::default()
    }
  }

  /// The `Atom` identifying a given global name, allocating one on first
  /// use and reusing it on every subsequent call through this
  /// `MetaContext`'s own table.
  pub fn intern(&mut self, path: ModulePath) -> Atom {
    self.atoms.intern(path)
  }

  pub fn atoms_mut(&mut self) -> &mut AtomTable {
    &mut self.atoms
  }

  pub fn atoms(&self) -> &AtomTable {
    &self.atoms
  }

  /// Turn on `Match`/`if`-node resolution capture (Phase 0 of
  /// `plans/implementations/core-term-closure-evaluator.md`) — a no-op
  /// if already enabled, so callers don't need to track whether they've
  /// called this before.
  pub fn enable_match_capture(&mut self) {
    if self.match_resolutions.is_none() {
      self.match_resolutions = Some(Vec::new());
    }
  }

  /// Record a `Match`/`if` node's resolved inductive `Atom`, in
  /// visitation order. No-op when capture isn't enabled (the default) —
  /// safe to call unconditionally from `core_check.rs`'s `Match`
  /// handling.
  ///
  /// Deliberately *not* keyed by the scrutinee's own content: `check`/
  /// `infer` open enclosing binders (`Bound` -> a fresh `Free` atom)
  /// before recursing into a body, so the scrutinee captured here is in
  /// *opened* form — structurally different from the *closed*
  /// (`Bound`-indexed) scrutinee that ends up in the final, stored
  /// `CoreTerm` a lowering pass sees (confirmed empirically: every
  /// captured scrutinee was `Free(atom)`, never `Bound(_)`, even for
  /// matches deep inside a `Lam`). Instead, captures are consumed
  /// strictly in the same left-to-right order they're recorded — see
  /// `core_program::CoreProgram::match_resolutions`'s doc comment for how
  /// callers keep this correctly scoped per-def.
  pub(crate) fn record_match_resolution(&mut self, case_names: Vec<Identifier>, atom: Atom) {
    if let Some(queue) = self.match_resolutions.as_mut() {
      queue.push((case_names, atom));
    }
  }

  /// Take everything captured so far, **leaving capture enabled** (an
  /// empty queue, ready for the next def) if it was on. Callers drain
  /// this once per def (right after that def's own `check`/`infer` call,
  /// before moving to the next def) so each resulting queue is correctly
  /// scoped to one def's own visitation order, without needing to
  /// re-enable capture for every subsequent def in the same module's
  /// check — see `core_check_module.rs::check_one_def_new`.
  pub fn take_match_resolutions(&mut self) -> Vec<(Vec<Identifier>, Atom)> {
    match self.match_resolutions.as_mut() {
      Some(queue) => std::mem::take(queue),
      None => Vec::new(),
    }
  }

  /// Current length of the capture queue — `0` when capture isn't
  /// enabled, consistent with `record_match_resolution`'s own no-op
  /// behavior there. Lets a caller record where in the queue its OWN
  /// contribution begins, before doing any of its own (possibly
  /// speculative) capturing — see `splice_match_resolutions`'s doc
  /// comment for why this matters beyond just "0".
  pub(crate) fn match_resolutions_len(&self) -> usize {
    self.match_resolutions.as_ref().map_or(0, Vec::len)
  }

  /// Run `f` with capture fully suppressed (a no-op restore if it was
  /// already off) — for a SPECULATIVE/dry-run desugar whose only purpose
  /// is discovering type information (`try_resolve_class_method`'s own
  /// per-arg loop, `core_check.rs`, when a class method's own type
  /// parameter isn't pinned yet) and whose result — and therefore
  /// whatever match resolutions it resolves along the way — will be
  /// entirely thrown away and redone for real once that information is
  /// known. Whatever was captured before this call is untouched and
  /// still there afterward; nothing `f` itself resolves leaves a trace.
  pub(crate) fn without_match_capture<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
    let saved = self.match_resolutions.take();
    let out = f(self);
    self.match_resolutions = saved;
    out
  }

  /// Run `f` with capture (if already enabled — a plain, uncaptured call
  /// to `f` otherwise) redirected into a fresh, separate buffer instead
  /// of the main queue, returned alongside `f`'s own result. Pairs with
  /// `splice_match_resolutions`: used to redo a class method's
  /// speculatively-desugared (and therefore capture-suppressed, via
  /// `without_match_capture`) EARLY arguments for real, once whatever
  /// later argument was going to pin the class method's own type
  /// parameter has done so — the redo's captures need to end up ahead
  /// of anything captured after the speculative pass (the class
  /// method's own dictionary projection, plus any already-resolved
  /// later argument), not merely appended after it, so they can't be
  /// pushed onto the live queue directly; buffering first lets the
  /// caller splice them into the right place.
  pub(crate) fn capture_match_resolutions_into_buffer<T>(
    &mut self,
    f: impl FnOnce(&mut Self) -> T,
  ) -> (T, Vec<(Vec<Identifier>, Atom)>) {
    if self.match_resolutions.is_none() {
      return (f(self), Vec::new());
    }
    let saved = self.match_resolutions.replace(Vec::new());
    let out = f(self);
    let buffer = std::mem::replace(&mut self.match_resolutions, saved).unwrap_or_default();
    (out, buffer)
  }

  /// Splice `entries` into the capture queue at position `at` — the
  /// counterpart to `capture_match_resolutions_into_buffer`. No-op when
  /// capture isn't enabled.
  ///
  /// `at` must be the queue's own length at the moment the call being
  /// redone STARTED (`match_resolutions_len()`, read before that call's
  /// own argument loop) — NOT simply `0`. An earlier version of this
  /// always spliced at the front, reasoning that a class method's own
  /// speculatively-desugared arguments form a PREFIX of ITS OWN spine
  /// (true — unification never un-resolves a type parameter once
  /// pinned) — but that reasoning only accounts for entries captured
  /// *within* the one call being redone, not entries a PRECEDING SIBLING
  /// call already placed at the front of the very same live queue. A
  /// real example that caught this: `let fr := Foldable.foldr(...) in
  /// let fl := Foldable.foldl(...) in fr == fl` — splicing `fl`'s redo
  /// at the front put its captures *before* `fr`'s own (already
  /// correctly positioned) captures and self-capture, when they belong
  /// after. Splicing at the CALLER's own entry-time length correctly
  /// inserts relative to wherever this call's own contribution begins,
  /// regardless of how much a preceding sibling already added.
  pub(crate) fn splice_match_resolutions(
    &mut self,
    at: usize,
    entries: Vec<(Vec<Identifier>, Atom)>,
  ) {
    if let Some(queue) = self.match_resolutions.as_mut() {
      let at = at.min(queue.len());
      let mut tail = queue.split_off(at);
      queue.extend(entries);
      queue.append(&mut tail);
    }
  }

  /// Allocate a fresh, unsolved metavariable of the given type.
  pub fn fresh_meta(&mut self, typ: CoreTerm) -> MetaId {
    let id = MetaId::fresh();
    self.meta_types.insert(id, typ);
    id
  }

  pub fn lookup(&self, id: MetaId) -> Option<&CoreTerm> {
    self.solved.get(&id)
  }

  pub fn meta_type(&self, id: MetaId) -> Option<&CoreTerm> {
    self.meta_types.get(&id)
  }

  pub fn is_solved(&self, id: MetaId) -> bool {
    self.solved.contains_key(&id)
  }

  fn solve(&mut self, id: MetaId, term: CoreTerm) {
    self.solved.insert(id, term);
  }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum UnifyError {
  Mismatch {
    left: CoreTerm,
    right: CoreTerm,
  },
  /// A metavariable would need to be solved with a term that contains
  /// itself — rejected rather than silently producing an infinite type.
  /// `match_resolve_type_inner`/`check_free_vars` in the old checker had
  /// no equivalent check at all.
  OccursCheck {
    meta: MetaId,
    term: CoreTerm,
  },
  /// Placeholder for the Miller-pattern higher-order case (a `Meta`
  /// application spine unified against a non-pattern term) — flagged as a
  /// future extension point in the plan, not implemented now. Reported
  /// explicitly rather than silently guessing, which is strictly better
  /// than the old checker's total lack of detection for this case.
  UnsupportedPattern {
    left: CoreTerm,
    right: CoreTerm,
  },
}

// ---------------------------------------------------------------------------
// force / occurs / bind — metavariable resolution
// ---------------------------------------------------------------------------

/// Resolve a term to its solved value if it's a (possibly chained) solved
/// metavariable at the head position; otherwise return it unchanged. This
/// is the "find" half of union-find-style metavariable resolution — full
/// recursive substitution of every nested `Meta` is `zonk`, below.
pub fn force(mctx: &MetaContext, term: CoreTerm) -> CoreTerm {
  match term {
    CoreTerm::Meta(m) => match mctx.lookup(m) {
      Some(sol) => force(mctx, sol.clone()),
      None => CoreTerm::Meta(m),
    },
    // Must see through `Ctx` here rather than falling into the `other`
    // wildcard below — a solved metavariable wrapped in `Ctx` (e.g. a
    // def's own body position) would otherwise never get resolved, since
    // `CoreTerm::Ctx { .. }` doesn't match `CoreTerm::Meta(_)` structurally.
    // Preserves the wrapper around the forced result so callers matching
    // on `force`'s own output still see (and can strip) the same location.
    CoreTerm::Ctx { loc, term: inner } => CoreTerm::Ctx {
      loc,
      term: Box::new(force(mctx, *inner)),
    },
    other => other,
  }
}

/// Does `term` contain `target`, directly or via any chain of already-solved
/// metavariables? Checked before every `bind`, so a metavariable can never
/// end up solved with a term that (transitively) contains itself.
fn occurs(mctx: &MetaContext, target: MetaId, term: &CoreTerm) -> bool {
  match term {
    CoreTerm::Meta(m) => {
      *m == target || mctx.lookup(*m).is_some_and(|sol| occurs(mctx, target, sol))
    }
    CoreTerm::Bound(_) | CoreTerm::Free(_) | CoreTerm::Sort { .. } | CoreTerm::Hole => false,
    CoreTerm::Forall { typ, body, .. } => occurs(mctx, target, typ) || occurs(mctx, target, body),
    CoreTerm::Pi { arg, ret, .. } => occurs(mctx, target, arg) || occurs(mctx, target, ret),
    CoreTerm::Lam {
      param_typ, body, ..
    } => occurs(mctx, target, param_typ) || occurs(mctx, target, body),
    CoreTerm::App { fun, arg } => occurs(mctx, target, fun) || occurs(mctx, target, arg),
    CoreTerm::Lit(lit) => occurs_lit(mctx, target, lit),
    CoreTerm::Con(c) => occurs_args(mctx, target, &c.args),
    CoreTerm::Ntv(n) => occurs_args(mctx, target, &n.args),
    CoreTerm::Ctx { term, .. } => occurs(mctx, target, term),
  }
}

fn occurs_args(mctx: &MetaContext, target: MetaId, args: &[Option<CoreTerm>]) -> bool {
  args
    .iter()
    .any(|a| a.as_ref().is_some_and(|t| occurs(mctx, target, t)))
}

fn occurs_lit(mctx: &MetaContext, target: MetaId, lit: &CoreLit) -> bool {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      false
    }
    CoreLit::Match { scrutinee, cases } => {
      occurs(mctx, target, scrutinee) || cases.iter().any(|c| occurs(mctx, target, &c.value))
    }
    CoreLit::If { cond, then, els } => {
      occurs(mctx, target, cond) || occurs(mctx, target, then) || occurs(mctx, target, els)
    }
    CoreLit::StructLit { fields, .. } => fields.values().any(|v| occurs(mctx, target, v)),
    CoreLit::StructUpdate { base, fields } => {
      occurs(mctx, target, base) || fields.values().any(|v| occurs(mctx, target, v))
    }
  }
}

fn bind(mctx: &mut MetaContext, m: MetaId, term: CoreTerm) -> Result<(), UnifyError> {
  if occurs(mctx, m, &term) {
    return Err(UnifyError::OccursCheck { meta: m, term });
  }
  mctx.solve(m, term);
  Ok(())
}

// ---------------------------------------------------------------------------
// unify — the actual fix: identity by index/atom/meta-id, never by name
// ---------------------------------------------------------------------------

/// Structurally unify `a` and `b`, recording metavariable solutions in
/// `mctx` as it goes. `Bound`/`Bound` unify iff same index (same relative
/// binder position — there is nothing to special-case the way the old
/// checker's `clash_vars` had to, since two unrelated binders can never
/// produce the same index at the same comparison depth unless they truly
/// are the same position); `Free`/`Free` unify iff same atom (replacing
/// the old checker's unsound "both names are in keep_vars" shortcut with
/// genuine identity comparison).
pub fn unify(mctx: &mut MetaContext, a: &CoreTerm, b: &CoreTerm) -> Result<(), UnifyError> {
  let a = force(mctx, a.clone());
  let b = force(mctx, b.clone());
  // Strip any `Ctx` location wrapper before dispatching on shape — this
  // match's final arm is a wildcard (`_ => Err(mismatch(a, b))`), which
  // the compiler can't flag as missing a `Ctx` case the way an exhaustive
  // match would: without this, a `Ctx`-wrapped `Forall`/`Pi`/`App`/etc.
  // would silently fail to match ANY of the specific-shape arms below and
  // fall straight into "these don't unify", spuriously rejecting valid
  // programs. `unify`'s own recursive calls on sub-terms (`t1`/`t2`,
  // `arg`/`ret`, ...) each re-strip at their own entry, so nested `Ctx`
  // wrappers deeper in the tree are handled the same way, one level at a
  // time.
  let a = a.strip_ctx().clone();
  let b = b.strip_ctx().clone();
  match (&a, &b) {
    (CoreTerm::Hole, _) | (_, CoreTerm::Hole) => Ok(()),

    (CoreTerm::Meta(m1), CoreTerm::Meta(m2)) if m1 == m2 => Ok(()),
    (CoreTerm::Meta(m), _) => bind(mctx, *m, b),
    (_, CoreTerm::Meta(m)) => bind(mctx, *m, a),

    (CoreTerm::Bound(i), CoreTerm::Bound(j)) => {
      if i == j {
        Ok(())
      } else {
        Err(mismatch(a, b))
      }
    }
    (CoreTerm::Free(x), CoreTerm::Free(y)) => {
      if x == y {
        Ok(())
      } else {
        Err(mismatch(a, b))
      }
    }
    // E7: universe cumulativity — a `Sort { level: l1 }`-typed value is
    // also usable wherever `Sort { level: l2 }` (l2 >= l1) is expected
    // (`Prop`/`Sort 0` is a `Sort 1`/`Type` too, standard cumulative-
    // universe semantics), not just when the levels match exactly.
    // Directional: every call site in this checker consistently unifies
    // `(actual/inferred, expected)` in that argument order (`check`'s own
    // generic fallback, `try_absorb_into_forall`, ...), so `l1 <= l2`
    // (the ACTUAL side's level at most the EXPECTED side's) is the
    // correct subsumption direction, not `l1 == l2` or a symmetric `<=`
    // either way (which would wrongly accept `Sort 5` where `Sort 0` is
    // expected too).
    (CoreTerm::Sort { level: l1 }, CoreTerm::Sort { level: l2 }) => {
      if l1 <= l2 {
        Ok(())
      } else {
        Err(mismatch(a, b))
      }
    }

    (
      CoreTerm::Forall {
        typ: t1, body: b1, ..
      },
      CoreTerm::Forall {
        typ: t2, body: b2, ..
      },
    ) => {
      unify(mctx, t1, t2)?;
      unify_under_binder(mctx, b1, b2)
    }
    (
      CoreTerm::Pi {
        arg: a1,
        ret: r1,
        mult: m1,
        ..
      },
      CoreTerm::Pi {
        arg: a2,
        ret: r2,
        mult: m2,
        ..
      },
    ) => {
      if m1 != m2 {
        return Err(mismatch(a.clone(), b.clone()));
      }
      unify(mctx, a1, a2)?;
      unify_under_binder(mctx, r1, r2)
    }
    (
      CoreTerm::Lam {
        param_typ: p1,
        body: b1,
        ..
      },
      CoreTerm::Lam {
        param_typ: p2,
        body: b2,
        ..
      },
    ) => {
      unify(mctx, p1, p2)?;
      unify_under_binder(mctx, b1, b2)
    }
    (CoreTerm::App { fun: f1, arg: a1 }, CoreTerm::App { fun: f2, arg: a2 }) => {
      unify(mctx, f1, f2)?;
      unify(mctx, a1, a2)
    }

    (CoreTerm::Con(c1), CoreTerm::Con(c2)) => unify_con(mctx, &a, &b, c1, c2),
    (CoreTerm::Ntv(n1), CoreTerm::Ntv(n2)) => unify_ntv(mctx, &a, &b, n1, n2),
    (CoreTerm::Lit(l1), CoreTerm::Lit(l2)) => unify_lit(mctx, &a, &b, l1, l2),

    // Exactly one side is still Forall-wrapped (the other arm above
    // already claimed the both-Forall case). This happens whenever a
    // still-polymorphic type surfaces *inside* a structural comparison —
    // e.g. nested inside an `App`'s `fun`/`arg` position during
    // `App`/`App` unification above — not just at a top-level `check`/
    // `infer` call, which is the only place `instantiate_foralls` would
    // otherwise run. Auto-instantiate with a fresh meta and retry, same
    // as `core_check::instantiate_foralls` does at the top level: a
    // polymorphic value being *used* (matched against something else)
    // should be instantiated, not left rigid — mirrors the plan's
    // rejection of the old checker's textual-merge approach, just
    // applied uniformly wherever unification recurses, not only once at
    // the entry point.
    (CoreTerm::Forall { typ, body, .. }, _) => {
      let instantiated = instantiate(mctx, typ, body);
      unify(mctx, &instantiated, &b)
    }
    (_, CoreTerm::Forall { typ, body, .. }) => {
      let instantiated = instantiate(mctx, typ, body);
      unify(mctx, &a, &instantiated)
    }

    _ => Err(mismatch(a, b)),
  }
}

fn mismatch(left: CoreTerm, right: CoreTerm) -> UnifyError {
  UnifyError::Mismatch { left, right }
}

fn unify_args(
  mctx: &mut MetaContext,
  a: &CoreTerm,
  b: &CoreTerm,
  args1: &[Option<CoreTerm>],
  args2: &[Option<CoreTerm>],
) -> Result<(), UnifyError> {
  if args1.len() != args2.len() {
    return Err(mismatch(a.clone(), b.clone()));
  }
  for (x, y) in args1.iter().zip(args2.iter()) {
    match (x, y) {
      (Some(x), Some(y)) => unify(mctx, x, y)?,
      (None, None) => {}
      _ => return Err(mismatch(a.clone(), b.clone())),
    }
  }
  Ok(())
}

fn unify_con(
  mctx: &mut MetaContext,
  a: &CoreTerm,
  b: &CoreTerm,
  c1: &CoreConstructor,
  c2: &CoreConstructor,
) -> Result<(), UnifyError> {
  if c1.name != c2.name || c1.typ_name != c2.typ_name || c1.num_args != c2.num_args {
    return Err(mismatch(a.clone(), b.clone()));
  }
  unify_args(mctx, a, b, &c1.args, &c2.args)
}

fn unify_ntv(
  mctx: &mut MetaContext,
  a: &CoreTerm,
  b: &CoreTerm,
  n1: &CoreNative,
  n2: &CoreNative,
) -> Result<(), UnifyError> {
  if n1.native_name != n2.native_name || n1.num_args != n2.num_args {
    return Err(mismatch(a.clone(), b.clone()));
  }
  unify_args(mctx, a, b, &n1.args, &n2.args)
}

/// Open `body` (bound at literal indices `depth..depth+arity`, an N-ary
/// block of simultaneous binders — e.g. a `match` case's `arity` pattern
/// variables) with `arity` fresh atoms, targeting each literal depth
/// directly (they were never shifted down, since `open_at` never removes
/// a binder from the surrounding structure — see `core_term.rs`'s doc
/// comments). Returns the atoms in binder order (index 0 first).
pub(crate) fn open_n(body: &CoreTerm, depth: u32, arity: u32) -> (Vec<Atom>, CoreTerm) {
  let mut atoms = Vec::with_capacity(arity as usize);
  let mut current = body.clone();
  for i in 0..arity {
    let atom = Atom::fresh();
    current = open_at(&current, depth + i, &CoreTerm::Free(atom));
    atoms.push(atom);
  }
  (atoms, current)
}

fn unify_lit(
  mctx: &mut MetaContext,
  a: &CoreTerm,
  b: &CoreTerm,
  l1: &CoreLit,
  l2: &CoreLit,
) -> Result<(), UnifyError> {
  match (l1, l2) {
    (CoreLit::Str { value: v1 }, CoreLit::Str { value: v2 }) if v1 == v2 => Ok(()),
    (CoreLit::Char { value: v1 }, CoreLit::Char { value: v2 }) if v1 == v2 => Ok(()),
    (
      CoreLit::Num {
        value: v1,
        suffix: s1,
      },
      CoreLit::Num {
        value: v2,
        suffix: s2,
      },
    ) if v1 == v2 && s1 == s2 => Ok(()),
    (
      CoreLit::Float {
        value: v1,
        suffix: s1,
      },
      CoreLit::Float {
        value: v2,
        suffix: s2,
      },
    ) if v1 == v2 && s1 == s2 => Ok(()),
    (
      CoreLit::If {
        cond: c1,
        then: t1,
        els: e1,
      },
      CoreLit::If {
        cond: c2,
        then: t2,
        els: e2,
      },
    ) => {
      unify(mctx, c1, c2)?;
      unify(mctx, t1, t2)?;
      unify(mctx, e1, e2)
    }
    (
      CoreLit::StructLit {
        fields: f1,
        type_name: t1,
      },
      CoreLit::StructLit {
        fields: f2,
        type_name: t2,
      },
    ) => {
      if let (Some(a1), Some(a2)) = (t1, t2)
        && a1 != a2
      {
        return Err(mismatch(a.clone(), b.clone()));
      }
      unify_fields(mctx, a, b, f1, f2)
    }
    (
      CoreLit::StructUpdate {
        base: base1,
        fields: f1,
      },
      CoreLit::StructUpdate {
        base: base2,
        fields: f2,
      },
    ) => {
      unify(mctx, base1, base2)?;
      unify_fields(mctx, a, b, f1, f2)
    }
    (
      CoreLit::Match {
        scrutinee: s1,
        cases: cases1,
      },
      CoreLit::Match {
        scrutinee: s2,
        cases: cases2,
      },
    ) => {
      unify(mctx, s1, s2)?;
      if cases1.len() != cases2.len() {
        return Err(mismatch(a.clone(), b.clone()));
      }
      for (case1, case2) in cases1.iter().zip(cases2.iter()) {
        if case1.name != case2.name || case1.dbgs.len() != case2.dbgs.len() {
          return Err(mismatch(a.clone(), b.clone()));
        }
        let arity = case1.dbgs.len() as u32;
        // Open both sides' bodies with the SAME fresh atoms per position —
        // same "compare under a binder" technique as unify_under_binder,
        // generalized to an N-ary block of simultaneous binders.
        let (atoms, opened1) = open_n(&case1.value, 0, arity);
        let mut opened2 = (*case2.value).clone();
        for (i, atom) in atoms.iter().enumerate() {
          opened2 = open_at(&opened2, i as u32, &CoreTerm::Free(*atom));
        }
        unify(mctx, &opened1, &opened2)?;
      }
      Ok(())
    }
    _ => Err(mismatch(a.clone(), b.clone())),
  }
}

fn unify_fields(
  mctx: &mut MetaContext,
  a: &CoreTerm,
  b: &CoreTerm,
  f1: &crate::Map<crate::term::Identifier, CoreTerm>,
  f2: &crate::Map<crate::term::Identifier, CoreTerm>,
) -> Result<(), UnifyError> {
  if f1.len() != f2.len() {
    return Err(mismatch(a.clone(), b.clone()));
  }
  for (k, v1) in f1.iter() {
    match f2.get(k) {
      Some(v2) => unify(mctx, v1, v2)?,
      None => return Err(mismatch(a.clone(), b.clone())),
    }
  }
  Ok(())
}

/// Open both sides of a binder's body with the *same* fresh `Free` atom
/// before comparing — the standard "compare under a binder" technique:
/// avoids ever needing to compare raw un-opened indices across the two
/// sides, which is where naive de-Bruijn implementations reintroduce
/// accidental bugs.
fn unify_under_binder(
  mctx: &mut MetaContext,
  b1: &CoreTerm,
  b2: &CoreTerm,
) -> Result<(), UnifyError> {
  let atom = Atom::fresh();
  let ob1 = open_with(b1, &CoreTerm::Free(atom));
  let ob2 = open_with(b2, &CoreTerm::Free(atom));
  unify(mctx, &ob1, &ob2)
}

// ---------------------------------------------------------------------------
// instantiate — replaces pi_of_forall_types_with_mult's textual Forall
// merge: opening with a fresh metavariable can never leak one call's
// variables into another's, since MetaIds are globally unique by
// construction.
// ---------------------------------------------------------------------------

/// Instantiate a `Forall { typ, body }` by substituting a fresh metavariable
/// (of type `typ`) for its bound variable in `body`. This is the
/// locally-nameless "open with a meta" operation used at every
/// application/call site that needs to use a polymorphic value — the
/// direct replacement for the old checker's `pi_of_forall_types_with_mult`
/// Forall-merge trick, which is what leaked one call's still-generic type
/// into another's expected-type position (the root cause traced in the
/// plan's Context section).
pub fn instantiate(mctx: &mut MetaContext, typ: &CoreTerm, body: &CoreTerm) -> CoreTerm {
  let m = mctx.fresh_meta(typ.clone());
  open_with(body, &CoreTerm::Meta(m))
}

// ---------------------------------------------------------------------------
// zonk — fully resolve every solved metavariable occurrence
// ---------------------------------------------------------------------------

/// Recursively replace every solved `Meta` in `term` with its solution.
/// Unsolved metavariables are left as-is. Replaces the old checker's
/// `substitute_forall`'s `~`-suffix-stripping hack, which had to guess
/// whether a name was a real binder or synthetic bookkeeping from string
/// shape alone.
pub fn zonk(mctx: &MetaContext, term: &CoreTerm) -> CoreTerm {
  match term {
    CoreTerm::Meta(m) => match mctx.lookup(*m) {
      Some(sol) => zonk(mctx, sol),
      None => term.clone(),
    },
    CoreTerm::Bound(_) | CoreTerm::Free(_) | CoreTerm::Sort { .. } | CoreTerm::Hole => term.clone(),
    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(zonk(mctx, typ)),
      body: Box::new(zonk(mctx, body)),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(zonk(mctx, arg)),
      ret: Box::new(zonk(mctx, ret)),
      mult: mult.clone(),
    },
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => CoreTerm::Lam {
      dbg: dbg.clone(),
      param_typ: Box::new(zonk(mctx, param_typ)),
      body: Box::new(zonk(mctx, body)),
    },
    CoreTerm::App { fun, arg } => CoreTerm::App {
      fun: Box::new(zonk(mctx, fun)),
      arg: Box::new(zonk(mctx, arg)),
    },
    CoreTerm::Lit(lit) => CoreTerm::Lit(zonk_lit(mctx, lit)),
    CoreTerm::Con(c) => CoreTerm::Con(CoreConstructor {
      name: c.name.clone(),
      typ_name: c.typ_name.clone(),
      num_args: c.num_args,
      args: zonk_args(mctx, &c.args),
    }),
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: zonk_args(mctx, &n.args),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(zonk(mctx, term)),
    },
  }
}

fn zonk_args(mctx: &MetaContext, args: &[Option<CoreTerm>]) -> Vec<Option<CoreTerm>> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| zonk(mctx, t)))
    .collect()
}

fn zonk_lit(mctx: &MetaContext, lit: &CoreLit) -> CoreLit {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      lit.clone()
    }
    CoreLit::Match { scrutinee, cases } => CoreLit::Match {
      scrutinee: Box::new(zonk(mctx, scrutinee)),
      cases: cases
        .iter()
        .map(|c| CoreMatchCase {
          name: c.name.clone(),
          dbgs: c.dbgs.clone(),
          value: Box::new(zonk(mctx, &c.value)),
        })
        .collect(),
    },
    CoreLit::If { cond, then, els } => CoreLit::If {
      cond: Box::new(zonk(mctx, cond)),
      then: Box::new(zonk(mctx, then)),
      els: Box::new(zonk(mctx, els)),
    },
    CoreLit::StructLit { fields, type_name } => CoreLit::StructLit {
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), zonk(mctx, v)))
        .collect(),
      type_name: *type_name,
    },
    CoreLit::StructUpdate { base, fields } => CoreLit::StructUpdate {
      base: Box::new(zonk(mctx, base)),
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), zonk(mctx, v)))
        .collect(),
    },
  }
}

// ---------------------------------------------------------------------------
// generalize — re-abstract any metavariables still unresolved at a
// generalization boundary (a top-level def's inferred type) as fresh
// Forall binders. The principled replacement for the old checker's
// keep_vars/add_forall_to_type name-based re-wrap.
// ---------------------------------------------------------------------------

/// Replace every occurrence of `Meta(target)` with `Bound(depth)` — mirrors
/// `crate::core_term`'s `close_at`, but closing over a metavariable
/// instead of an opened `Free` atom (used at generalization, where a
/// still-unresolved metavariable becomes a fresh `Forall` binder rather
/// than a previously-opened rigid variable becoming re-closed).
fn close_meta_at(term: &CoreTerm, depth: u32, target: MetaId) -> CoreTerm {
  match term {
    CoreTerm::Meta(m) if *m == target => CoreTerm::Bound(depth),
    CoreTerm::Bound(_)
    | CoreTerm::Free(_)
    | CoreTerm::Meta(_)
    | CoreTerm::Sort { .. }
    | CoreTerm::Hole => term.clone(),
    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(close_meta_at(typ, depth, target)),
      body: Box::new(close_meta_at(body, depth + 1, target)),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(close_meta_at(arg, depth, target)),
      ret: Box::new(close_meta_at(ret, depth + 1, target)),
      mult: mult.clone(),
    },
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => CoreTerm::Lam {
      dbg: dbg.clone(),
      param_typ: Box::new(close_meta_at(param_typ, depth, target)),
      body: Box::new(close_meta_at(body, depth + 1, target)),
    },
    CoreTerm::App { fun, arg } => CoreTerm::App {
      fun: Box::new(close_meta_at(fun, depth, target)),
      arg: Box::new(close_meta_at(arg, depth, target)),
    },
    CoreTerm::Lit(lit) => CoreTerm::Lit(close_meta_at_lit(lit, depth, target)),
    CoreTerm::Con(c) => CoreTerm::Con(CoreConstructor {
      name: c.name.clone(),
      typ_name: c.typ_name.clone(),
      num_args: c.num_args,
      args: close_meta_at_args(&c.args, depth, target),
    }),
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: close_meta_at_args(&n.args, depth, target),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(close_meta_at(term, depth, target)),
    },
  }
}

fn close_meta_at_args(
  args: &[Option<CoreTerm>],
  depth: u32,
  target: MetaId,
) -> Vec<Option<CoreTerm>> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| close_meta_at(t, depth, target)))
    .collect()
}

fn close_meta_at_lit(lit: &CoreLit, depth: u32, target: MetaId) -> CoreLit {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      lit.clone()
    }
    CoreLit::Match { scrutinee, cases } => CoreLit::Match {
      scrutinee: Box::new(close_meta_at(scrutinee, depth, target)),
      cases: cases
        .iter()
        .map(|c| CoreMatchCase {
          name: c.name.clone(),
          dbgs: c.dbgs.clone(),
          value: Box::new(close_meta_at(&c.value, depth + c.dbgs.len() as u32, target)),
        })
        .collect(),
    },
    CoreLit::If { cond, then, els } => CoreLit::If {
      cond: Box::new(close_meta_at(cond, depth, target)),
      then: Box::new(close_meta_at(then, depth, target)),
      els: Box::new(close_meta_at(els, depth, target)),
    },
    CoreLit::StructLit { fields, type_name } => CoreLit::StructLit {
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), close_meta_at(v, depth, target)))
        .collect(),
      type_name: *type_name,
    },
    CoreLit::StructUpdate { base, fields } => CoreLit::StructUpdate {
      base: Box::new(close_meta_at(base, depth, target)),
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), close_meta_at(v, depth, target)))
        .collect(),
    },
  }
}

/// Collect the `MetaId`s still unresolved in `term`, in first-occurrence
/// (pre-order) order, without duplicates.
fn unresolved_metas_in_order(mctx: &MetaContext, term: &CoreTerm, out: &mut Vec<MetaId>) {
  match term {
    CoreTerm::Meta(m) => {
      if !mctx.is_solved(*m) && !out.contains(m) {
        out.push(*m);
      }
    }
    CoreTerm::Bound(_) | CoreTerm::Free(_) | CoreTerm::Sort { .. } | CoreTerm::Hole => {}
    CoreTerm::Forall { typ, body, .. } => {
      unresolved_metas_in_order(mctx, typ, out);
      unresolved_metas_in_order(mctx, body, out);
    }
    CoreTerm::Pi { arg, ret, .. } => {
      unresolved_metas_in_order(mctx, arg, out);
      unresolved_metas_in_order(mctx, ret, out);
    }
    CoreTerm::Lam {
      param_typ, body, ..
    } => {
      unresolved_metas_in_order(mctx, param_typ, out);
      unresolved_metas_in_order(mctx, body, out);
    }
    CoreTerm::App { fun, arg } => {
      unresolved_metas_in_order(mctx, fun, out);
      unresolved_metas_in_order(mctx, arg, out);
    }
    CoreTerm::Lit(lit) => unresolved_metas_in_order_lit(mctx, lit, out),
    CoreTerm::Con(c) => unresolved_metas_in_order_args(mctx, &c.args, out),
    CoreTerm::Ntv(n) => unresolved_metas_in_order_args(mctx, &n.args, out),
    CoreTerm::Ctx { term, .. } => unresolved_metas_in_order(mctx, term, out),
  }
}

fn unresolved_metas_in_order_args(
  mctx: &MetaContext,
  args: &[Option<CoreTerm>],
  out: &mut Vec<MetaId>,
) {
  for a in args.iter().flatten() {
    unresolved_metas_in_order(mctx, a, out);
  }
}

fn unresolved_metas_in_order_lit(mctx: &MetaContext, lit: &CoreLit, out: &mut Vec<MetaId>) {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {}
    CoreLit::Match { scrutinee, cases } => {
      unresolved_metas_in_order(mctx, scrutinee, out);
      for c in cases {
        unresolved_metas_in_order(mctx, &c.value, out);
      }
    }
    CoreLit::If { cond, then, els } => {
      unresolved_metas_in_order(mctx, cond, out);
      unresolved_metas_in_order(mctx, then, out);
      unresolved_metas_in_order(mctx, els, out);
    }
    CoreLit::StructLit { fields, .. } => {
      for v in fields.values() {
        unresolved_metas_in_order(mctx, v, out);
      }
    }
    CoreLit::StructUpdate { base, fields } => {
      unresolved_metas_in_order(mctx, base, out);
      for v in fields.values() {
        unresolved_metas_in_order(mctx, v, out);
      }
    }
  }
}

/// Zonk `term`, then wrap it in a fresh `Forall` for every metavariable
/// still unresolved (in first-occurrence order — the first metavariable
/// encountered becomes the outermost `Forall`), using each metavariable's
/// recorded type (from `MetaContext::fresh_meta`) as the new binder's type.
/// This is the principled, index-correct replacement for the old checker's
/// `keep_vars`/`add_forall_to_type`: it operates on the actual set of
/// metavariables that occurred, not a name-based "is this identifier still
/// free in the term" scan.
pub fn generalize(
  mctx: &MetaContext,
  term: &CoreTerm,
  dbg_for: impl Fn(MetaId) -> crate::core_term::DebugName,
) -> CoreTerm {
  let zonked = zonk(mctx, term);
  let mut metas = Vec::new();
  unresolved_metas_in_order(mctx, &zonked, &mut metas);

  // Innermost binder first: the *last* meta in first-occurrence order
  // becomes the innermost (closest) Forall, so after processing all of
  // them in reverse, the *first*-encountered meta ends up outermost.
  let mut result = zonked;
  for m in metas.into_iter().rev() {
    let closed_body = close_meta_at(&result, 0, m);
    let typ = mctx
      .meta_type(m)
      .cloned()
      .unwrap_or(CoreTerm::Sort { level: 1 });
    // The meta's own recorded type may itself mention earlier (more-outer,
    // not-yet-closed) metas but cannot mention *later* (already-closed,
    // now-`Bound`) ones by construction (a meta's type is fixed at
    // creation time, before any inner metas exist) — so it needs no
    // closing here relative to `m` itself, only zonking against whatever
    // is solved so far.
    let typ = zonk(mctx, &typ);
    result = CoreTerm::Forall {
      dbg: dbg_for(m),
      typ: Box::new(typ),
      body: Box::new(closed_body),
    };
  }
  result
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::core_term::DebugName;
  use crate::term::{Identifier, Multiplicity};

  fn named(s: &str) -> DebugName {
    DebugName::Named(Identifier::new(s.to_string()))
  }

  fn sort1() -> CoreTerm {
    CoreTerm::Sort { level: 1 }
  }
  fn sort0() -> CoreTerm {
    CoreTerm::Sort { level: 0 }
  }

  fn non_dep_pi(arg: CoreTerm, ret: CoreTerm) -> CoreTerm {
    // ret doesn't reference the bound arg, so it's `Bound`-index-shifted
    // away by construction (never contains Bound(0)) — a plain `A -> B`.
    CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(arg),
      ret: Box::new(ret),
      mult: Multiplicity::Many,
    }
  }

  // -------------------------------------------------------------------
  // Basic unify behavior
  // -------------------------------------------------------------------

  #[test]
  fn test_unify_bound_same_index() {
    let mut mctx = MetaContext::new();
    assert!(unify(&mut mctx, &CoreTerm::Bound(0), &CoreTerm::Bound(0)).is_ok());
  }

  #[test]
  fn test_unify_bound_different_index_fails() {
    let mut mctx = MetaContext::new();
    assert!(unify(&mut mctx, &CoreTerm::Bound(0), &CoreTerm::Bound(1)).is_err());
  }

  #[test]
  fn test_unify_free_same_atom() {
    let mut mctx = MetaContext::new();
    let a = Atom::fresh();
    assert!(unify(&mut mctx, &CoreTerm::Free(a), &CoreTerm::Free(a)).is_ok());
  }

  #[test]
  fn test_unify_free_different_atom_fails() {
    let mut mctx = MetaContext::new();
    let a = Atom::fresh();
    let b = Atom::fresh();
    assert!(unify(&mut mctx, &CoreTerm::Free(a), &CoreTerm::Free(b)).is_err());
  }

  #[test]
  fn test_unify_meta_solves() {
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    unify(&mut mctx, &CoreTerm::Meta(m), &sort0()).unwrap();
    assert_eq!(mctx.lookup(m), Some(&sort0()));
  }

  // -------------------------------------------------------------------
  // unify: asymmetric Forall auto-instantiation (a still-polymorphic
  // type surfacing *inside* a structural comparison, e.g. nested in an
  // App's fun/arg position — not just at a top-level check/infer call,
  // the only place core_check::instantiate_foralls would otherwise run).
  // -------------------------------------------------------------------

  #[test]
  fn test_unify_instantiates_forall_nested_in_app_fun_position() {
    // App{fun: ({A} -> A -> Bool), arg: atom} vs App{fun: (atom2 -> Bool), arg: atom}
    // — fun's polymorphic Forall must auto-instantiate (A := atom2) for
    // the whole App/App comparison to succeed; without the fix, `unify`'s
    // App/App case recurses into unify(fun1, fun2) with no
    // instantiate_foralls step, and a bare (Forall, Pi) pair falls
    // straight to the catch-all Mismatch.
    let mut mctx = MetaContext::new();
    let atom = Atom::fresh();
    let poly_pred = CoreTerm::Forall {
      dbg: DebugName::Named(Identifier::new("A".to_string())),
      typ: Box::new(sort1()),
      body: Box::new(non_dep_pi(CoreTerm::Bound(0), sort0())),
    };
    let concrete_pred = non_dep_pi(CoreTerm::Free(atom), sort0());
    let left = CoreTerm::App {
      fun: Box::new(poly_pred),
      arg: Box::new(CoreTerm::Free(atom)),
    };
    let right = CoreTerm::App {
      fun: Box::new(concrete_pred),
      arg: Box::new(CoreTerm::Free(atom)),
    };
    assert!(
      unify(&mut mctx, &left, &right).is_ok(),
      "a Forall nested in App's fun position must auto-instantiate"
    );
  }

  #[test]
  fn test_unify_instantiates_forall_on_either_side() {
    let mut mctx = MetaContext::new();
    // {A:Type} -> A -> A   vs   Sort0 -> Sort0 : must unify (A := Sort0),
    // regardless of which side is the Forall.
    // `ret` is one binder deeper than `arg` (every Pi occupies a slot
    // for its return type), so the SAME outer Forall var referenced from
    // `ret` is Bound(1), not Bound(0) — see core_term.rs's depth
    // convention and the matching fixtures earlier in this file.
    let poly = CoreTerm::Forall {
      dbg: DebugName::Named(Identifier::new("A".to_string())),
      typ: Box::new(sort1()),
      body: Box::new(non_dep_pi(CoreTerm::Bound(0), CoreTerm::Bound(1))),
    };
    let concrete = non_dep_pi(sort0(), sort0());
    assert!(unify(&mut mctx, &poly.clone(), &concrete).is_ok());
    assert!(unify(&mut mctx, &concrete, &poly).is_ok());
  }

  #[test]
  fn test_occurs_check_rejects_self_reference() {
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    let self_referential = non_dep_pi(CoreTerm::Meta(m), sort0());
    let err = unify(&mut mctx, &CoreTerm::Meta(m), &self_referential).unwrap_err();
    assert!(matches!(err, UnifyError::OccursCheck { meta, .. } if meta == m));
  }

  #[test]
  fn test_unify_pi_different_mult_fails() {
    let mut mctx = MetaContext::new();
    let p1 = CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(sort0()),
      ret: Box::new(sort0()),
      mult: Multiplicity::Many,
    };
    let p2 = CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(sort0()),
      ret: Box::new(sort0()),
      mult: Multiplicity::Linear,
    };
    assert!(unify(&mut mctx, &p1, &p2).is_err());
  }

  // -------------------------------------------------------------------
  // Regression fixtures — the exact bug shapes that broke the old,
  // name-keyed checker (four failed local-patch attempts across a prior
  // session). Reproduced here at the CoreTerm level: two unrelated
  // generics both using type-parameter position 0, instantiated via
  // metavariables, must never cross-contaminate — because metavariable
  // identity is a MetaId, not a name, cross-contamination isn't even
  // representable.
  // -------------------------------------------------------------------

  /// `List.any : {A : Type} -> (A -> Bool) -> (List A -> Bool)`, as a
  /// CoreTerm Forall (single implicit param, matching the real function's
  /// shape from std/list.mo).
  fn list_any_type() -> CoreTerm {
    // {A : Type} -> (A -> Bool) -> (A -> Bool)
    // ("List A" is stood in for by bare `A` here — Con/App aren't modeled
    // in CoreTerm yet, Phase 2+ — the point of this fixture is purely the
    // binder/metavariable-identity behavior, not an accurate List shape.
    // The `ret` branch's `Bound(1)` (not `Bound(0)`) is deliberate: it's
    // one level deeper than the outer Pi's `arg`, since every Pi's `ret`
    // is under one more binder than its `arg` — see
    // test_open_close_round_trip_nested_binder in core_term.rs.)
    CoreTerm::Forall {
      dbg: named("A"),
      typ: Box::new(sort1()),
      body: Box::new(non_dep_pi(
        non_dep_pi(CoreTerm::Bound(0), sort0()), // pred : A -> Bool
        non_dep_pi(CoreTerm::Bound(1), sort0()), // stand-in for List A -> Bool
      )),
    }
  }

  #[test]
  fn test_two_unrelated_generic_instantiations_do_not_cross_contaminate() {
    // The actual bug: `List.any`'s own generic `A` (instantiated to solve
    // for `String`, from the `pred : String -> Bool` argument) must never
    // leak into or collide with a *different*, unrelated instantiation of
    // a same-named `A` from another generic function used nearby (e.g.
    // `BTreeMap`'s `K`/`V`, both also just called `A` in this reduced
    // fixture). Old checker: both were tracked in one name-keyed
    // `FreeVars.vars: Map<&Identifier, FreeVar>`, so both `A`s shared a
    // slot. New checker: each instantiation gets its own `MetaId`.
    let mut mctx = MetaContext::new();

    let list_any = list_any_type();
    let other_generic = list_any_type(); // same shape, same name "A" — an unrelated call

    let (typ1, body1) = match &list_any {
      CoreTerm::Forall { typ, body, .. } => (typ.as_ref(), body.as_ref()),
      _ => unreachable!(),
    };
    let (typ2, body2) = match &other_generic {
      CoreTerm::Forall { typ, body, .. } => (typ.as_ref(), body.as_ref()),
      _ => unreachable!(),
    };

    let inst1 = instantiate(&mut mctx, typ1, body1);
    let inst2 = instantiate(&mut mctx, typ2, body2);

    // Solve instantiation 1's `A` against `Free(string_atom)` (standing in
    // for "String") by unifying its `pred : A -> Bool` position.
    let string_atom = Atom::fresh();
    let pred1_expected = non_dep_pi(CoreTerm::Free(string_atom), sort0());
    let pred1_actual = match &inst1 {
      CoreTerm::Pi { arg, .. } => arg.as_ref().clone(),
      _ => unreachable!(),
    };
    unify(&mut mctx, &pred1_actual, &pred1_expected).unwrap();

    // Solve instantiation 2's `A` against a completely different atom
    // ("Bool", say) — an unrelated call to the same-shaped generic.
    let bool_atom = Atom::fresh();
    let pred2_expected = non_dep_pi(CoreTerm::Free(bool_atom), sort0());
    let pred2_actual = match &inst2 {
      CoreTerm::Pi { arg, .. } => arg.as_ref().clone(),
      _ => unreachable!(),
    };
    unify(&mut mctx, &pred2_actual, &pred2_expected).unwrap();

    // The two instantiations' metavariables must have resolved
    // independently — no shared name-keyed slot exists to conflate them.
    let zonked1 = zonk(&mctx, &inst1);
    let zonked2 = zonk(&mctx, &inst2);
    assert_ne!(
      zonked1, zonked2,
      "the two instantiations must resolve independently"
    );

    match &zonked1 {
      CoreTerm::Pi { arg, .. } => {
        assert_eq!(**arg, non_dep_pi(CoreTerm::Free(string_atom), sort0()))
      }
      _ => panic!("expected Pi"),
    }
    match &zonked2 {
      CoreTerm::Pi { arg, .. } => assert_eq!(**arg, non_dep_pi(CoreTerm::Free(bool_atom), sort0())),
      _ => panic!("expected Pi"),
    }
  }

  #[test]
  fn test_instantiate_forall_then_unify_pipe_shape() {
    // Simplified analogue of the std/list.mo pipe bug: `List.any pred`
    // is a partial application whose remaining type is still
    // Forall-wrapped until unified against the concrete list type. Old
    // checker: merging that leftover Forall into the outer expected type
    // via `pi_of_forall_types_with_mult` leaked it into an unrelated
    // position. New checker: instantiating with a fresh meta and
    // unifying directly against the known concrete type solves it in
    // one step, no merge/leak possible.
    let mut mctx = MetaContext::new();
    // {A : Type} -> List A -> Bool   (List A modeled as Pi(A, Bool) stand-in)
    let partial_app_type = CoreTerm::Forall {
      dbg: named("A"),
      typ: Box::new(sort1()),
      body: Box::new(non_dep_pi(CoreTerm::Bound(0), sort0())),
    };
    let (typ, body) = match &partial_app_type {
      CoreTerm::Forall { typ, body, .. } => (typ.as_ref(), body.as_ref()),
      _ => unreachable!(),
    };
    let instantiated = instantiate(&mut mctx, typ, body); // (Meta(m) -> Bool)

    let string_atom = Atom::fresh();
    let concrete_expected = non_dep_pi(CoreTerm::Free(string_atom), sort0()); // String -> Bool
    unify(&mut mctx, &instantiated, &concrete_expected).unwrap();

    let solved_arg = match &instantiated {
      CoreTerm::Pi { arg, .. } => match arg.as_ref() {
        CoreTerm::Meta(m) => mctx.lookup(*m).cloned().unwrap(),
        _ => unreachable!(),
      },
      _ => unreachable!(),
    };
    assert_eq!(solved_arg, CoreTerm::Free(string_atom));
  }

  // -------------------------------------------------------------------
  // zonk
  // -------------------------------------------------------------------

  #[test]
  fn test_zonk_resolves_nested_and_chained_metas() {
    let mut mctx = MetaContext::new();
    let m1 = mctx.fresh_meta(sort1());
    let m2 = mctx.fresh_meta(sort1());
    // m1 solved to m2, m2 solved to Sort 0 — zonk must chase the chain.
    unify(&mut mctx, &CoreTerm::Meta(m1), &CoreTerm::Meta(m2)).unwrap();
    unify(&mut mctx, &CoreTerm::Meta(m2), &sort0()).unwrap();

    let term = non_dep_pi(CoreTerm::Meta(m1), sort0());
    assert_eq!(zonk(&mctx, &term), non_dep_pi(sort0(), sort0()));
  }

  #[test]
  fn test_zonk_leaves_unsolved_metas() {
    let mctx = MetaContext::new();
    let m = MetaId::fresh(); // never registered/solved
    assert_eq!(zonk(&mctx, &CoreTerm::Meta(m)), CoreTerm::Meta(m));
  }

  // -------------------------------------------------------------------
  // generalize
  // -------------------------------------------------------------------

  #[test]
  fn test_generalize_wraps_single_unresolved_meta_as_forall() {
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    let term = non_dep_pi(CoreTerm::Meta(m), CoreTerm::Meta(m)); // A -> A, unresolved

    let generalized = generalize(&mctx, &term, |_| named("A"));
    match generalized {
      CoreTerm::Forall { dbg, typ, body } => {
        assert_eq!(dbg.as_str(), "A");
        assert_eq!(*typ, sort1());
        // `ret` is one binder deeper than `arg` (every `Pi` introduces a
        // binder slot for its return type), so the same outer variable
        // referenced from `ret` is `Bound(1)`, not `Bound(0)`.
        assert_eq!(*body, non_dep_pi(CoreTerm::Bound(0), CoreTerm::Bound(1)));
      }
      other => panic!("expected Forall, got {other}"),
    }
  }

  #[test]
  fn test_generalize_after_partial_solve_only_wraps_remaining() {
    let mut mctx = MetaContext::new();
    let m1 = mctx.fresh_meta(sort1());
    let m2 = mctx.fresh_meta(sort1());
    unify(&mut mctx, &CoreTerm::Meta(m1), &sort0()).unwrap(); // m1 resolved
    // m2 stays unresolved.
    let term = non_dep_pi(CoreTerm::Meta(m1), CoreTerm::Meta(m2));

    let generalized = generalize(&mctx, &term, |_| named("B"));
    match generalized {
      CoreTerm::Forall { dbg, body, .. } => {
        assert_eq!(dbg.as_str(), "B");
        // m1 zonked away to Sort 0; m2 closed over as the new binder,
        // referenced as Bound(1) from `ret`'s one-level-deeper position.
        assert_eq!(*body, non_dep_pi(sort0(), CoreTerm::Bound(1)));
      }
      other => panic!("expected Forall, got {other}"),
    }
  }

  #[test]
  fn test_generalize_multiple_metas_outer_to_inner_in_first_occurrence_order() {
    let mut mctx = MetaContext::new();
    let m1 = mctx.fresh_meta(sort1());
    let m2 = mctx.fresh_meta(sort1());
    // term: m1 -> m2 (m1 encountered first, should end up OUTERMOST forall)
    let term = non_dep_pi(CoreTerm::Meta(m1), CoreTerm::Meta(m2));

    let generalized = generalize(
      &mctx,
      &term,
      |m| if m == m1 { named("A") } else { named("B") },
    );
    match &generalized {
      CoreTerm::Forall { dbg, body, .. } => {
        assert_eq!(dbg.as_str(), "A");
        match body.as_ref() {
          CoreTerm::Forall { dbg, body, .. } => {
            assert_eq!(dbg.as_str(), "B");
            // `arg` sits at the Pi's own depth: A (outer, 2 binders out
            // from here) is Bound(1) (skipping the nearer B). `ret` sits
            // one level deeper (Pi's own implicit binder slot), so from
            // there B (the nearer binder) is also Bound(1) — see
            // test_generalize_after_partial_solve_only_wraps_remaining.
            assert_eq!(**body, non_dep_pi(CoreTerm::Bound(1), CoreTerm::Bound(1)));
          }
          other => panic!("expected inner Forall, got {other}"),
        }
      }
      other => panic!("expected outer Forall, got {other}"),
    }
  }

  // -------------------------------------------------------------------
  // unify: Lit / Con / Match — the extended scope
  // -------------------------------------------------------------------

  fn str_lit(s: &str) -> CoreTerm {
    CoreTerm::Lit(CoreLit::Str {
      value: s.to_string(),
    })
  }

  #[test]
  fn test_unify_str_literals() {
    let mut mctx = MetaContext::new();
    assert!(unify(&mut mctx, &str_lit("a"), &str_lit("a")).is_ok());
    assert!(unify(&mut mctx, &str_lit("a"), &str_lit("b")).is_err());
  }

  #[test]
  fn test_unify_str_literal_solves_meta() {
    // A metavariable unified against a concrete literal must solve to it —
    // same as any other shape, confirming Lit doesn't bypass the Meta arm.
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    unify(&mut mctx, &CoreTerm::Meta(m), &str_lit("hi")).unwrap();
    assert_eq!(mctx.lookup(m), Some(&str_lit("hi")));
  }

  fn cons(head: CoreTerm, tail: CoreTerm) -> CoreTerm {
    CoreTerm::Con(CoreConstructor {
      name: Identifier::new("cons".to_string()),
      typ_name: crate::term::ModulePath::top("List"),
      num_args: 2,
      args: vec![Some(head), Some(tail)],
    })
  }

  #[test]
  fn test_unify_con_same_shape_unifies_args_pairwise() {
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    let a = cons(CoreTerm::Meta(m), str_lit("tail"));
    let b = cons(sort0(), str_lit("tail"));
    unify(&mut mctx, &a, &b).unwrap();
    assert_eq!(mctx.lookup(m), Some(&sort0()));
  }

  #[test]
  fn test_unify_con_different_constructor_name_fails() {
    let mut mctx = MetaContext::new();
    let a = cons(sort0(), sort0());
    let b = CoreTerm::Con(CoreConstructor {
      name: Identifier::new("empty".to_string()),
      typ_name: crate::term::ModulePath::top("List"),
      num_args: 0,
      args: vec![],
    });
    assert!(unify(&mut mctx, &a, &b).is_err());
  }

  fn match_case(name: &str, arity: usize, value: CoreTerm) -> CoreMatchCase {
    CoreMatchCase {
      name: Identifier::new(name.to_string()),
      dbgs: (0..arity).map(|_| DebugName::Anonymous).collect(),
      value: Box::new(value),
    }
  }

  #[test]
  fn test_unify_match_same_shape_opens_cases_with_same_atoms() {
    // match s1 { cons a t => a } vs match s2 { cons a t => a } — same
    // shape, scrutinees unify via a shared meta, case bodies unify
    // trivially since both reference their OWN case's first pattern var.
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    let a = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(CoreTerm::Meta(m)),
      cases: vec![match_case("cons", 2, CoreTerm::Bound(1))],
    });
    let b = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(sort0()),
      cases: vec![match_case("cons", 2, CoreTerm::Bound(1))],
    });
    assert!(unify(&mut mctx, &a, &b).is_ok());
    assert_eq!(mctx.lookup(m), Some(&sort0()));
  }

  #[test]
  fn test_unify_match_different_case_bodies_fail() {
    let mut mctx = MetaContext::new();
    let a = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(sort0()),
      cases: vec![match_case("cons", 2, CoreTerm::Bound(1))], // refs outer arg
    });
    let b = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(sort0()),
      cases: vec![match_case("cons", 2, CoreTerm::Bound(0))], // refs inner arg
    });
    assert!(unify(&mut mctx, &a, &b).is_err());
  }

  #[test]
  fn test_unify_match_different_arity_fails() {
    let mut mctx = MetaContext::new();
    let a = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(sort0()),
      cases: vec![match_case("cons", 2, sort0())],
    });
    let b = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(sort0()),
      cases: vec![match_case("cons", 1, sort0())],
    });
    assert!(unify(&mut mctx, &a, &b).is_err());
  }

  #[test]
  fn test_occurs_check_reaches_into_con_args() {
    let mut mctx = MetaContext::new();
    let m = mctx.fresh_meta(sort1());
    let self_referential = cons(CoreTerm::Meta(m), sort0());
    let err = unify(&mut mctx, &CoreTerm::Meta(m), &self_referential).unwrap_err();
    assert!(matches!(err, UnifyError::OccursCheck { meta, .. } if meta == m));
  }
}
