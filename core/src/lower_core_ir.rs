//! `CoreTerm -> CoreIr` lowering — Phase 2 of
//! `plans/implementations/core-term-closure-evaluator.md`.
//!
//! Consumes a whole-program `CoreProgram` (Phase 0) instead of a
//! `Scope`/`Term` the way `lower.rs`'s `Term -> EvalTerm` pass does.
//! Deliberately smaller in scope than that pass: de Bruijn indices are
//! already computed by `CoreTerm` (a `Bound(i)` lowers to `Local(i)`
//! unchanged — no index recomputation, and no `open_at`/`open_n`
//! either, since lowering only needs to preserve the existing index
//! *structure*, not inspect it the way the checker's unification does),
//! and dictionary-passing is already baked in as plain `Free`/`Match`
//! nodes (nothing class/instance-dispatch-specific needs reinventing
//! here).

use crate::Map;
use crate::core_ir::{self, CoreIr, IrLit, IrRef, MatchArm};
use crate::core_program::CoreProgram;
use crate::core_term::{Atom, CoreConstructor, CoreLit, CoreNative, CoreTerm};
use crate::term::{Identifier, ModulePath, mpt};

/// Shift every `Local` reference in `ir` that resolves OUTSIDE `ir`'s own
/// locally-bound scope (i.e. `>= cutoff`) up by `delta` — the standard de
/// Bruijn "open a gap" operation, applied once at lowering time (not on
/// every `eval`, which stays subst/shift-free per this module's own doc
/// comment). Needed by `lower_match`'s wildcard-arm reuse: a wildcard
/// case's source pattern (`_`) always binds zero names, so its body was
/// lowered assuming NO extra frames sit between it and its enclosing
/// scope — but `dispatch` (`core_eval.rs`) unconditionally pushes one
/// frame per field of whichever constructor tag actually matched before
/// running that body, for every tag the wildcard covers. Reusing the
/// SAME body unchanged across tags with different arities (an earlier
/// version of this function did, reasoning "the body never reads those
/// extra bindings, so it's fine") is wrong: it doesn't matter whether the
/// body ever reads the extra bindings — every `Local` reference the body
/// makes to something OUTSIDE its own binder scope still needs to skip
/// past them once they're actually there, exactly like opening any other
/// binder. `Local`s bound *within* `ir` (by a nested `Lam` or `Match`
/// arm) are left alone; only `cutoff` advances as the walk descends past
/// each of those.
fn shift_ir(ir: &IrRef, cutoff: u32, delta: u32) -> IrRef {
  if delta == 0 {
    return ir.clone();
  }
  match ir.as_ref() {
    CoreIr::Local(i) => {
      if *i >= cutoff {
        std::sync::Arc::new(CoreIr::Local(i + delta))
      } else {
        ir.clone()
      }
    }
    CoreIr::Global(_) | CoreIr::Lit(_) | CoreIr::MatchFail { .. } => ir.clone(),
    CoreIr::Lam { body } => std::sync::Arc::new(CoreIr::Lam {
      body: shift_ir(body, cutoff + 1, delta),
    }),
    CoreIr::App { fun, arg } => std::sync::Arc::new(CoreIr::App {
      fun: shift_ir(fun, cutoff, delta),
      arg: shift_ir(arg, cutoff, delta),
    }),
    CoreIr::Match { scrutinee, arms } => std::sync::Arc::new(CoreIr::Match {
      scrutinee: shift_ir(scrutinee, cutoff, delta),
      arms: arms
        .iter()
        .map(|arm| MatchArm {
          bind_count: arm.bind_count,
          body: shift_ir(&arm.body, cutoff + arm.bind_count, delta),
        })
        .collect(),
    }),
    CoreIr::Con { tag, arity, args } => std::sync::Arc::new(CoreIr::Con {
      tag: *tag,
      arity: *arity,
      args: args.iter().map(|a| shift_ir(a, cutoff, delta)).collect(),
    }),
    CoreIr::Ntv { native_id, args } => std::sync::Arc::new(CoreIr::Ntv {
      native_id: *native_id,
      args: args.iter().map(|a| shift_ir(a, cutoff, delta)).collect(),
    }),
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LowerCoreIrError {
  /// A `Free(Atom)` with no entry in the current def's own `atom_paths`
  /// — should never happen for a term that came from a successful
  /// checker run; indicates a Phase 0 capture bug if it does.
  UnresolvedAtom(Atom),
  /// A `Match`/`if` node with no captured resolution — either capture
  /// wasn't enabled when this def was checked, or (for `if`) `Bool`
  /// itself wasn't registered in `CoreProgram.inductives`.
  UnresolvedMatch,
  /// The lowering pass's traversal order diverged from the checker's own
  /// — popped a resolution whose case names don't match the `Match`
  /// node being lowered. Indicates a real bug (the two traversals must
  /// visit `Match`/`if`/`StructUpdate` nodes in the same left-to-right
  /// order for the queue-based association in
  /// `CoreProgram::match_resolutions` to be correct), not something to
  /// paper over.
  MatchTraversalMismatch {
    expected: Vec<Identifier>,
    found: Vec<Identifier>,
  },
  UnknownInductive(ModulePath),
  UnknownConstructor(ModulePath, Identifier),
  /// A `match`/`if` doesn't cover one of the scrutinee's inductive's
  /// constructors and has no wildcard (`_`) case either — a genuinely
  /// malformed program (the checker should have rejected it), not
  /// something to guess a fallback for.
  NonExhaustiveMatch(ModulePath, Identifier),
  /// A `CoreConstructor`/`CoreNative`'s `args` has a `Some` after a
  /// `None` — not just-a-prefix-applied, which is the only shape
  /// ordinary left-to-right `CoreTerm::App` chains can produce. Treated
  /// as an error rather than silently reordering/dropping args.
  SparseArgs(ModulePath, Identifier),
  SparseNativeArgs(Identifier),
  /// `Meta`/`Forall`/`Pi`/`Sort`/`Hole` reached lowering — type-level or
  /// pre-zonk constructs that should never appear inside a checked def's
  /// *value* body.
  UnexpectedTypeLevelTerm(&'static str),
  /// A `StructLit`/`StructUpdate` whose `type_name` doesn't resolve to a
  /// registered single-constructor inductive, or supplies a field name
  /// the struct doesn't declare.
  UnknownStruct(Atom),
  UnknownStructField(ModulePath, Identifier),
  /// A global slot got interned (referenced from somewhere) but never
  /// resolved to a def, instance, or constructor — indicates either a
  /// gap in `CoreProgram`'s capture (e.g. a def that exists in the real
  /// program but whose module wasn't included in the set checked by
  /// `check_all_modules_capturing_core`) or a genuine unresolved name
  /// that should have been rejected by the checker already.
  UnresolvedGlobal(ModulePath),
}

/// Lazily assigns flat indices to global paths, in first-sight order —
/// the whole-program analogue of `core_term::AtomTable`'s own pattern.
#[derive(Debug, Default)]
pub struct GlobalInterner {
  indices: Map<ModulePath, u32>,
  order: Vec<ModulePath>,
}

impl GlobalInterner {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn intern(&mut self, path: ModulePath) -> u32 {
    if let Some(&idx) = self.indices.get(&path) {
      return idx;
    }
    let idx = self.order.len() as u32;
    self.indices.insert(path.clone(), idx);
    self.order.push(path);
    idx
  }

  /// Every path interned so far, in index order (index `i` is at
  /// position `i`) — used by whole-program assembly to resolve each
  /// slot's actual definition.
  pub fn paths(&self) -> &[ModulePath] {
    &self.order
  }
}

/// Per-def lowering context. `atom_paths` and `match_queue` are swapped
/// out per def (each def's own atoms/match resolutions are only
/// meaningful within that def's own check — see
/// `core_program::CheckedCoreDef`'s and
/// `CoreProgram::match_resolutions`'s doc comments); `interner`/
/// `natives` accumulate across the whole program.
pub struct LowerCtx<'a> {
  pub program: &'a CoreProgram,
  pub interner: &'a mut GlobalInterner,
  pub natives: &'a mut Map<Identifier, u32>,
  pub native_order: &'a mut Vec<Identifier>,
  /// Index = the same `native_id` `natives`/`native_order` use — the
  /// fixed number of args a native needs before `core_eval`'s
  /// `exec_native` (Phase 5) may fire it. Captured once, from the
  /// `CoreNative` node's own `num_args`, the first time each native name
  /// is interned (mirrors `lower.rs`'s `prim_arities`) — `CoreIr::Ntv`
  /// itself carries no arity (unlike `CoreIr::Con`, which does), since a
  /// native's arity is a whole-program-constant property of the native
  /// itself, not of any one call site.
  pub native_arities: &'a mut Vec<u32>,
  pub atom_paths: &'a Map<Atom, ModulePath>,
  /// This def's own `Match`/`if` resolutions, in the same left-to-right
  /// order `check`/`infer` visited them — consumed front-to-back as
  /// `lower_term` visits `Match`/`StructUpdate` nodes in that same
  /// order. A mismatch here (empty queue when one is expected, or a
  /// popped entry whose case names don't match the node being lowered)
  /// indicates the two traversals actually diverged and is checked for,
  /// not silently ignored.
  pub match_queue: std::collections::VecDeque<(Vec<Identifier>, Atom)>,
}

impl<'a> LowerCtx<'a> {
  fn pop_match_resolution(&mut self, case_names: &[Identifier]) -> Result<Atom, LowerCoreIrError> {
    let (queued_names, atom) = self
      .match_queue
      .pop_front()
      .ok_or(LowerCoreIrError::UnresolvedMatch)?;
    if queued_names != case_names {
      return Err(LowerCoreIrError::MatchTraversalMismatch {
        expected: case_names.to_vec(),
        found: queued_names,
      });
    }
    Ok(atom)
  }
}

impl<'a> LowerCtx<'a> {
  fn intern_native(&mut self, name: &Identifier, num_args: usize) -> u32 {
    if let Some(&id) = self.natives.get(name) {
      return id;
    }
    let id = self.native_order.len() as u32;
    self.natives.insert(name.clone(), id);
    self.native_order.push(name.clone());
    self.native_arities.push(num_args as u32);
    id
  }
}

/// Recognizes a fully-applied class-method/struct-field-projection call
/// spine: fully unwind `term`'s `App` chain (collecting each argument,
/// left to right) and check whether the resulting base is
/// `project_dict_field`'s exact output shape (`core_check.rs`) — a
/// single-case `Match`. Deliberately does NOT also require the
/// scrutinee to be a bare `Free` (an earlier version did): a
/// non-parametric class method's dictionary (`BEq`/`Append` over a
/// concrete type like `I64`/`String`) does scrutinize a bare
/// `Free(dict_atom)`, but a GENERIC/type-constructor-parameterized
/// class's dictionary (`Foldable`/`FromListLiteral` over `List`) needs
/// its instance resolved via a more complex expression first — a real
/// example that surfaced this: `Foldable.foldl f acc [1,2,3]` (a
/// `FromListLiteral` call nested inside `Foldable`'s own third
/// argument) failed with the bare-`Free` check in place. Just checking
/// `cases.len() == 1` is safe even though it's broader: an ordinary
/// (non-dict) ambient match is never itself the base of an `App` spine
/// unless its *result* is a function being called directly — a rare
/// shape — and misclassifying it here fails LOUDLY (a
/// `MatchTraversalMismatch`, not a silently wrong answer), same as any
/// other traversal-order bug this whole family of fixes addresses.
fn dict_projection_spine(term: &CoreTerm) -> Option<(&CoreTerm, Vec<&CoreTerm>)> {
  let mut args = Vec::new();
  let mut head = term;
  while let CoreTerm::App { fun, arg } = head.strip_ctx() {
    args.push(arg.as_ref());
    head = fun.as_ref();
  }
  args.reverse();
  match head.strip_ctx() {
    CoreTerm::Lit(CoreLit::Match { cases, .. }) if cases.len() == 1 => Some((head, args)),
    _ => None,
  }
}

/// Lower one def's/instance-method's checked body. `Bound`/`Free`
/// indices and dictionary-passing structure carry straight through — see
/// this module's doc comment.
pub fn lower_term(ctx: &mut LowerCtx, term: &CoreTerm) -> Result<CoreIr, LowerCoreIrError> {
  match term {
    CoreTerm::Bound(i) => Ok(core_ir::local(*i)),
    CoreTerm::Free(atom) => {
      let path = ctx
        .atom_paths
        .get(atom)
        .cloned()
        .ok_or(LowerCoreIrError::UnresolvedAtom(*atom))?;
      Ok(core_ir::global(ctx.interner.intern(path)))
    }
    CoreTerm::Meta(_) => Err(LowerCoreIrError::UnexpectedTypeLevelTerm("Meta")),
    CoreTerm::Forall { .. } => Err(LowerCoreIrError::UnexpectedTypeLevelTerm("Forall")),
    CoreTerm::Pi { .. } => Err(LowerCoreIrError::UnexpectedTypeLevelTerm("Pi")),
    // `Type`/`Prop`/`Pred`/`Sort n` used in ordinary VALUE position (e.g.
    // `get_sort Type`, `get_identity Prop` -- functions that take a
    // universe as an argument and hand it back unchanged, never actually
    // inspecting its structure). `CoreIr`/`Value` otherwise have no
    // concept of universes at all (by design -- see this module's own
    // doc comment on what's deliberately excluded), but an opaque,
    // structurally-inert `IrLit::Sort(level)` is enough for a `Sort` to
    // flow through locals/`App`/identity functions correctly without
    // needing any REAL runtime universe machinery, the same way an
    // uninspected `Str`/`Num` literal flows through unexamined -- a real
    // gap found running `init/tests.mo`'s own `test_sort_formation`/
    // `test_type_as_value_arg`/etc. through Phase 8's parity harness.
    CoreTerm::Sort { level } => Ok(CoreIr::Lit(IrLit::Sort(*level))),
    CoreTerm::Hole => Err(LowerCoreIrError::UnexpectedTypeLevelTerm("Hole")),
    CoreTerm::Lam { body, .. } => Ok(core_ir::lam(lower_term(ctx, body)?)),
    // `let x := value in body` (and any other beta-redex-shaped `App`)
    // desugars to `App(Lam(body), value)` — and `desugar_struct_literals`'s
    // own `App` arm (`core_check.rs`) special-cases exactly this shape,
    // desugaring `arg` (the let-bound VALUE) BEFORE `fun`'s body (matching
    // `let`'s natural evaluation order), the OPPOSITE of the generic
    // fun-then-arg order below. Lowering has to match that same order for
    // the match-resolution queue to line up — an earlier version of this
    // arm didn't special-case this, and desynced the queue for any `let`
    // whose bound value AND body both involved a dictionary-projected
    // class method (a real, previously-uncaught example: `init/init.mo`'s
    // `List.get`, whose body is `let b := index == 0 in (match l {...})`).
    CoreTerm::App { .. } if dict_projection_spine(term).is_some() => {
      // A class-method (or struct-field-projection) call site:
      // `desugar_struct_literals`'s `App` arm (`core_check.rs`) doesn't
      // recurse into `fun`/`arg` one level at a time for these — it
      // resolves the WHOLE spine via `try_resolve_class_method`, which
      // desugars every spine argument FIRST, and only THEN wraps the
      // call in `project_dict_field`'s single-arm `Match{scrutinee:
      // Free(dict_atom), cases: [class_name]}` (recorded into the queue
      // at that point) — args-first, self-last, the same "recurse first,
      // capture self last" convention `let`/`if`/ordinary `match` all
      // follow. The GENERIC fallback below (fun-then-arg) gets this
      // backwards for exactly this shape: naively unwinding one `App`
      // layer at a time reaches the dict-projection `Match` (sitting at
      // the spine's base, i.e. innermost `fun`) *before* any argument
      // nested further out in `arg` position — desyncing the queue for
      // any expression combining two class methods, e.g. `"a" ++ "b" ==
      // "ab"` (`Append.append` nested inside `BEq.beq`'s own first arg).
      // `dict_projection_spine` recognizes this exact shape (the base of
      // a fully-unwound `App` spine is a single-case `Match` over a bare
      // `Free`) and lowers every argument, left to right, before the
      // head.
      let (head, args) = dict_projection_spine(term).expect("checked above");
      let mut arg_irs = Vec::with_capacity(args.len());
      for a in args {
        arg_irs.push(lower_term(ctx, a)?);
      }
      let head_ir = lower_term(ctx, head)?;
      Ok(arg_irs.into_iter().fold(head_ir, core_ir::app))
    }
    // `let x := value in body` (and any other beta-redex-shaped `App`)
    // desugars to `App(Lam(body), value)` — and `desugar_struct_literals`'s
    // own `App` arm (`core_check.rs`) special-cases exactly this shape,
    // desugaring `arg` (the let-bound VALUE) BEFORE `fun`'s body (matching
    // `let`'s natural evaluation order), the OPPOSITE of the generic
    // fun-then-arg order below. Lowering has to match that same order for
    // the match-resolution queue to line up — an earlier version of this
    // arm didn't special-case this, and desynced the queue for any `let`
    // whose bound value AND body both involved a dictionary-projected
    // class method (a real, previously-uncaught example: `init/init.mo`'s
    // `List.get`, whose body is `let b := index == 0 in (match l {...})`).
    CoreTerm::App { fun, arg } => match fun.as_ref().strip_ctx() {
      CoreTerm::Lam { body: lam_body, .. } => {
        let arg_ir = lower_term(ctx, arg)?;
        let body_ir = lower_term(ctx, lam_body)?;
        Ok(core_ir::app(core_ir::lam(body_ir), arg_ir))
      }
      _ => Ok(core_ir::app(lower_term(ctx, fun)?, lower_term(ctx, arg)?)),
    },
    CoreTerm::Lit(lit) => lower_lit(ctx, lit),
    CoreTerm::Con(c) => lower_con(ctx, c),
    CoreTerm::Ntv(n) => lower_ntv(ctx, n),
    // A source-location wrapper — transparent for lowering, same as
    // `infer`/`check`'s own pass-through (`core_check.rs`). Recursing
    // through the same `lower_term` entry point means a `Match` node
    // hiding behind a `Ctx` wrapper is still reached (and its queued
    // resolution still consumed) exactly where it would be if the
    // wrapper weren't there.
    CoreTerm::Ctx { term, .. } => lower_term(ctx, term),
  }
}

fn lower_lit(ctx: &mut LowerCtx, lit: &CoreLit) -> Result<CoreIr, LowerCoreIrError> {
  match lit {
    CoreLit::Str { value } => Ok(core_ir::lit(IrLit::Str(value.clone()))),
    CoreLit::Char { value } => Ok(core_ir::lit(IrLit::Char(*value))),
    CoreLit::Num { value, suffix } => Ok(core_ir::lit(IrLit::Num(*value, *suffix))),
    CoreLit::Float { value, suffix } => Ok(core_ir::lit(IrLit::Float(*value, *suffix))),
    CoreLit::If { cond, then, els } => lower_if(ctx, cond, then, els),
    CoreLit::Match { scrutinee, cases } => lower_match(ctx, scrutinee, cases),
    CoreLit::StructLit { fields, type_name } => lower_struct_lit(ctx, fields, *type_name),
    CoreLit::StructUpdate { base, fields } => lower_struct_update(ctx, base, fields),
  }
}

/// `if` compiles through the same `Match`/tag-dispatch mechanism as an
/// ordinary `match` — not a separate IR variant — against `Bool`'s own
/// declared constructor order (not assumed/hardcoded, since a checker
/// change could reorder `true`/`false` in the prelude).
fn lower_if(
  ctx: &mut LowerCtx,
  cond: &CoreTerm,
  then: &CoreTerm,
  els: &CoreTerm,
) -> Result<CoreIr, LowerCoreIrError> {
  let bool_path = mpt("Bool");
  let info = ctx
    .program
    .inductives
    .get(&bool_path)
    .ok_or_else(|| LowerCoreIrError::UnknownInductive(bool_path.clone()))?;
  // Order matters here, same as `lower_match`: `desugar_struct_literals`'s
  // own `If` arm (`core_check.rs`) captures any dictionary-projection
  // `Match` resolutions nested inside `cond`, THEN `then`, THEN `els`, in
  // that literal order (Rust struct-literal field initializers evaluate
  // left-to-right regardless of the struct's declared field order) — so
  // lowering must consume the queue in that same order. `Bool`'s own
  // declared constructor order (which constructor is tag 0 vs. 1) is a
  // SEPARATE concern (only affects which slot each arm ends up in below,
  // not the order they're lowered/captured in) — an earlier version of
  // this function conflated the two, lowering `then`/`els` (in whichever
  // order `Bool`'s constructors happened to be declared) before `cond`,
  // which desynced the queue for any `if` whose `cond` involved a
  // dictionary-projected class method (`n == 0`, `String.beq s ""`, ...)
  // together with one in `then`/`els` — i.e. almost any real `if`.
  let cond_ir = lower_term(ctx, cond)?;
  let then_ir = lower_term(ctx, then)?;
  let els_ir = lower_term(ctx, els)?;
  let mut arms = Vec::with_capacity(info.constructors.len());
  for ctor in &info.constructors {
    let name = &ctor.name;
    let body = match name.as_str() {
      "true" => then_ir.clone(),
      "false" => els_ir.clone(),
      other => {
        return Err(LowerCoreIrError::UnknownConstructor(
          bool_path.clone(),
          Identifier::new(other.to_string()),
        ));
      }
    };
    arms.push(core_ir::arm(0, body));
  }
  Ok(core_ir::match_(cond_ir, arms))
}

/// `Type`/`Prop`/`Pred`'s own universe levels, matching
/// `core_check_module.rs`'s E7 registration (`ctx.insert(atom,
/// CoreTerm::Sort { level })`) exactly — `Pred` is a plain alias for
/// `Prop`, same level, same as that registration.
fn builtin_sort_level(path: &ModulePath) -> Option<u64> {
  match path.to_string().as_str() {
    "Type" => Some(1),
    "Prop" | "Pred" => Some(0),
    _ => None,
  }
}

/// `match` compiles to constructor-tag dispatch: one arm per constructor
/// of the scrutinee's inductive, in declaration order, filled from the
/// matching named case or (if absent) the wildcard `_` case — mirroring
/// the tree-walker's own wildcard-fallback convention. The resolved
/// inductive comes from `CoreProgram.match_resolutions` (captured at
/// check time — see that field's doc comment for why re-deriving it
/// from case names alone here would be wrong).
fn lower_match(
  ctx: &mut LowerCtx,
  scrutinee: &CoreTerm,
  cases: &[crate::core_term::CoreMatchCase],
) -> Result<CoreIr, LowerCoreIrError> {
  // Order matters here: `core_check.rs`'s `infer`/`check` call
  // `infer(scrutinee)` (recursing into any match nested *inside* the
  // scrutinee first) before capturing *this* match's own resolution,
  // before recursing into the case bodies — so lowering must pop in that
  // same order (scrutinee, then self, then cases) for the queue-based
  // association to line up.
  let scrutinee_ir = lower_term(ctx, scrutinee)?;
  let case_names: Vec<Identifier> = cases.iter().map(|c| c.name.clone()).collect();
  let atom = ctx.pop_match_resolution(&case_names)?;
  let inductive_path = ctx
    .atom_paths
    .get(&atom)
    .cloned()
    .ok_or(LowerCoreIrError::UnresolvedAtom(atom))?;
  let info = ctx
    .program
    .inductives
    .get(&inductive_path)
    .ok_or_else(|| LowerCoreIrError::UnknownInductive(inductive_path.clone()))?;
  // Lower each *source* case exactly once, in order — matching
  // `check`/`infer`'s own `for case in cases` loop — rather than once
  // per constructor tag it ends up covering. A wildcard case can cover
  // several tags; visiting its body once per tag here (instead of once,
  // reused/shared) would both do redundant work and, more importantly,
  // pop more queue entries than `check`/`infer` ever pushed for it,
  // desyncing every subsequent match in this def.
  let mut named: Map<Identifier, MatchArm> = Map::new();
  let mut wildcard: Option<MatchArm> = None;
  for case in cases {
    let bind_count = case.dbgs.len() as u32;
    let body = std::sync::Arc::new(lower_term(ctx, &case.value)?);
    let arm = MatchArm { bind_count, body };
    if case.name.as_str() == "_" {
      wildcard = Some(arm);
    } else {
      named.insert(case.name.clone(), arm);
    }
  }
  let mut arms = Vec::with_capacity(info.constructors.len());
  // Memoizes `shift_ir(&wildcard.body, 0, delta)` by `delta` (== a
  // covered tag's own arity, since the wildcard's own `bind_count` is
  // always 0) — several tags commonly share the same arity (e.g. every
  // 1-field `Term` constructor: `lit`/`ntv`/`con`/`type_`), so this
  // avoids re-walking the same body once per tag.
  let mut shifted_wildcard_bodies: Map<u32, IrRef> = Map::new();
  for ctor in &info.constructors {
    let arm = match named.get(&ctor.name).cloned() {
      Some(arm) => arm,
      None if wildcard.is_none() => {
        // No named case AND no wildcard covers this constructor — the
        // surface language allows this (`match List.cons 5 List.empty {
        // cons x _ => x == 5 }` never mentions `empty` at all) whenever
        // the programmer knows, informally, that constructor can't
        // actually occur here; the tree-walker handles it by dispatching
        // on the scrutinee's REAL runtime tag and simply never reaching
        // an uncovered arm in a well-behaved program. `arms` here has to
        // be a complete, fixed-size array indexed by tag regardless —
        // synthesize a `MatchFail` arm for this one tag (a genuine
        // runtime error, `CoreEvalError::NonExhaustiveMatch`, ONLY if
        // this exact tag is ever actually dispatched to) instead of
        // refusing to lower the whole def, which used to fail even the
        // common case where this constructor is provably never
        // constructed. See `CoreIr::MatchFail`'s own doc comment.
        MatchArm {
          bind_count: ctor.arity,
          body: std::sync::Arc::new(CoreIr::MatchFail {
            inductive: inductive_path.clone(),
            ctor: ctor.name.clone(),
          }),
        }
      }
      None => {
        let wildcard = wildcard.clone().unwrap();
        // A wildcard case's own SOURCE pattern (`_`) always binds zero
        // names (`case.dbgs.len() == 0` above), but at runtime `dispatch`
        // (`core_eval.rs`) unconditionally pushes every one of the
        // MATCHED constructor's own real fields into `env` before
        // running the arm body — regardless of whether that body ever
        // reads them. Reusing the wildcard's own `bind_count` (0) here
        // is only correct for a nullary constructor; for anything else
        // (e.g. `Option.some 1`'s `some`, arity 1) it desyncs `dispatch`'s
        // own `args.len() != arm.bind_count` check, producing
        // `ArityMismatch` (surfaced as "expected 0 constructor fields,
        // got 1") the moment a wildcard-only match ever runs against a
        // constructor with fields — a real bug found running
        // `init/tests.mo`'s own `test_match_wildcard_only` through Phase
        // 8's parity harness. Each constructor tag that falls through to
        // the wildcard needs ITS OWN `bind_count` (`ctor.arity`), not the
        // wildcard pattern's.
        //
        // The shared `body` itself is NOT safe to reuse unchanged, though
        // (an earlier version of this function assumed it was, reasoning
        // "a wildcard body never references any of these extra, unused
        // bindings"): whether the body ever READS the extra bindings is
        // irrelevant — the body was lowered assuming its own enclosing
        // scope sits immediately outside it (0 frames of its own), and
        // `dispatch` now interposes `ctor.arity` extra frames before it
        // runs. Any `Local` reference the body makes to something OUTSIDE
        // its own binder scope (e.g. an outer function parameter it
        // closes over) needs to skip past those extra frames too, exactly
        // like opening any other binder — otherwise it silently resolves
        // to one of the newly-pushed constructor fields instead of the
        // real outer value. Concretely: `match a { pat => ..., _ => match
        // b { ... } }`'s wildcard arm body references `b` (bound outside
        // this whole match); once this arm covers a tag with `arity > 0`,
        // `b`'s reference must shift by that arity or it reads one of the
        // matched constructor's own fields instead — confirmed via
        // `lang/typecheck/unify.mo`'s `unify`, whose final wildcard arm
        // (covering `Term.app`/`Term.lit`/... , all `arity > 0`) does
        // exactly this, corrupting `Similar.similar a b`'s own `b`
        // argument. `shift_ir` performs this adjustment once per distinct
        // arity, at lowering time (not on every `eval`).
        let body = shifted_wildcard_bodies
          .entry(ctor.arity)
          .or_insert_with(|| shift_ir(&wildcard.body, 0, ctor.arity))
          .clone();
        MatchArm {
          bind_count: ctor.arity,
          body,
        }
      }
    };
    arms.push(arm);
  }
  Ok(core_ir::match_(scrutinee_ir, arms))
}

/// A constructor value, possibly partially applied. `CoreTerm::App`
/// chains only ever apply arguments left-to-right, so `args` is always
/// either fully `Some` or a `Some` prefix followed by a `None` suffix —
/// never sparse; `SparseArgs` below is a defensive check, not an
/// expected path.
fn lower_con(ctx: &mut LowerCtx, c: &CoreConstructor) -> Result<CoreIr, LowerCoreIrError> {
  let info = ctx
    .program
    .inductives
    .get(&c.typ_name)
    .ok_or_else(|| LowerCoreIrError::UnknownInductive(c.typ_name.clone()))?;
  let tag = info
    .constructors
    .iter()
    .position(|ctor| ctor.name == c.name)
    .ok_or_else(|| LowerCoreIrError::UnknownConstructor(c.typ_name.clone(), c.name.clone()))?
    as u32;
  let args = lower_prefix_args(ctx, &c.args)
    .ok_or_else(|| LowerCoreIrError::SparseArgs(c.typ_name.clone(), c.name.clone()))??;
  Ok(core_ir::con(tag, c.num_args as u32, args))
}

fn lower_ntv(ctx: &mut LowerCtx, n: &CoreNative) -> Result<CoreIr, LowerCoreIrError> {
  let native_id = ctx.intern_native(&n.native_name, n.num_args);
  let args = lower_prefix_args(ctx, &n.args)
    .ok_or_else(|| LowerCoreIrError::SparseNativeArgs(n.native_name.clone()))??;
  Ok(core_ir::ntv(native_id, args))
}

/// Lower a `Vec<Option<CoreTerm>>`'s `Some` prefix, erroring (outer
/// `None`) if a `Some` follows a `None` anywhere in the list.
fn lower_prefix_args(
  ctx: &mut LowerCtx,
  args: &[Option<CoreTerm>],
) -> Option<Result<Vec<CoreIr>, LowerCoreIrError>> {
  let mut out = Vec::with_capacity(args.len());
  let mut seen_none = false;
  for arg in args {
    match arg {
      Some(_) if seen_none => return None,
      Some(t) => match lower_term(ctx, t) {
        Ok(ir) => out.push(ir),
        Err(e) => return Some(Err(e)),
      },
      None => seen_none = true,
    }
  }
  Some(Ok(out))
}

/// `{ x := 1, y := 2 }` compiles to an ordinary `Con` of the annotated
/// struct's sole constructor, with `fields` (keyed by name, unordered)
/// re-ordered into the struct's declared field order. Missing fields
/// (defaults, which this checker doesn't track — see
/// `core_check::check_struct_fields`'s doc comment) are not synthesized
/// here either; a struct value with a missing field simply isn't
/// constructible via this path, matching the checker's own limitation.
fn lower_struct_lit(
  ctx: &mut LowerCtx,
  fields: &Map<Identifier, CoreTerm>,
  type_name: Option<Atom>,
) -> Result<CoreIr, LowerCoreIrError> {
  let atom = type_name.ok_or(LowerCoreIrError::UnresolvedMatch)?;
  let struct_path = ctx
    .atom_paths
    .get(&atom)
    .cloned()
    .ok_or(LowerCoreIrError::UnresolvedAtom(atom))?;
  build_struct_con(ctx, atom, &struct_path, fields)
}

/// `{ base with y := 2 }` — unlike `StructLit`, `base` is a genuine
/// value (evaluated once, used for any field `fields` doesn't override).
/// Compiled to a `Match` that destructures `base`'s fields into locals,
/// then builds a fresh `Con` reusing the destructured fields for
/// anything not overridden — there's no in-place mutation at this IR
/// level (constructors are immutable values), so an "update" is always a
/// full rebuild.
fn lower_struct_update(
  _ctx: &mut LowerCtx,
  _base: &CoreTerm,
  _fields: &Map<Identifier, CoreTerm>,
) -> Result<CoreIr, LowerCoreIrError> {
  // NOT YET IMPLEMENTED: unlike `StructLit` (which carries a resolved
  // `type_name: Option<Atom>` on the node itself), `StructUpdate` has no
  // such field, and `core_check.rs`'s `check`/`infer` currently records
  // no resolution for it at all (only `CoreLit::Match`'s two handling
  // sites call `record_match_resolution`) — so there is nothing in
  // `CoreProgram` to resolve `base`'s struct type from yet. The intended
  // design (once that capture exists): compile to a `Match` that
  // destructures `base`'s fields into locals, then builds a fresh `Con`
  // reusing the destructured fields for anything `fields` doesn't
  // override (there's no in-place mutation at this IR level —
  // constructors are immutable values, so an "update" is always a full
  // rebuild) — left as a follow-up rather than guessed at without a
  // real capture to drive it.
  Err(LowerCoreIrError::UnresolvedMatch)
}

fn build_struct_con(
  ctx: &mut LowerCtx,
  struct_atom: Atom,
  struct_path: &ModulePath,
  fields: &Map<Identifier, CoreTerm>,
) -> Result<CoreIr, LowerCoreIrError> {
  let info = ctx
    .program
    .inductives
    .get(struct_path)
    .ok_or_else(|| LowerCoreIrError::UnknownInductive(struct_path.clone()))?;
  let field_names = info
    .struct_field_names
    .clone()
    .ok_or(LowerCoreIrError::UnknownStruct(struct_atom))?;
  let mut args = Vec::with_capacity(field_names.len());
  for name in &field_names {
    let value = fields
      .get(name)
      .ok_or_else(|| LowerCoreIrError::UnknownStructField(struct_path.clone(), name.clone()))?;
    args.push(lower_term(ctx, value)?);
  }
  Ok(core_ir::con(0, field_names.len() as u32, args))
}

// ---------------------------------------------------------------------------
// Whole-program assembly
// ---------------------------------------------------------------------------

/// What a global slot actually is, once every def/instance/constructor
/// reference in the program has been resolved to a flat index.
#[derive(Debug, Clone)]
pub enum GlobalDef {
  /// An ordinary def, instance method, or assembled instance dictionary
  /// — has a real `CoreIr` body to evaluate (once, then memoize — see
  /// the plan's Phase 5).
  Def(core_ir::IrRef),
  /// A constructor referenced point-free (no `CoreIr` body exists for
  /// it) — the evaluator (Phase 3/4/5) resolves this straight to a
  /// synthesized, empty `Value::Con { tag, args: vec![] }`, filled
  /// left-to-right by ordinary application.
  Constructor { tag: u32, arity: u32 },
  /// A native-attributed def with no explicit body (`@[native i64_add]
  /// def I64.add (a b : I64) : I64`) — no *useful* `CoreIr` body exists
  /// for it either, for a different reason than `Constructor`: see
  /// `point_free_native_shape`'s doc comment. Resolves the same way —
  /// straight to a synthesized, empty `Value::PartialNtv { native_id,
  /// args: vec![] }`, filled left-to-right by ordinary application.
  Native { native_id: u32, arity: u32 },
  /// A def that failed to lower for a known, already-diagnosed reason
  /// (see `LoweredProgram::skipped`) — forcing this slot at evaluation
  /// time should error clearly, not silently produce a wrong value.
  Unresolved(ModulePath),
}

/// A specific, by-name-resolved constructor's tag + arity within its
/// inductive's declared constructor order.
#[derive(Debug, Clone, Copy)]
pub struct CtorTag {
  pub tag: u32,
  pub arity: u32,
}

/// Detects the exact shape `term::def_with_native` synthesizes for a
/// native-attributed def with no explicit body (`@[native i64_add] def
/// I64.add (a b : I64) : I64`): `num_args` nested `Lam`s (giving the def
/// its correctly-arity'd Pi type) wrapping a `CoreNative` whose own
/// `args` are ALL `None`. The params are never actually threaded into
/// the native call itself — the old `Term`/`EvalTerm` pipeline instead
/// relies on a `Par::I`-parameterized-`Lam`-specific evaluation rule
/// (`eval.rs`) that has no `CoreTerm`/`CoreIr` equivalent, and was never
/// ported here since ordinary lowering never had a reason to look for
/// it. (Point-free *constructor* defs dodge the same class of gap for a
/// different reason: their `Value` never routes through a Term-
/// synthesized body at all — see `GlobalDef::Constructor` — so this
/// wasn't caught until a real program actually forced a native-backed
/// def's global slot directly, e.g. `I64.beq` inside `instance BEq I64`'s
/// dictionary.) Detected up front so `lower_program` can synthesize an
/// equivalent `GlobalDef::Native` directly, instead of lowering the
/// (structurally valid but semantically empty) `Lam`-wrapped `Ntv` node,
/// which would otherwise silently compile to a native call that can
/// never actually receive its arguments (`Ntv { args: [] }`, forever).
fn point_free_native_shape(term: &CoreTerm) -> Option<(&Identifier, usize)> {
  let mut current = term.strip_ctx();
  let mut depth = 0usize;
  while let CoreTerm::Lam { body, .. } = current {
    depth += 1;
    current = body.strip_ctx();
  }
  let CoreTerm::Ntv(native) = current else {
    return None;
  };
  if native.num_args == depth && native.args.iter().all(Option::is_none) {
    Some((&native.native_name, native.num_args))
  } else {
    None
  }
}

fn find_ctor(program: &CoreProgram, inductive: &ModulePath, name: &str) -> Option<CtorTag> {
  let info = program.inductives.get(inductive)?;
  let (tag, ctor) = info
    .constructors
    .iter()
    .enumerate()
    .find(|(_, c)| c.name.as_str() == name)?;
  Some(CtorTag {
    tag: tag as u32,
    arity: ctor.arity,
  })
}

/// Constructor tags for the handful of prelude inductives native
/// execution (Phase 5) needs to build or inspect directly: `Bool`, since
/// every int/float/string comparison native produces a boolean result as
/// a `Value::Con` (there is no `IrLit::Bool` — see `core_ir.rs`'s doc
/// comment; `if`/`match` already treat `Bool` as an ordinary
/// two-constructor inductive, see `lower_if`), and `Option`/`List`, for
/// `String.get`/`to_list`/`from_list`. Resolved once, directly from the
/// whole program's `CoreProgram.inductives` — deliberately NOT from which
/// constructors happen to have been interned into `LoweredProgram.globals`:
/// a fully-applied constructor (e.g. the surface `true`/`false` literals)
/// compiles straight to a `CoreIr::Con` node and never touches `Global`
/// at all, so a slot-based lookup would come up empty for exactly the
/// constructors this needs most. Mirrors `eval_term::Env::well_known`,
/// which did the same job less precisely via `ModulePath` string-suffix
/// matching (the only option available there, since `Term`-based lowering
/// has no equivalent of `CoreProgram.inductives`).
#[derive(Debug, Clone, Default)]
pub struct WellKnownCtors {
  pub bool_true: Option<CtorTag>,
  pub bool_false: Option<CtorTag>,
  pub option_some: Option<CtorTag>,
  pub option_none: Option<CtorTag>,
  pub list_cons: Option<CtorTag>,
  pub list_empty: Option<CtorTag>,
  /// `IO A`'s sole constructor (`init/io.mo`'s `type IO A { io A }`) —
  /// not needed by any native today, but needed to interpret a forced
  /// test def's result `Value` the same way the tree-walker's own
  /// `detect_test_result` (`lib.rs`) unwraps an `IO`-wrapped `Bool`/
  /// `Result` before judging pass/fail — see `core_parity.rs`.
  ///
  /// TODO: `IO` is slated to be replaced with an opaque indexed monad
  /// whose internal value is NOT accessible via an ordinary constructor
  /// match — `io_io` (and any code unwrapping it, e.g. `core_parity.rs`)
  /// will need to change to whatever that type's own (non-structural)
  /// unwrap mechanism ends up being once that lands.
  pub io_io: Option<CtorTag>,
  /// `Result E A`'s two constructors (`init/prelude.mo`) — same reason.
  pub result_ok: Option<CtorTag>,
  pub result_err: Option<CtorTag>,
}

impl WellKnownCtors {
  fn resolve(program: &CoreProgram) -> Self {
    let bool_path = mpt("Bool");
    let option_path = mpt("Option");
    let list_path = mpt("List");
    let io_path = mpt("IO");
    let result_path = mpt("Result");
    WellKnownCtors {
      bool_true: find_ctor(program, &bool_path, "true"),
      bool_false: find_ctor(program, &bool_path, "false"),
      option_some: find_ctor(program, &option_path, "some"),
      option_none: find_ctor(program, &option_path, "none"),
      list_cons: find_ctor(program, &list_path, "cons"),
      list_empty: find_ctor(program, &list_path, "empty"),
      io_io: find_ctor(program, &io_path, "io"),
      result_ok: find_ctor(program, &result_path, "ok"),
      result_err: find_ctor(program, &result_path, "err"),
    }
  }
}

pub struct LoweredProgram {
  /// Index = the same flat index every `CoreIr::Global` in this program
  /// uses.
  pub globals: Vec<GlobalDef>,
  /// Index = the same `native_id` every `CoreIr::Ntv` in this program
  /// uses — the evaluator's native-dispatch table (Phase 5) is keyed the
  /// same way.
  pub natives: Vec<Identifier>,
  /// Index = the same `native_id` as `natives` — each native's fixed
  /// arity (see `LowerCtx::native_arities`'s doc comment for why this
  /// lives in a parallel table rather than on `CoreIr::Ntv` itself).
  pub native_arities: Vec<u32>,
  /// Defs that couldn't be lowered because of a *known, already-diagnosed*
  /// gap — currently just `UnresolvedMatch` arising from a dictionary-
  /// field-projection `Match` node (`project_dict_field`,
  /// `core_check.rs`), which `desugar_struct_literals` synthesizes
  /// *after* `check`/`infer` already ran, so it's never visited by this
  /// session's `record_match_resolution` capture at all (that capture
  /// only sees `Match` nodes present *during* the check pass — see
  /// `plans/implementations/core-term-closure-evaluator.md`'s Phase 2
  /// notes). Any *other* def whose lowering fails is a genuine error and
  /// aborts `lower_program` outright, rather than being silently
  /// collected here — this list exists to make partial progress visible
  /// and honest, not to hide unexpected bugs.
  pub skipped: Vec<(ModulePath, LowerCoreIrError)>,
  /// Every interned global path, in the same index order as `globals` —
  /// how a caller finds which slot to start evaluating from (e.g. a
  /// program's `main`), via `LoweredProgram::index_of`.
  pub paths: Vec<ModulePath>,
  /// Constructor tags native execution (Phase 5) needs — see
  /// `WellKnownCtors`'s own doc comment for why this is resolved
  /// separately from `globals`/`paths`.
  pub well_known: WellKnownCtors,
}

impl LoweredProgram {
  /// The global slot index for `path`, if anything in the program
  /// actually referenced it (an entry point that's never referenced by
  /// anything else — the common case for `main` — still gets a slot,
  /// since every captured def's own path is interned up front in
  /// `lower_program`, whether or not anything else points to it).
  pub fn index_of(&self, path: &ModulePath) -> Option<u32> {
    self.paths.iter().position(|p| p == path).map(|i| i as u32)
  }
}

/// Lower every captured def (and instance method — captured the same
/// way, under an instance-qualified path) in `program`, then assemble a
/// flat, whole-program `LoweredProgram`. Every def gets its own global
/// slot reserved up front (even one nothing else references, e.g. an
/// entry point like `main`); a bare constructor reference gets a slot
/// too, resolved from `program.inductives` rather than requiring a
/// lowered body (constructors have none); an instance's own dictionary
/// slot is assembled on demand as a `Con` of `Global` references into
/// its already-independently-lowered methods (not a copy of their
/// bodies) — this is exactly what gives dictionary access the same O(1),
/// memoized-once-forced treatment as any other global reference.
pub fn lower_program(program: &CoreProgram) -> Result<LoweredProgram, LowerCoreIrError> {
  let mut interner = GlobalInterner::new();
  let mut natives: Map<Identifier, u32> = Map::new();
  let mut native_order: Vec<Identifier> = Vec::new();
  let mut native_arities: Vec<u32> = Vec::new();

  let mut lowered_defs: Map<ModulePath, CoreIr> = Map::new();
  let mut native_defs: Map<ModulePath, (u32, u32)> = Map::new();
  let mut skipped: Vec<(ModulePath, LowerCoreIrError)> = Vec::new();
  for (path, checked) in &program.defs {
    let match_queue = program
      .match_resolutions
      .get(path)
      .cloned()
      .unwrap_or_default()
      .into();
    let mut ctx = LowerCtx {
      program,
      interner: &mut interner,
      natives: &mut natives,
      native_order: &mut native_order,
      native_arities: &mut native_arities,
      atom_paths: &checked.atom_paths,
      match_queue,
    };
    // A native-attributed def with no explicit body needs special
    // handling BEFORE the ordinary `lower_term` call below — see
    // `point_free_native_shape`'s doc comment for why lowering it
    // normally would silently produce a native call that can never
    // receive its arguments.
    if let Some((native_name, num_args)) = point_free_native_shape(&checked.term) {
      let native_id = ctx.intern_native(native_name, num_args);
      ctx.interner.intern(path.clone());
      native_defs.insert(path.clone(), (native_id, num_args as u32));
      continue;
    }
    // A def whose *value* is itself type-level (e.g. `def Lens S T A B
    // := (S -> A) -> ...`, a type synonym rather than runtime data) has
    // no runtime representation and is never referenced from value
    // position by well-typed code — skip it rather than erroring the
    // whole program. Only reserve/populate its global slot on success,
    // so a genuinely-unused type-level def never claims one; if
    // something *does* reference it in value position, that's a real
    // bug and will surface as `UnresolvedGlobal` at assembly time below.
    match lower_term(&mut ctx, &checked.term) {
      Ok(ir) => {
        ctx.interner.intern(path.clone());
        lowered_defs.insert(path.clone(), ir);
      }
      Err(LowerCoreIrError::UnexpectedTypeLevelTerm(_)) => {}
      Err(e @ (LowerCoreIrError::UnresolvedMatch | LowerCoreIrError::NonExhaustiveMatch(..))) => {
        // Reserve this def's slot anyway (rather than leaving it to be
        // lazily interned later, possibly *after* the snapshot the final
        // assembly loop below takes) — anything referencing this path
        // gets a `GlobalDef::Unresolved` placeholder there instead of a
        // real body.
        //
        // `NonExhaustiveMatch` specifically: the surface language
        // permits a `match` that only covers SOME of a type's
        // constructors with no wildcard, whenever the programmer knows
        // (informally, unverified) the others can't occur -- e.g.
        // `match List.cons 5 List.empty { cons x _ => ... }`, matching a
        // scrutinee constructed one line up. The tree-walker handles
        // this at RUNTIME (dispatch by the scrutinee's actual tag; a
        // truly-missing case only errors if it's ever actually reached).
        // `lower_match` instead needs a complete, fixed-size `arms`
        // array indexed by tag at LOWERING time -- it has no runtime
        // "case not found" fallback to defer to. Skipping the def (like
        // `UnresolvedMatch`) is the safe, conservative choice for now:
        // this def simply won't lower, and forcing it errors cleanly
        // (`UnresolvedGlobal`) rather than crashing the whole program's
        // lowering. A real limitation relative to the tree-walker,
        // tracked as a known Phase 8 gap rather than fixed here --
        // fixing it properly means synthesizing a runtime-error arm for
        // every genuinely-missing constructor, not skipping the def.
        ctx.interner.intern(path.clone());
        skipped.push((path.clone(), e));
      }
      Err(e) => return Err(e),
    }
  }

  for path in program.instances.keys() {
    interner.intern(path.clone());
  }

  // Reverse index: a constructor's full path (`List.cons`, matching
  // exactly the shape `Free(ctor_atom)`'s own `atom_paths` entry uses,
  // per `register_inductive`'s `ctor.name()` convention) -> (tag,
  // arity) — for resolving a point-free constructor reference that
  // never appears as a `CoreTerm::Con` node at all.
  let mut constructor_slots: Map<ModulePath, (u32, u32)> = Map::new();
  for (inductive_path, info) in &program.inductives {
    for (tag, ctor) in info.constructors.iter().enumerate() {
      let ctor_path = inductive_path.clone().append(vec![ctor.name.clone()]);
      constructor_slots.insert(ctor_path, (tag as u32, ctor.arity));
    }
  }

  // Snapshot interned paths now: assembling an instance's dictionary
  // below only ever re-interns paths that must already be present (its
  // own methods, captured via `program.defs` in the loop above), so this
  // list is already complete and won't grow further.
  let paths = interner.paths().to_vec();
  let mut globals = Vec::with_capacity(paths.len());
  for path in &paths {
    if let Some(ir) = lowered_defs.get(path) {
      globals.push(GlobalDef::Def(std::sync::Arc::new(ir.clone())));
    } else if let Some(&(native_id, arity)) = native_defs.get(path) {
      globals.push(GlobalDef::Native { native_id, arity });
    } else if let Some(info) = program.instances.get(path) {
      let args: Vec<CoreIr> = info
        .method_paths
        .iter()
        .map(|m| core_ir::global(interner.intern(m.clone())))
        .collect();
      let dict = core_ir::con(0, info.method_paths.len() as u32, args);
      globals.push(GlobalDef::Def(std::sync::Arc::new(dict)));
    } else if let Some(&(tag, arity)) = constructor_slots.get(path) {
      globals.push(GlobalDef::Constructor { tag, arity });
    } else if program.defs.contains_key(path) {
      // Reserved above specifically because it was skipped (a known,
      // already-diagnosed gap — see `skipped`), not a mystery reference.
      globals.push(GlobalDef::Unresolved(path.clone()));
    } else if let Some(level) = builtin_sort_level(path) {
      // `Type`/`Prop`/`Pred` used as a VALUE (`get_sort Type`) — these
      // are registered as known globals purely for type-checking
      // (`core_check_module.rs`'s E7, `ctx.insert(atom, CoreTerm::Sort
      // {..})`), entirely separate from `program.defs` (they're not real
      // `.mo`-file defs at all), so they'd otherwise fall through to the
      // "mystery reference" catch-all below and surface as
      // `UnresolvedGlobal` the moment anything actually evaluates one —
      // a real gap found running `init/tests.mo`'s own
      // `test_type_as_value_arg`/`test_prop_as_value_arg`/etc. through
      // Phase 8's parity harness. Same opaque `IrLit::Sort` literal
      // `CoreTerm::Sort`'s own lowering arm produces.
      globals.push(GlobalDef::Def(std::sync::Arc::new(CoreIr::Lit(
        IrLit::Sort(level),
      ))));
    } else {
      // A bare reference with no def, instance, or constructor behind
      // it at all — in practice this is a class method's own abstract
      // atom (e.g. `HAdd.add`, registered as a `known_globals` entry by
      // `register_inductive`'s `Class` branch so its *type* is
      // resolvable, but with no body: only concrete *instances* have
      // one). A well-typed program should only ever reach a class
      // method through `project_dict_field`'s dictionary-projection
      // `Match` (not captured yet — see `LowerCoreIrError::UnresolvedMatch`'s
      // doc comment), so a bare `Free` reference surfacing here at all
      // is downstream of that same gap, not a separate one. Treated the
      // same way — recorded, not fatal — until that capture exists.
      skipped.push((
        path.clone(),
        LowerCoreIrError::UnresolvedGlobal(path.clone()),
      ));
      globals.push(GlobalDef::Unresolved(path.clone()));
    }
  }

  let well_known = WellKnownCtors::resolve(program);

  Ok(LoweredProgram {
    globals,
    natives: native_order,
    native_arities,
    skipped,
    paths,
    well_known,
  })
}
