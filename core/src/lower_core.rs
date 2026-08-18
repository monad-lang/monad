//! Names → `CoreTerm` lowering pass — Phase 2 of
//! `plans/implementations/typechecker-de-bruijn-core.md`.
//!
//! Converts a parser/macro-facing `crate::term::Term` (named) into a
//! `crate::core_term::CoreTerm` (locally nameless). Must run strictly
//! after macro expansion — `Quote`/macro hygiene fundamentally need
//! names (see the plan's Architecture section), so this pass treats an
//! unresolved `Quote` as an error, exactly mirroring how
//! `core/src/lower.rs` (the existing, separate `Term` → `EvalTerm` pass)
//! already refuses to lower `Quote` (`lower.rs:170`).
//!
//! Modeled directly on `core/src/lower.rs`'s `LowerContext`/`bound_vars`
//! stack + `find_bound` linear scan — same discipline, extended to push a
//! binder slot for `Forall`/`Pi` too (that pass only pushes for `Lam`,
//! and erases `Forall`/`Pi` outright, since its target `EvalTerm` has no
//! type-level binders; this pass must preserve them, since the type
//! checker needs the dependent-type structure).
//!
//! Scope for this increment: everything `CoreTerm` now represents
//! (`Forall`/`Pi`/`Lam`/`App`/`Var`/`Sort`/`Hole`/`Lit`/`Con`/`Ntv`, plus
//! the transparent `Ctx`/`Ann` wrappers). `Quote` and macro references
//! stay surface-only (see this module's and `core_term`'s doc comments) —
//! this pass rejects them with a descriptive `LowerError` rather than
//! guessing.

use crate::Map;
use crate::core_term::{
  Atom, AtomTable, CoreConstructor, CoreLit, CoreMatchCase, CoreNative, CoreTerm, DebugName,
};
use crate::term::{Identifier, Literal, ModulePath, NameRef, Operator, Par, Term};

#[derive(Debug, Clone, PartialEq)]
pub enum LowerError {
  /// A `Term` variant this increment doesn't yet lower — not a bug, a
  /// scope boundary (see module doc).
  Unsupported(String),
  /// A `NameRef::Index` reached lowering directly. That mechanism is
  /// unrelated positional constructor/native-argument threading (see the
  /// plan's research notes on `Par::I`/`NameRef::Index`), not general de
  /// Bruijn indexing — it should never appear in a term handed to this
  /// pass.
  UnexpectedIndex(usize),
}

/// Everything a `LowerContext` needs besides the (always-fresh,
/// always-empty-at-the-start) local-binder stack — bundled into one
/// struct rather than adding a new `LowerContext::with_*` constructor
/// per field, since module-level callers (`core_check_module`) routinely
/// need several of these at once.
#[derive(Debug, Default, Clone)]
pub struct LowerConfig {
  /// `infix (op) := path` declarations in scope, so a `NameRef::Op`
  /// occurrence (e.g. `(++)`) resolves to the same global atom its
  /// underlying function (`path`) does — without this, every infix
  /// operator reference is an unconditional `LowerError::Unsupported`
  /// (see `lower_var`). Empty by default — populated by module-level
  /// callers that scan a file's `infix` decls first.
  pub infix: Map<Operator, ModulePath>,
  /// Pre-bound free-name → `Atom` overrides, checked before falling back
  /// to `global_atom`. Needed when a name must resolve to one SPECIFIC
  /// atom for THIS lowering call rather than the process-wide shared
  /// global — e.g. `core_check_module` peels a `def`'s (separately
  /// elaborated) type's leading `Forall`s itself, minting fresh rigid
  /// atoms for its implicit type parameters, and must lower the `def`'s
  /// BODY with those exact same atoms for e.g. `(a : A)`'s inline
  /// annotation — otherwise the body's own bare `A` would resolve to the
  /// unrelated shared-by-name global atom instead, and checking the body
  /// against the elaborated type would spuriously fail (two different
  /// atoms that happen to both be spelled "A").
  pub free_overrides: Map<Identifier, Atom>,
  /// Unqualified-name → `Atom` aliases contributed by `open` declarations
  /// (e.g. `open Bool` makes bare `true` resolve to `Bool.true`'s atom).
  /// Checked after `free_overrides` but before the `global_atom(bare
  /// name)` fallback — `open` widens what a short name *can* mean, it
  /// doesn't override a more specific binding. Building this table (by
  /// working out, for every known global path, which unqualified forms
  /// the currently-active `open`s make it reachable under) is a
  /// module-level concern, not this lowering pass's — see
  /// `core_check_module`'s doc comment on why `Decl::Open` itself is
  /// never inspected here.
  pub unqualified_aliases: Map<Identifier, Atom>,
}

/// Local-binder stack (innermost last). Global references resolve via
/// `atoms` — an explicit, caller-owned `AtomTable` (see `core_term.rs`),
/// borrowed for this `LowerContext`'s lifetime rather than a table
/// private to it — so that two occurrences of the same global name
/// *across separate lowering calls* (e.g. two different `def`s both
/// referencing `List.any`) still resolve to the same `Atom`, not just two
/// occurrences within one call, as long as callers thread the SAME
/// `AtomTable` through every `LowerContext` constructed for one checking
/// run (exactly as `core_check_module.rs` does).
#[derive(Debug)]
pub struct LowerContext<'a> {
  bound: Vec<Identifier>,
  config: LowerConfig,
  atoms: &'a mut AtomTable,
  /// Every `ModulePath` this call resolved to a global `Atom` (via any of
  /// the three `Self::global_atom` call sites in this file —
  /// `resolve_free_name`'s fallback, a `NameRef::P` occurrence, or an
  /// infix operator's target), recorded as it happens. Global name
  /// resolution never validates that a path is "known" ahead of time — it
  /// always succeeds, minting or reusing an atom for whatever path it's
  /// given — so a lowered term's `Free` atoms aren't limited to whatever a
  /// caller's own `known_globals`-style registry happened to track in
  /// advance. `raise_core` needs the REVERSE of exactly this, atom by
  /// atom, to turn a `Free` occurrence back into a name — this is the
  /// explicit-parameter source for that (see `raise_core.rs`'s module doc
  /// for why it's a parameter, not a global lookup): callers fold
  /// `into_resolved_atoms()`'s result into whatever `atom_paths` map
  /// they're building, after each `lower_term` call.
  resolved_atoms: Map<Atom, ModulePath>,
}

impl<'a> LowerContext<'a> {
  pub fn new(atoms: &'a mut AtomTable) -> Self {
    Self::with_config(LowerConfig::default(), atoms)
  }

  pub fn with_config(config: LowerConfig, atoms: &'a mut AtomTable) -> Self {
    Self {
      bound: Vec::new(),
      config,
      atoms,
      resolved_atoms: Map::new(),
    }
  }

  fn push(&mut self, name: Identifier) {
    self.bound.push(name);
  }

  fn pop(&mut self) {
    self.bound.pop();
  }

  /// De Bruijn index of `name` if it's currently bound locally — a linear
  /// scan from the innermost (last-pushed) binder outward, exactly
  /// `core/src/lower.rs::find_bound`'s discipline.
  fn find_bound(&self, name: &Identifier) -> Option<u32> {
    self
      .bound
      .iter()
      .rev()
      .position(|n| n == name)
      .map(|i| i as u32)
  }

  /// Resolve `path` to a global atom, recording the mapping in
  /// `resolved_atoms` as a side effect — the single choke point every
  /// atom-interning call in this file goes through, so `resolved_atoms`
  /// is guaranteed complete for whatever this `LowerContext` actually
  /// resolved.
  fn global_atom(&mut self, path: ModulePath) -> Atom {
    let atom = self.atoms.intern(path.clone());
    self.resolved_atoms.insert(atom, path);
    atom
  }

  /// Every `Atom` this context resolved to a global `ModulePath` over its
  /// lifetime (across however many `lower_term` calls used it) — see this
  /// struct's `resolved_atoms` doc comment for why callers need this.
  pub fn resolved_atoms(&self) -> &Map<Atom, ModulePath> {
    &self.resolved_atoms
  }
}

/// Recover an ordinary `def`'s declared parameter names (and any default
/// value each carries) from its own BODY's leading `Term::Lam` chain --
/// see `core_check::StructFields::def_params`'s doc comment (in
/// `core_check.rs`, this pass's downstream consumer) for why this is the
/// only place a def's real param names survive at all (`pi_with_mult`
/// always erases them from the def's registered `Pi` TYPE, `arg_name:
/// None`) and why no field TYPE needs recovering here, only names +
/// defaults. Stops at the first non-`Lam` node (the def's real body) or
/// the first `Par::I` (implicit) layer -- `def_parser` only ever wraps a
/// def's own EXPLICIT param list in `Lam`s (`lams(params, term)`); an
/// implicit param is `Forall`-wrapped on the TYPE side instead and never
/// produces a `Lam` layer at all, so a `Par::I` here would mean this walk
/// started somewhere other than a def's own top-level body -- stop
/// defensively rather than assume. Returns an empty `Vec` for a niladic
/// def (no `Lam` layers at all). Pushes/pops `ctx`'s own binder stack the
/// same way `lower_term`'s own `Term::Lam` arm does, restoring it to
/// exactly where it started before returning -- callers may reuse `ctx`
/// afterward.
pub fn def_param_names(
  ctx: &mut LowerContext,
  def_term: &Term,
) -> Vec<(Identifier, Option<CoreTerm>)> {
  let mut current = def_term;
  let mut params: Vec<(Identifier, Option<CoreTerm>)> = Vec::new();
  while let Term::Lam { param, body } = current {
    let Par::P(p) = param else { break };
    let default_c = p.default.as_deref().and_then(|d| lower_term(ctx, d).ok());
    params.push((p.name.clone(), default_c));
    ctx.push(p.name.clone());
    current = body.as_ref();
  }
  for _ in 0..params.len() {
    ctx.pop();
  }
  params
}

pub fn lower_term(ctx: &mut LowerContext, term: &Term) -> Result<CoreTerm, LowerError> {
  match term {
    Term::Var { name } => lower_var(ctx, name),

    Term::Forall { name, typ, body } => {
      let typ_c = lower_term(ctx, typ)?;
      ctx.push(name.clone());
      let body_c = lower_term(ctx, body);
      ctx.pop();
      Ok(CoreTerm::Forall {
        dbg: DebugName::Named(name.clone()),
        typ: Box::new(typ_c),
        body: Box::new(body_c?),
      })
    }

    Term::Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => {
      let arg_c = lower_term(ctx, arg)?;
      let dbg = match arg_name {
        Some(n) => DebugName::Named(n.clone()),
        None => DebugName::Anonymous,
      };
      // Every Pi occupies a binder slot in CoreTerm, dependent or not —
      // `ret` is always one level deeper than `arg` (see core_term.rs's
      // depth convention) — so push a placeholder name even when there's
      // no user-facing name, purely to keep depth-tracking correct.
      let push_name = arg_name
        .clone()
        .unwrap_or_else(|| Identifier::new("_".to_string()));
      ctx.push(push_name);
      let ret_c = lower_term(ctx, ret);
      ctx.pop();
      Ok(CoreTerm::Pi {
        dbg,
        arg: Box::new(arg_c),
        ret: Box::new(ret_c?),
        mult: mult.clone(),
      })
    }

    Term::Lam { param, body } => match param {
      Par::P(p) => {
        let param_typ_c = lower_term(ctx, &p.typ)?;
        ctx.push(p.name.clone());
        let body_c = lower_term(ctx, body);
        ctx.pop();
        Ok(CoreTerm::Lam {
          dbg: DebugName::Named(p.name.clone()),
          param_typ: Box::new(param_typ_c),
          body: Box::new(body_c?),
        })
      }
      Par::I { typ, .. } => {
        let param_typ_c = lower_term(ctx, typ)?;
        ctx.push(Identifier::new("_".to_string()));
        let body_c = lower_term(ctx, body);
        ctx.pop();
        Ok(CoreTerm::Lam {
          dbg: DebugName::Anonymous,
          param_typ: Box::new(param_typ_c),
          body: Box::new(body_c?),
        })
      }
    },

    Term::App { fun, arg } => {
      let fun_c = lower_term(ctx, fun)?;
      let arg_c = lower_term(ctx, arg)?;
      Ok(CoreTerm::App {
        fun: Box::new(fun_c),
        arg: Box::new(arg_c),
      })
    }

    Term::Sort { level } => Ok(CoreTerm::Sort { level: *level }),
    Term::Hole => Ok(CoreTerm::Hole),

    // Carry the source location into CoreTerm's own `Ctx` wrapper (added
    // for `plans/implementations/typechecker-de-bruijn-core.md`'s
    // Diagnostics follow-up) rather than discarding it — every function
    // that inspects a `CoreTerm`'s shape strips this transparently (see
    // `CoreTerm::strip_ctx`/`strip_ctx_loc`/`into_stripped_ctx`), so
    // wrapping here doesn't change what anything downstream sees, only
    // what error-reporting can recover.
    Term::Ctx { loc, term, .. } => Ok(CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(lower_term(ctx, term)?),
    }),
    // `(term : typ)` desugars to `App(Lam{param_typ: typ, body: Bound(0)},
    // term)` — the exact same "immediately-applied identity function"
    // shape `let x : T := v in x` already lowers to — rather than simply
    // discarding `typ` (as an earlier version of this arm did). Both
    // `check`'s and `desugar_struct_literals`'s own `App(Lam, _)` ("let")
    // handling already know how to check/desugar `term` against a KNOWN
    // (non-`Hole`) `param_typ` before consuming the Lam entirely — so this
    // reuses that existing machinery to thread the annotation in as a
    // real expected-type hint, instead of one more place that would
    // otherwise need its own bespoke handling. Needed for e.g. `([] :
    // List I64)`: with no other argument to infer an element type from,
    // discarding the annotation left `FromListLiteral.empty`'s own class
    // param permanently unresolved.
    Term::Ann { term, typ } => {
      let typ_c = lower_term(ctx, typ)?;
      let term_c = lower_term(ctx, term)?;
      Ok(CoreTerm::App {
        fun: Box::new(CoreTerm::Lam {
          dbg: DebugName::Named(Identifier::gensym("$ann")),
          param_typ: Box::new(typ_c),
          body: Box::new(CoreTerm::Bound(0)),
        }),
        arg: Box::new(term_c),
      })
    }

    Term::Lit { value } => Ok(CoreTerm::Lit(lower_lit(ctx, value)?)),

    Term::Con(c) => Ok(CoreTerm::Con(CoreConstructor {
      name: c.name().clone(),
      typ_name: c.typ_name().clone(),
      num_args: c.num_args(),
      args: lower_args(ctx, c.args())?,
    })),

    Term::Ntv { native } => Ok(CoreTerm::Ntv(CoreNative {
      native_name: native.native_name.clone(),
      num_args: native.num_args,
      args: lower_args(ctx, &native.args)?,
    })),

    Term::Quote { .. } => Err(LowerError::Unsupported(
      "Quote must be resolved by macro expansion before lowering — matches \
       core/src/lower.rs's existing Quote handling"
        .to_string(),
    )),
  }
}

fn lower_args(
  ctx: &mut LowerContext,
  args: &[Option<Term>],
) -> Result<Vec<Option<CoreTerm>>, LowerError> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| lower_term(ctx, t)).transpose())
    .collect()
}

/// Resolve a name that isn't locally bound: `free_overrides` (most
/// specific — a per-call pinned atom) wins first, then
/// `unqualified_aliases` (an `open`-contributed short form), and only
/// then the `global_atom(bare name)` fallback (the name genuinely is,
/// or is being treated as, its own top-level path).
fn resolve_free_name(ctx: &mut LowerContext, name: &Identifier) -> Atom {
  if let Some(atom) = ctx.config.free_overrides.get(name) {
    *atom
  } else if let Some(atom) = ctx.config.unqualified_aliases.get(name) {
    *atom
  } else {
    ctx.global_atom(name.clone().to_path())
  }
}

/// Resolve a bare local-variable `Identifier` occurrence (not wrapped in a
/// `NameRef`) the same way `lower_var` resolves `NameRef::Id` — used for
/// `Literal::StructUpdate`'s `base`, which is a genuine variable reference
/// in `Term` (unlike `CoreLit::StructUpdate::base`, see `core_term.rs`'s
/// doc comment on why it's a resolved `CoreTerm` there, not a name).
fn lower_ident_var(ctx: &mut LowerContext, name: &Identifier) -> CoreTerm {
  match ctx.find_bound(name) {
    Some(idx) => CoreTerm::Bound(idx),
    None => CoreTerm::Free(resolve_free_name(ctx, name)),
  }
}

fn lower_lit(ctx: &mut LowerContext, lit: &Literal) -> Result<CoreLit, LowerError> {
  match lit {
    Literal::Str { value } => Ok(CoreLit::Str {
      value: value.clone(),
    }),
    Literal::Char { value } => Ok(CoreLit::Char { value: *value }),
    Literal::Num { value, suffix } => Ok(CoreLit::Num {
      value: *value,
      suffix: *suffix,
    }),
    Literal::Float { value, suffix } => Ok(CoreLit::Float {
      value: *value,
      suffix: *suffix,
    }),
    Literal::If { value, then, els } => Ok(CoreLit::If {
      cond: Box::new(lower_term(ctx, value)?),
      then: Box::new(lower_term(ctx, then)?),
      els: Box::new(lower_term(ctx, els)?),
    }),
    Literal::StructLit { fields, type_name } => {
      let mut out = crate::Map::new();
      for (name, value) in fields {
        out.insert(name.clone(), lower_term(ctx, value)?);
      }
      // Resolved the same way any other global name reference is (via
      // `lower_term`, which routes a bare `Var` through
      // `resolve_free_name`) — a struct's name is always a global/rigid
      // reference, never a locally-bound variable, so the result must be
      // a `Free` atom.
      let type_name = match type_name {
        Some(t) => match lower_term(ctx, t)? {
          CoreTerm::Free(atom) => Some(atom),
          other => {
            return Err(LowerError::Unsupported(format!(
              "struct literal type annotation must name a type directly, got {other:?}"
            )));
          }
        },
        None => None,
      };
      Ok(CoreLit::StructLit {
        fields: out,
        type_name,
      })
    }
    Literal::StructUpdate { base, fields } => {
      let base_c = lower_ident_var(ctx, base);
      let mut out = crate::Map::new();
      for (name, value) in fields {
        out.insert(name.clone(), lower_term(ctx, value)?);
      }
      Ok(CoreLit::StructUpdate {
        base: Box::new(base_c),
        fields: out,
      })
    }
    Literal::Match { value, cases } => {
      let scrutinee = Box::new(lower_term(ctx, value)?);
      let mut out_cases = Vec::with_capacity(cases.len());
      for case in cases {
        for a in &case.args {
          ctx.push(a.clone());
        }
        let value_c = lower_term(ctx, &case.value);
        for _ in &case.args {
          ctx.pop();
        }
        out_cases.push(CoreMatchCase {
          name: case.name.clone(),
          dbgs: case
            .args
            .iter()
            .map(|a| DebugName::Named(a.clone()))
            .collect(),
          value: Box::new(value_c?),
        });
      }
      Ok(CoreLit::Match {
        scrutinee,
        cases: out_cases,
      })
    }
    // Runtime-only values (only ever produced as evaluation results, never
    // written in source) — see core_term.rs's CoreLit doc comment.
    Literal::Term(_) | Literal::Foreign(_) => Err(LowerError::Unsupported(format!(
      "runtime-only literal ({lit}) reached lowering"
    ))),
  }
}

fn lower_var(ctx: &mut LowerContext, name: &NameRef) -> Result<CoreTerm, LowerError> {
  match name {
    NameRef::Id(id) => match ctx.find_bound(id) {
      Some(idx) => Ok(CoreTerm::Bound(idx)),
      None => Ok(CoreTerm::Free(resolve_free_name(ctx, id))),
    },
    NameRef::P(path) => Ok(CoreTerm::Free(ctx.global_atom(path.clone()))),
    NameRef::Index(i) => Err(LowerError::UnexpectedIndex(*i)),
    NameRef::Op(op) => match ctx.config.infix.get(op).cloned() {
      Some(path) => Ok(CoreTerm::Free(ctx.global_atom(path))),
      None => Err(LowerError::Unsupported(format!(
        "infix operator {name} has no entry in the lowering pass's infix table \
         (populate via LowerConfig::infix)"
      ))),
    },
    NameRef::Macro(_) => Err(LowerError::Unsupported(format!("{name}"))),
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::core_term::{close, open};
  use crate::term::{Multiplicity, app, forall, id, lam, param, pi, pi_name, sort0, sort1, var};

  fn lower(term: &Term) -> CoreTerm {
    lower_term(&mut LowerContext::new(&mut AtomTable::new()), term)
      .expect("lowering should succeed")
  }

  // -------------------------------------------------------------------
  // Basic shapes
  // -------------------------------------------------------------------

  #[test]
  fn test_lower_sort_and_hole() {
    assert_eq!(lower(&sort1()), CoreTerm::Sort { level: 1 });
    assert_eq!(lower(&Term::Hole), CoreTerm::Hole);
  }

  #[test]
  fn test_lower_lam_bound_var() {
    // fn a => a
    let term = lam(param(id("a"), sort1()), var("a"));
    let core = lower(&term);
    match core {
      CoreTerm::Lam { dbg, body, .. } => {
        assert_eq!(dbg.as_str(), "a");
        assert_eq!(*body, CoreTerm::Bound(0));
      }
      other => panic!("expected Lam, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_forall_pi_bound_var() {
    // {A : Type} -> A -> A
    let term = forall(param(id("A"), sort1()), pi(var("A"), var("A")));
    let core = lower(&term);
    match core {
      CoreTerm::Forall { dbg, body, .. } => {
        assert_eq!(dbg.as_str(), "A");
        match *body {
          CoreTerm::Pi { arg, ret, .. } => {
            assert_eq!(*arg, CoreTerm::Bound(0));
            // `ret` is one binder deeper than `arg` (Pi always occupies a
            // slot for its return type) — see core_term.rs's depth
            // convention and the matching core_unify.rs fixtures.
            assert_eq!(*ret, CoreTerm::Bound(1));
          }
          other => panic!("expected Pi, got {other:?}"),
        }
      }
      other => panic!("expected Forall, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_dependent_pi_named_arg() {
    // (x : A) -> x  — a dependent Pi whose return type references its own arg
    let term = pi_name(Some(id("x")), var("A"), var("x"));
    let core = lower(&term);
    match core {
      CoreTerm::Pi { dbg, arg, ret, .. } => {
        assert_eq!(dbg.as_str(), "x");
        // `A` isn't locally bound here, so it lowers to a Free atom.
        assert!(matches!(*arg, CoreTerm::Free(_)));
        // `x`, referenced from `ret`, is the Pi's own bound var: Bound(0).
        assert_eq!(*ret, CoreTerm::Bound(0));
      }
      other => panic!("expected Pi, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_app() {
    // f x
    let term = app(var("f"), var("x"));
    let core = lower(&term);
    match core {
      CoreTerm::App { fun, arg } => {
        assert!(matches!(*fun, CoreTerm::Free(_)));
        assert!(matches!(*arg, CoreTerm::Free(_)));
      }
      other => panic!("expected App, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_ctx_is_transparent() {
    use crate::parser::ModuleContext;
    use std::sync::Arc;
    let wrapped = Term::Ctx {
      loc: Default::default(),
      module: Arc::new(ModuleContext::default()),
      term: Box::new(sort1()),
    };
    assert_eq!(lower(&wrapped), CoreTerm::Sort { level: 1 });
  }

  #[test]
  fn test_lower_ann_desugars_to_applied_identity_lam() {
    // `(term : typ)` lowers to `App(Lam{param_typ: typ, body: Bound(0)},
    // term)` — the same "immediately-applied identity function" shape a
    // `let x : T := v in x` uses — rather than discarding `typ` (see
    // `try_resolve_class_method`'s doc comment on why the annotation
    // needs to survive as a real expected-type hint, e.g. for `([] :
    // List I64)`).
    let annotated = Term::Ann {
      term: Box::new(sort1()),
      typ: Box::new(sort0()),
    };
    let CoreTerm::App { fun, arg } = lower(&annotated) else {
      panic!("expected Ann to lower to an App");
    };
    assert_eq!(*arg, CoreTerm::Sort { level: 1 });
    let CoreTerm::Lam {
      param_typ, body, ..
    } = *fun
    else {
      panic!("expected Ann's App to apply a Lam");
    };
    assert_eq!(*param_typ, CoreTerm::Sort { level: 0 });
    assert_eq!(*body, CoreTerm::Bound(0));
  }

  // -------------------------------------------------------------------
  // Scope boundaries: things this increment deliberately doesn't lower
  // -------------------------------------------------------------------

  #[test]
  fn test_lower_quote_is_rejected() {
    let term = Term::Quote {
      term: Box::new(sort1()),
    };
    assert!(matches!(
      lower_term(&mut LowerContext::new(&mut AtomTable::new()), &term),
      Err(LowerError::Unsupported(_))
    ));
  }

  // -------------------------------------------------------------------
  // Global atom identity — the same free reference lowers to the same
  // Atom every time within one pass (required for the unifier to ever
  // treat repeated references as the same variable).
  // -------------------------------------------------------------------

  #[test]
  fn test_repeated_global_reference_shares_one_atom() {
    // f f  (applying a global `f` to itself, as a reference — not
    // meaningful as a real program, just exercises atom sharing)
    let term = app(var("f"), var("f"));
    let core = lower(&term);
    match core {
      CoreTerm::App { fun, arg } => {
        let CoreTerm::Free(a1) = *fun else {
          panic!("expected Free")
        };
        let CoreTerm::Free(a2) = *arg else {
          panic!("expected Free")
        };
        assert_eq!(a1, a2, "same global name must lower to the same atom");
      }
      other => panic!("expected App, got {other:?}"),
    }
  }

  #[test]
  fn test_distinct_globals_get_distinct_atoms() {
    let term = app(var("f"), var("g"));
    let core = lower(&term);
    match core {
      CoreTerm::App { fun, arg } => {
        let CoreTerm::Free(a1) = *fun else {
          panic!("expected Free")
        };
        let CoreTerm::Free(a2) = *arg else {
          panic!("expected Free")
        };
        assert_ne!(a1, a2);
      }
      other => panic!("expected App, got {other:?}"),
    }
  }

  // -------------------------------------------------------------------
  // Alpha-equivalence through a REAL lowering pass (not hand-built
  // CoreTerm, as in core_term.rs's Phase 0 test) — the core promise of
  // this whole redesign, now exercised end-to-end from named `Term`s
  // built the same way the parser itself builds them.
  // -------------------------------------------------------------------

  #[test]
  fn test_alpha_equivalent_foralls_lower_to_equal_core_terms() {
    // {A : Type} -> A -> A   vs   {B : Type} -> B -> B
    let a = forall(param(id("A"), sort1()), pi(var("A"), var("A")));
    let b = forall(param(id("B"), sort1()), pi(var("B"), var("B")));
    assert_ne!(a, b, "the named surface terms differ (sanity check)");
    assert_eq!(
      lower(&a),
      lower(&b),
      "lowered CoreTerms must be alpha-equivalent"
    );
  }

  #[test]
  fn test_two_unrelated_same_named_foralls_lower_independently() {
    // The actual bug this whole effort targets: two *different* generic
    // functions that both happen to name their type parameter "A" must
    // never be conflated. Lowered independently (fresh LowerContext per
    // call, as a real two-def module would be), their CoreTerms may
    // coincide in *shape* (if alpha-equivalent) but any subsequent
    // instantiation (core_unify::instantiate) gives each a fresh,
    // unrelated MetaId — nothing here ties them together by name.
    let generic_to_bool = forall(
      param(id("A"), sort1()),
      pi(var("A"), Term::Sort { level: 0 }),
    );
    let generic_to_self = forall(param(id("A"), sort1()), pi(var("A"), var("A")));
    assert_ne!(
      lower(&generic_to_bool),
      lower(&generic_to_self),
      "different bodies must not be conflated just because both name their param A"
    );
  }

  #[test]
  fn test_lowered_forall_round_trips_through_open_close() {
    // Sanity check that a real lowered Forall composes correctly with
    // core_term's open/close (used pervasively by core_unify).
    let term = forall(param(id("A"), sort1()), pi(var("A"), var("A")));
    let core = lower(&term);
    match core {
      CoreTerm::Forall { typ, body, .. } => {
        let (atom, opened) = open(&body);
        let closed = close(&opened, atom);
        assert_eq!(closed, *body);
        let _ = typ; // just needs to exist / be Sort 1, checked elsewhere
      }
      other => panic!("expected Forall, got {other:?}"),
    }
  }

  // -------------------------------------------------------------------
  // Shadowing: an inner binder reusing an outer binder's name must still
  // resolve occurrences to the correct (innermost) binder by index, not
  // get confused by the name collision — the whole point of this design.
  // -------------------------------------------------------------------

  #[test]
  fn test_shadowed_name_resolves_to_innermost_binder() {
    // fn x => fn x => x   (inner x shadows outer x; body's `x` must be
    // Bound(0), i.e. the INNER binder, not Bound(1)/the outer one)
    let term = lam(
      param(id("x"), sort1()),
      lam(param(id("x"), sort1()), var("x")),
    );
    let core = lower(&term);
    match core {
      CoreTerm::Lam { body, .. } => match *body {
        CoreTerm::Lam { body, .. } => assert_eq!(*body, CoreTerm::Bound(0)),
        other => panic!("expected inner Lam, got {other:?}"),
      },
      other => panic!("expected outer Lam, got {other:?}"),
    }
  }

  #[test]
  fn test_multiplicity_preserved_through_lowering() {
    let term = Term::Pi {
      arg_name: None,
      arg: Box::new(sort1()),
      ret: Box::new(sort1()),
      mult: Multiplicity::Linear,
    };
    match lower(&term) {
      CoreTerm::Pi { mult, .. } => assert_eq!(mult, Multiplicity::Linear),
      other => panic!("expected Pi, got {other:?}"),
    }
  }

  // -------------------------------------------------------------------
  // Lit/Con/Match — the extended scope (real .mo files use these
  // pervasively, unlike the earlier Forall/Pi/Lam/App-only increment).
  // -------------------------------------------------------------------

  #[test]
  fn test_lower_num_and_str_literals() {
    use crate::term::{num, str};
    match lower(&num(42)) {
      CoreTerm::Lit(crate::core_term::CoreLit::Num { value, .. }) => assert_eq!(value, 42),
      other => panic!("expected Lit::Num, got {other:?}"),
    }
    match lower(&str("hi")) {
      CoreTerm::Lit(crate::core_term::CoreLit::Str { value }) => assert_eq!(value, "hi"),
      other => panic!("expected Lit::Str, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_if_lowers_all_three_branches() {
    use crate::term::if_term;
    let term = if_term(var("cond"), var("then_val"), var("else_val"));
    match lower(&term) {
      CoreTerm::Lit(crate::core_term::CoreLit::If { cond, then, els }) => {
        assert!(matches!(*cond, CoreTerm::Free(_)));
        assert!(matches!(*then, CoreTerm::Free(_)));
        assert!(matches!(*els, CoreTerm::Free(_)));
      }
      other => panic!("expected Lit::If, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_match_binds_pattern_args_by_index() {
    use crate::term::{case, match_term};
    // match xs { cons a tail => a, empty => x }
    // `x` here is a FREE reference (not one of the pattern args), to
    // confirm pattern binders don't shadow unrelated free names.
    let term = match_term(
      var("xs"),
      vec![
        case(id("cons"), vec![id("a"), id("tail")], var("a")),
        case(id("empty"), vec![], var("x")),
      ],
    );
    match lower(&term) {
      CoreTerm::Lit(crate::core_term::CoreLit::Match { scrutinee, cases }) => {
        assert!(matches!(*scrutinee, CoreTerm::Free(_)));
        assert_eq!(cases.len(), 2);
        // `cons a tail => a`: two pattern args pushed (a, then tail), so
        // `a` (pushed first) is the OUTER one — Bound(1), not Bound(0)
        // (tail, pushed last/innermost, is unused here).
        assert_eq!(cases[0].dbgs.len(), 2);
        assert_eq!(*cases[0].value, CoreTerm::Bound(1));
        // `empty => x`: zero pattern args, `x` isn't a pattern var, so it
        // must resolve to a Free atom, not any Bound index.
        assert_eq!(cases[1].dbgs.len(), 0);
        assert!(matches!(*cases[1].value, CoreTerm::Free(_)));
      }
      other => panic!("expected Lit::Match, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_match_arm_referencing_outer_lambda_binder() {
    use crate::term::{case, match_term};
    // fn x => match x { some y => y, none => x }
    // Confirms a match case body can reference BOTH its own pattern
    // binder and an outer Lam's binder without index confusion.
    let inner_match = match_term(
      var("x"),
      vec![
        case(id("some"), vec![id("y")], var("y")),
        case(id("none"), vec![], var("x")),
      ],
    );
    let term = lam(param(id("x"), sort1()), inner_match);
    match lower(&term) {
      CoreTerm::Lam { body, .. } => match *body {
        CoreTerm::Lit(crate::core_term::CoreLit::Match { scrutinee, cases }) => {
          // scrutinee `x` is the Lam's own bound var.
          assert_eq!(*scrutinee, CoreTerm::Bound(0));
          // `some y => y`: y is its own pattern binder, Bound(0) from
          // inside that case's one-arg block.
          assert_eq!(*cases[0].value, CoreTerm::Bound(0));
          // `none => x`: no pattern args, so `x` refers straight through
          // to the enclosing Lam's binder, Bound(0) (no extra depth).
          assert_eq!(*cases[1].value, CoreTerm::Bound(0));
        }
        other => panic!("expected Lit::Match, got {other:?}"),
      },
      other => panic!("expected Lam, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_constructor_args() {
    use crate::term::{ModulePath, constructor};
    let con = constructor(
      id("cons"),
      ModulePath::top("List"),
      vec![Some(var("head")), Some(var("tail"))],
    );
    match lower(&Term::Con(con)) {
      CoreTerm::Con(c) => {
        assert_eq!(c.name, id("cons"));
        assert_eq!(c.num_args, 2);
        assert!(matches!(c.args[0], Some(CoreTerm::Free(_))));
        assert!(matches!(c.args[1], Some(CoreTerm::Free(_))));
      }
      other => panic!("expected Con, got {other:?}"),
    }
  }

  #[test]
  fn test_lower_struct_update_base_is_resolved_not_a_name() {
    use crate::Map;
    use crate::term::num;
    let mut fields = Map::new();
    fields.insert(id("x"), num(1));
    let term = Term::Lit {
      value: Literal::StructUpdate {
        base: id("point"),
        fields,
      },
    };
    // `point` is a bound Lam parameter, not a global — base must resolve
    // to Bound(0), proving it goes through the same Bound/Free resolution
    // as any other variable occurrence, not stay a bare name.
    let wrapped = lam(param(id("point"), sort1()), term);
    match lower(&wrapped) {
      CoreTerm::Lam { body, .. } => match *body {
        CoreTerm::Lit(crate::core_term::CoreLit::StructUpdate { base, .. }) => {
          assert_eq!(*base, CoreTerm::Bound(0));
        }
        other => panic!("expected Lit::StructUpdate, got {other:?}"),
      },
      other => panic!("expected Lam, got {other:?}"),
    }
  }
}
