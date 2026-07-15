//! `CoreTerm` → `Term` raiser — B0 of
//! `plans/implementations/typechecker-de-bruijn-core.md`'s cutover phase.
//!
//! Converts a checked `CoreTerm` (locally-nameless: `Bound` for local
//! binders, `Free` for global references) back into the named surface
//! `Term` the rest of the pipeline (`eval.rs`, `lower.rs`, the kernel
//! evaluator, the REPL) still consumes. This is only ever called on a term
//! that has ALREADY been through `core_check::infer`/`check` successfully.
//!
//! `infer`/`check` never mutate the *term* being checked — they only
//! compute a *type* against it, and every place they open a binder to look
//! inside it (`infer`'s `Forall`/`Pi`/`Lam` arms) pairs that `open` with a
//! `close` before the result leaves the call, so no locally-opened `Free`
//! atom ever survives into a returned term or type. A `def`'s inferred
//! (rather than declared) type *can* contain unresolved `Meta`s, but only
//! ever as part of a *type* `core_check::infer` returns — never spliced
//! into the checked term itself — and the caller is expected to run
//! `core_unify::zonk` + `core_unify::generalize` on that type first (which
//! resolves every meta, or re-closes it as a fresh `Forall`/`Bound`) before
//! passing it to `raise_core`.
//!
//! By the time either a checked term or a zonked+generalized type reaches
//! this module, only `Bound` (properly scoped by an enclosing binder) and
//! `Free(atom)` remain — but a `Free` atom isn't always a reference to a
//! multi-segment global path: `core_check_module.rs`'s `peel_foralls`/
//! `LowerConfig::free_overrides` pins a def's own declared-type Forall
//! parameters to specific atoms, and reuses those SAME atoms when
//! lowering the def's BODY (so e.g. an inline `(a : A)` parameter
//! annotation resolves to the same atom as the declared type's
//! `Forall A`, not an unrelated global "A"). Every `Free(atom)` this
//! module raises is resolved uniformly through one `atom_paths: &Map<Atom,
//! ModulePath>` — for a def-local override, the caller mints a
//! single-segment `ModulePath` (`name.to_path()`) rather than a bare
//! `Identifier`, matching how a resolved `Var` reference is represented
//! everywhere else in this codebase (`NameRef::P` with a one-segment path
//! is the resolved form of what started as a bare name — see
//! `NameRef::as_id`/`to_path`) — so there's exactly one raised shape
//! (`NameRef::P`) for every `Free` atom, global or local.
//!
//! This is deliberately NOT a process-wide cache/`OnceLock` (this
//! project's established convention — `StructFields`/`ModuleCheckEnv`/
//! `LowerConfig` are all explicit parameters for the same reason): callers
//! already build and hold this exact information (`known_globals`,
//! `peel_foralls`'s per-def atom/name pairs) as part of their own
//! tracking, so passing it here costs nothing extra and keeps atom
//! resolution's dependency visible at every call site that needs it,
//! rather than hidden behind shared global state.
//!
//! Written as an explicit-stack (non-recursive) traversal over BORROWED
//! `&CoreTerm` nodes — never cloning the input tree, which (for a
//! `Box`-based recursive enum) would itself recurse via the derived
//! `Clone` impl just as deeply as naive recursive descent would — rather
//! than straightforward recursion, so raising a deeply-nested term (long
//! `App` spines from curried calls or piped operators, long `let` chains)
//! can't overflow the native call stack. The same reasoning applies to the
//! checker/evaluator generally, not just this module.

use crate::Map;
use crate::core_term::{
  Atom, CoreConstructor, CoreLit, CoreMatchCase, CoreNative, CoreTerm, DebugName,
};
use crate::term::{
  self, Identifier, Literal, MatchCase, ModulePath, Multiplicity, NameRef, Native, Par, Param, Term,
};

/// Raise a checked `CoreTerm` back into a named `Term`. `atom_paths` must
/// map every `Free` atom the term references back to its `ModulePath` —
/// a genuine multi-segment global path, or a single-segment
/// `name.to_path()` for a def-local override — see this module's doc
/// comment for the full explanation.
///
/// Panics if `term` contains a `Meta` (the caller forgot to
/// `zonk`+`generalize` a type first), a `Bound` with no enclosing binder in
/// view, or a `Free` atom missing from `atom_paths` (a locally-opened atom
/// that shouldn't have survived, or an incomplete `atom_paths` table) —
/// all three indicate a bug upstream, not a user-facing error.
pub fn raise_core(term: &CoreTerm, atom_paths: &Map<Atom, ModulePath>) -> Term {
  Raiser::new(atom_paths).run(term).into_term()
}

/// One traversal result: either an ordinary raised `Term`, or a raised
/// `MatchCase` — kept as a distinct variant (rather than trying to encode a
/// `MatchCase` as some `Term`) so a `Lit::Match`'s per-case sub-results can
/// travel through the same `results` stack as everything else without any
/// unsafe encoding, and be told apart from ordinary `Term`s when a `Reduce`
/// step drains them back off.
enum Res {
  Term(Term),
  Case(MatchCase),
}

impl Res {
  fn into_term(self) -> Term {
    match self {
      Res::Term(t) => t,
      Res::Case(_) => panic!("raise_core: expected a Term result, got a MatchCase"),
    }
  }
  fn into_case(self) -> MatchCase {
    match self {
      Res::Case(c) => c,
      Res::Term(_) => panic!("raise_core: expected a MatchCase result, got a Term"),
    }
  }
}

/// One pending unit of work in the iterative traversal. `Expand` mirrors
/// what a recursive call would do for one node — borrowing straight from
/// the original tree, never cloning it — `PushName`/`PopName` bracket a
/// binder's scope exactly where a recursive call would push/pop before and
/// after descending into a body; `Reduce` fires once all of a node's
/// children have produced their `Res`es (pushed onto `results`, in
/// left-to-right order) and combines them into the parent — the manual
/// equivalent of a recursive call's "now build the result from the
/// recursive sub-calls' return values" step. `Reduce`'s closure only ever
/// captures already-owned leaf data (small `Identifier`/`ModulePath`
/// clones) or already-produced `Res` values, never a borrow from the
/// original tree, so it needs no lifetime parameter of its own.
enum Item<'a> {
  Expand(&'a CoreTerm),
  PushName(Identifier),
  PopName,
  /// Pop the last `n` entries off `results` (in original left-to-right
  /// order — see `Raiser::run`) and push one combined `Res` in their place.
  Reduce(usize, Box<dyn FnOnce(Vec<Res>) -> Res>),
}

struct Raiser<'p> {
  /// Currently in-scope local binder names, innermost last (`Bound(0)`
  /// means the last-pushed name) — mirrors `core_term::Printer`'s own
  /// `names` stack and `lower_core::LowerContext`'s `bound: Vec<Identifier>`
  /// push/pop discipline exactly, since all three solve the identical
  /// "track which name a de Bruijn position currently refers to" problem.
  names: Vec<Identifier>,
  /// Caller-supplied `Atom` → `ModulePath` reverse lookup for global
  /// references — see this module's doc comment for why it's threaded in
  /// explicitly rather than read from a global table.
  atom_paths: &'p Map<Atom, ModulePath>,
}

impl<'p> Raiser<'p> {
  fn new(atom_paths: &'p Map<Atom, ModulePath>) -> Self {
    Raiser {
      names: Vec::new(),
      atom_paths,
    }
  }

  fn run<'a>(&mut self, term: &'a CoreTerm) -> Res {
    let mut work: Vec<Item<'a>> = vec![Item::Expand(term)];
    let mut results: Vec<Res> = Vec::new();
    while let Some(item) = work.pop() {
      match item {
        Item::PushName(name) => self.names.push(name),
        Item::PopName => {
          self.names.pop();
        }
        Item::Reduce(n, f) => {
          let len = results.len();
          let children = results.split_off(len - n);
          results.push(f(children));
        }
        Item::Expand(t) => self.expand(t, &mut work),
      }
    }
    results
      .pop()
      .expect("raise_core: traversal produced no result")
  }

  fn fresh_name(&self, dbg: &DebugName) -> Identifier {
    self.fresh_name_avoiding(dbg, &[])
  }

  /// Like `fresh_name`, but also disambiguates against `extra` — names
  /// already chosen for EARLIER pattern variables in the same `Match`
  /// case, which aren't in `self.names` yet (nothing's been pushed for
  /// this case at the point all its names are picked — see
  /// `push_match_case`) but still must not collide, or two positionally
  /// distinct pattern vars (e.g. `mk x x => ...`, legal since lowering
  /// tracks them by stack position, not name) would raise to the same
  /// `Identifier` and become indistinguishable in the named surface term.
  fn fresh_name_avoiding(&self, dbg: &DebugName, extra: &[Identifier]) -> Identifier {
    match dbg {
      DebugName::Named(id) => {
        let mut candidate = id.as_str().to_string();
        while self.names.iter().any(|n| n.as_str() == candidate)
          || extra.iter().any(|n| n.as_str() == candidate)
        {
          candidate.push('\'');
        }
        Identifier::new(candidate)
      }
      // A `Term` binder always needs *some* `Identifier`, even for a
      // position nothing ever references — gensym a throwaway one, same
      // idea `Identifier::gensym` already serves elsewhere.
      DebugName::Anonymous => Identifier::gensym("_anon"),
    }
  }

  /// Push the work items needed to raise `t`, in the reverse of their
  /// execution order (since `work` is a LIFO stack) — the non-recursive
  /// analogue of what a recursive `raise(t) -> Term` call's body would do.
  fn expand<'a>(&mut self, t: &'a CoreTerm, work: &mut Vec<Item<'a>>) {
    match t {
      CoreTerm::Bound(i) => {
        let i = *i;
        let len = self.names.len() as u32;
        let idx = len.checked_sub(1 + i).unwrap_or_else(|| {
          panic!(
            "raise_core: dangling Bound({i}) — term must be fully checked and closed before raising"
          )
        });
        let name = self.names[idx as usize].clone();
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Var {
              name: NameRef::Id(name),
            })
          }),
        ));
      }
      CoreTerm::Free(atom) => {
        let atom = *atom;
        let path = self.atom_paths.get(&atom).cloned().unwrap_or_else(|| {
          panic!(
            "raise_core: Free({atom:?}) is missing from atom_paths — a locally-opened atom leaked into a checked term, or atom_paths is incomplete"
          )
        });
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Var {
              name: NameRef::P(path),
            })
          }),
        ));
      }
      CoreTerm::Meta(m) => panic!(
        "raise_core: unresolved Meta({m:?}) — a def's inferred type must be zonk+generalize'd before raising"
      ),
      CoreTerm::Sort { level } => {
        let level = *level;
        work.push(Item::Reduce(
          0,
          Box::new(move |_| Res::Term(Term::Sort { level })),
        ));
      }
      CoreTerm::Hole => {
        work.push(Item::Reduce(0, Box::new(|_| Res::Term(Term::Hole))));
      }
      CoreTerm::Forall { dbg, typ, body } => {
        let name = self.fresh_name(dbg);
        let name2 = name.clone();
        work.push(Item::Reduce(
          2,
          Box::new(move |mut children| {
            let body_t = children.pop().unwrap().into_term();
            let typ_t = children.pop().unwrap().into_term();
            Res::Term(Term::Forall {
              name: name2,
              typ: Box::new(typ_t),
              body: Box::new(body_t),
            })
          }),
        ));
        work.push(Item::PopName);
        work.push(Item::Expand(body));
        work.push(Item::PushName(name));
        work.push(Item::Expand(typ));
      }
      CoreTerm::Pi {
        dbg,
        arg,
        ret,
        mult,
      } => {
        // Always give the raised `Pi` a real name for its argument (never
        // `None`), even when `dbg` is `Anonymous` — sidesteps having to
        // prove `ret` never structurally references `Bound(0)` in that
        // case (true in practice, since `lower_core`/`core_check` never
        // synthesize a dependent-but-unnamed Pi, but not worth relying on):
        // a name nothing references is harmless, while a `None` next to a
        // `ret` that secretly does reference it would raise a term nothing
        // downstream could bind correctly.
        let name = self.fresh_name(dbg);
        let name2 = name.clone();
        let mult = mult.clone();
        work.push(Item::Reduce(
          2,
          Box::new(move |mut children| {
            let ret_t = children.pop().unwrap().into_term();
            let arg_t = children.pop().unwrap().into_term();
            Res::Term(Term::Pi {
              arg_name: Some(name2),
              arg: Box::new(arg_t),
              ret: Box::new(ret_t),
              mult,
            })
          }),
        ));
        work.push(Item::PopName);
        work.push(Item::Expand(ret));
        work.push(Item::PushName(name));
        work.push(Item::Expand(arg));
      }
      CoreTerm::Lam {
        dbg,
        param_typ,
        body,
      } => {
        // `dbg: Anonymous` must raise back to `Par::I` (index-based, no
        // name at all), NOT `Par::P` with a made-up name — this is the
        // exact inverse of `lower_core.rs`'s own asymmetric `Par::I =>
        // DebugName::Anonymous` mapping, and it's load-bearing: natives
        // with explicit params (`def_with_native`, `term.rs`) are parsed
        // as a `Par::I`-lambda chain wrapping an unapplied `Ntv` whose
        // `args` are never substituted by NAME at all — the evaluator's
        // `Par::I`-application special-case fills the native's next `args`
        // slot positionally instead of doing ordinary name substitution
        // (there's nothing to substitute — the body never references the
        // param by name or index). Raising an Anonymous binder to `Par::P`
        // instead would make the evaluator treat it as an ordinary named
        // lambda, silently leaving every native's args permanently empty.
        let is_anonymous = matches!(dbg, DebugName::Anonymous);
        let name = self.fresh_name(dbg);
        let name2 = name.clone();
        work.push(Item::Reduce(
          2,
          Box::new(move |mut children| {
            let body_t = children.pop().unwrap().into_term();
            let typ_t = children.pop().unwrap().into_term();
            let param = if is_anonymous {
              Par::I {
                typ: Box::new(typ_t),
                mult: Multiplicity::Many,
              }
            } else {
              Par::P(Param {
                name: name2,
                typ: Box::new(typ_t),
                mult: Multiplicity::Many,
                default: None,
              })
            };
            Res::Term(Term::Lam {
              param,
              body: Box::new(body_t),
            })
          }),
        ));
        work.push(Item::PopName);
        work.push(Item::Expand(body));
        work.push(Item::PushName(name));
        work.push(Item::Expand(param_typ));
      }
      CoreTerm::App { fun, arg } => {
        work.push(Item::Reduce(
          2,
          Box::new(move |mut children| {
            let arg_t = children.pop().unwrap().into_term();
            let fun_t = children.pop().unwrap().into_term();
            Res::Term(Term::App {
              fun: Box::new(fun_t),
              arg: Box::new(arg_t),
            })
          }),
        ));
        work.push(Item::Expand(arg));
        work.push(Item::Expand(fun));
      }
      CoreTerm::Lit(lit) => self.expand_lit(lit, work),
      CoreTerm::Con(c) => self.expand_con(c, work),
      CoreTerm::Ntv(n) => self.expand_ntv(n, work),
    }
  }

  /// Push `Expand` items for a positional-argument slot list
  /// (`Con`/`Ntv`'s `Vec<Option<CoreTerm>>`), in reverse so they execute
  /// left-to-right. Returns nothing — callers already know each slot's
  /// `is_some()`-ness from the original `Vec<Option<CoreTerm>>` and use
  /// that (not this function) to reassemble in the `Reduce` closure.
  fn expand_args<'a>(&mut self, args: &'a [Option<CoreTerm>], work: &mut Vec<Item<'a>>) {
    for arg in args.iter().rev().filter_map(|a| a.as_ref()) {
      work.push(Item::Expand(arg));
    }
  }

  fn expand_con<'a>(&mut self, c: &'a CoreConstructor, work: &mut Vec<Item<'a>>) {
    // A shallow `Vec<bool>` presence mask, NOT `c.args.clone()` — an arg
    // slot can itself be an arbitrarily long chain of nested `Con`s (e.g.
    // a large `List.cons`-built list's tail), and cloning `CoreTerm`
    // recurses via its derived `Clone` impl exactly as deeply as naive
    // recursive descent would — the same pitfall `raise_core`'s top-level
    // borrow-instead-of-clone design exists to avoid in the first place.
    let presence: Vec<bool> = c.args.iter().map(Option::is_some).collect();
    let n = presence.iter().filter(|p| **p).count();
    let name = c.name.clone();
    let typ_name = c.typ_name.clone();
    work.push(Item::Reduce(
      n,
      Box::new(move |children| {
        let mut it = children.into_iter();
        let args: Vec<Option<Term>> = presence
          .iter()
          .map(|&present| present.then(|| it.next().unwrap().into_term()))
          .collect();
        Res::Term(Term::Con(term::constructor(name, typ_name, args)))
      }),
    ));
    self.expand_args(&c.args, work);
  }

  fn expand_ntv<'a>(&mut self, n: &'a CoreNative, work: &mut Vec<Item<'a>>) {
    // Same reasoning as `expand_con`: a shallow presence mask, never a
    // clone of the (potentially deeply nested) `CoreTerm` args themselves.
    let presence: Vec<bool> = n.args.iter().map(Option::is_some).collect();
    let count = presence.iter().filter(|p| **p).count();
    let native_name = n.native_name.clone();
    let num_args = n.num_args;
    work.push(Item::Reduce(
      count,
      Box::new(move |children| {
        let mut it = children.into_iter();
        let args: Vec<Option<Term>> = presence
          .iter()
          .map(|&present| present.then(|| it.next().unwrap().into_term()))
          .collect();
        Res::Term(Term::Ntv {
          native: Native {
            native_name,
            num_args,
            args,
          },
        })
      }),
    ));
    self.expand_args(&n.args, work);
  }

  fn expand_lit<'a>(&mut self, lit: &'a CoreLit, work: &mut Vec<Item<'a>>) {
    match lit {
      CoreLit::Str { value } => {
        let value = value.clone();
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Lit {
              value: Literal::Str { value },
            })
          }),
        ));
      }
      CoreLit::Char { value } => {
        let value = *value;
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Lit {
              value: Literal::Char { value },
            })
          }),
        ));
      }
      CoreLit::Num { value, suffix } => {
        let value = *value;
        let suffix = *suffix;
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Lit {
              value: Literal::Num { value, suffix },
            })
          }),
        ));
      }
      CoreLit::Float { value, suffix } => {
        let value = *value;
        let suffix = *suffix;
        work.push(Item::Reduce(
          0,
          Box::new(move |_| {
            Res::Term(Term::Lit {
              value: Literal::Float { value, suffix },
            })
          }),
        ));
      }
      CoreLit::If { cond, then, els } => {
        work.push(Item::Reduce(
          3,
          Box::new(move |mut children| {
            let els_t = children.pop().unwrap().into_term();
            let then_t = children.pop().unwrap().into_term();
            let value_t = children.pop().unwrap().into_term();
            Res::Term(Term::Lit {
              value: Literal::If {
                value: Box::new(value_t),
                then: Box::new(then_t),
                els: Box::new(els_t),
              },
            })
          }),
        ));
        work.push(Item::Expand(els));
        work.push(Item::Expand(then));
        work.push(Item::Expand(cond));
      }
      CoreLit::StructLit { fields, type_name } => {
        let keys: Vec<Identifier> = fields.keys().cloned().collect();
        let n = keys.len();
        let type_name_path = type_name.map(|atom| {
          self.atom_paths.get(&atom).cloned().unwrap_or_else(|| {
            panic!("raise_core: StructLit type_name Atom({atom:?}) is missing from atom_paths")
          })
        });
        work.push(Item::Reduce(
          n,
          Box::new(move |children| {
            let fields_t: crate::Map<Identifier, Term> = keys
              .into_iter()
              .zip(children.into_iter().map(Res::into_term))
              .collect();
            let type_name_t = type_name_path.map(|path| {
              Box::new(Term::Var {
                name: NameRef::P(path),
              })
            });
            Res::Term(Term::Lit {
              value: Literal::StructLit {
                fields: fields_t,
                type_name: type_name_t,
              },
            })
          }),
        ));
        for v in fields.values().rev() {
          work.push(Item::Expand(v));
        }
      }
      CoreLit::StructUpdate { base, fields } => {
        let keys: Vec<Identifier> = fields.keys().cloned().collect();
        let n = keys.len();
        work.push(Item::Reduce(
          1 + n,
          Box::new(move |mut children| {
            // `base` was expanded first, so it's at the FRONT of
            // `children` — split it off before zipping the rest against
            // `keys`.
            let field_results = children.split_off(1);
            let base_t = children.pop().unwrap().into_term();
            let base_id = match base_t {
              Term::Var {
                name: NameRef::Id(id),
              } => id,
              other => panic!(
                "raise_core: StructUpdate base must raise to a bare local Var, got {other:?}"
              ),
            };
            let fields_t: crate::Map<Identifier, Term> = keys
              .into_iter()
              .zip(field_results.into_iter().map(Res::into_term))
              .collect();
            Res::Term(Term::Lit {
              value: Literal::StructUpdate {
                base: base_id,
                fields: fields_t,
              },
            })
          }),
        ));
        for v in fields.values().rev() {
          work.push(Item::Expand(v));
        }
        work.push(Item::Expand(base));
      }
      CoreLit::Match { scrutinee, cases } => {
        let num_cases = cases.len();
        work.push(Item::Reduce(
          1 + num_cases,
          Box::new(move |mut children| {
            let case_results = children.split_off(1);
            let scrutinee_t = children.pop().unwrap().into_term();
            let cases_t: Vec<MatchCase> = case_results.into_iter().map(Res::into_case).collect();
            debug_assert_eq!(cases_t.len(), num_cases);
            Res::Term(Term::Lit {
              value: Literal::Match {
                value: Box::new(scrutinee_t),
                cases: cases_t,
              },
            })
          }),
        ));
        // Push each case's own (PushName* → Expand(value) → PopName* →
        // Reduce-into-Case) sequence, in reverse case order so cases
        // execute left-to-right; then the scrutinee, first.
        for case in cases.iter().rev() {
          self.push_match_case(case, work);
        }
        work.push(Item::Expand(scrutinee));
      }
    }
  }

  /// Push one `Lit::Match` case's work sequence: bind its `dbgs.len()`
  /// pattern variables (in declaration order — matching
  /// `lower_core::LowerContext`'s own push order exactly, so `Bound(0)`
  /// resolves to the LAST-declared pattern var, same convention `open_n`/
  /// `core_term::Printer` already use), raise `value` under that scope,
  /// then reduce into a single `Res::Case`.
  fn push_match_case<'a>(&self, case: &'a CoreMatchCase, work: &mut Vec<Item<'a>>) {
    let mut names: Vec<Identifier> = Vec::with_capacity(case.dbgs.len());
    for dbg in &case.dbgs {
      names.push(self.fresh_name_avoiding(dbg, &names));
    }
    let case_name = case.name.clone();
    let names_for_reduce = names.clone();
    work.push(Item::Reduce(
      1,
      Box::new(move |mut children| {
        let value_t = children.pop().unwrap().into_term();
        Res::Case(term::case(case_name, names_for_reduce, value_t))
      }),
    ));
    for _ in &names {
      work.push(Item::PopName);
    }
    work.push(Item::Expand(&case.value));
    for name in names.into_iter().rev() {
      work.push(Item::PushName(name));
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::core_term::AtomTable;
  use crate::lower_core::{LowerContext, lower_term};
  use crate::term::{
    ModulePath, app, case, constructor, forall, id, if_term, lam, match_term, num, param, pi,
    sort0, sort1, str, var,
  };

  fn lower(t: &Term, atoms: &mut AtomTable) -> CoreTerm {
    lower_term(&mut LowerContext::new(atoms), t).expect("lowering should succeed")
  }

  /// Build the `atom_paths` reverse lookup `raise_core` needs, for
  /// whichever global names (bare top-level module paths, e.g. `"Bool"`)
  /// a test fixture references — mints each via `core_term::global_atom`
  /// (the same, unchanged, process-wide forward table `lower_term` itself
  /// uses internally) and records the reverse mapping explicitly, exactly
  /// as a real caller (`core_check_module.rs`) would from its own
  /// `known_globals` tracking.
  fn atom_paths(names: &[&str], atoms: &mut AtomTable) -> Map<Atom, ModulePath> {
    names
      .iter()
      .map(|n| {
        let path = ModulePath::top(n);
        let atom = atoms.intern(path.clone());
        (atom, path)
      })
      .collect()
  }

  /// Round-trip through `raise_core` and back: lowering the RAISED term
  /// again must produce a `CoreTerm` alpha-equivalent to the original.
  /// `CoreTerm`'s derived `PartialEq` already ignores `DebugName` (see
  /// `core_term.rs`), so this comparison is exactly the alpha-equivalence
  /// check the plan calls for — it doesn't matter if raising happened to
  /// pick different concrete names than the original source used.
  fn assert_round_trips(t: &Term) {
    assert_round_trips_with_globals(t, &[]);
  }

  /// Like `assert_round_trips`, but for a fixture that references global
  /// names (e.g. `var("Bool")`) — `globals` lists them so `atom_paths` can
  /// build the reverse lookup `raise_core` needs.
  fn assert_round_trips_with_globals(t: &Term, globals: &[&str]) {
    let mut atoms = AtomTable::new();
    let original = lower(t, &mut atoms);
    let paths = atom_paths(globals, &mut atoms);
    let raised = raise_core(&original, &paths);
    let reloaded = lower(&raised, &mut atoms);
    assert_eq!(
      original, reloaded,
      "raise_core(lower(t)) must round-trip up to alpha-equivalence\noriginal: {original}\nraised:   {raised}\nreloaded: {reloaded}"
    );
  }

  #[test]
  fn test_round_trip_identity_lambda() {
    assert_round_trips(&lam(param(id("a"), sort0()), var("a")));
  }

  #[test]
  fn test_round_trip_forall_pi() {
    assert_round_trips(&forall(param(id("A"), sort1()), pi(var("A"), var("A"))));
  }

  #[test]
  fn test_round_trip_nested_lambdas_and_app() {
    let f = lam(
      param(id("a"), sort0()),
      lam(param(id("b"), sort0()), var("a")),
    );
    assert_round_trips(&app(app(f, sort0()), sort0()));
  }

  #[test]
  fn test_round_trip_shadowed_names() {
    // (fn x => (fn x => x)) — inner x shadows outer x; the raiser's own
    // disambiguation must still round-trip correctly (it doesn't need to
    // preserve the exact shadowed spelling, just the alpha-equivalence
    // class).
    let t = lam(
      param(id("x"), sort0()),
      lam(param(id("x"), sort0()), var("x")),
    );
    assert_round_trips(&t);
  }

  #[test]
  fn test_round_trip_if() {
    assert_round_trips_with_globals(
      &lam(
        param(id("cond"), var("Bool")),
        if_term(var("cond"), num(1), num(2)),
      ),
      &["Bool"],
    );
  }

  #[test]
  fn test_round_trip_str_literal() {
    assert_round_trips(&str("hello"));
  }

  #[test]
  fn test_round_trip_match_no_pattern_args() {
    let t = lam(
      param(id("xs"), sort1()),
      match_term(
        var("xs"),
        vec![case(id("a"), vec![], num(1)), case(id("b"), vec![], num(2))],
      ),
    );
    assert_round_trips(&t);
  }

  #[test]
  fn test_round_trip_match_with_pattern_args() {
    // match xs { cons h t => h }
    let t = lam(
      param(id("xs"), sort1()),
      match_term(
        var("xs"),
        vec![case(id("cons"), vec![id("h"), id("t")], var("h"))],
      ),
    );
    assert_round_trips(&t);
  }

  #[test]
  fn test_round_trip_match_case_with_duplicate_pattern_names() {
    // match xs { mk x x => x } — two positionally-distinct pattern vars
    // that happen to share a source name; the raiser must disambiguate
    // them (see fresh_name_avoiding's doc comment) rather than collapsing
    // both into the same raised Identifier.
    let t = lam(
      param(id("xs"), sort1()),
      match_term(
        var("xs"),
        vec![case(id("mk"), vec![id("x"), id("x")], var("x"))],
      ),
    );
    assert_round_trips(&t);
  }

  #[test]
  fn test_round_trip_con() {
    let c = constructor(id("empty"), ModulePath::top("List"), vec![]);
    assert_round_trips(&Term::Con(c));
  }

  #[test]
  fn test_round_trip_con_with_args() {
    let c = constructor(
      id("cons"),
      ModulePath::top("List"),
      vec![Some(num(1)), Some(num(2))],
    );
    assert_round_trips(&Term::Con(c));
  }

  // -------------------------------------------------------------------
  // Stack safety: the whole reason `raise_core` is written as an
  // explicit-stack traversal rather than recursive descent — a depth
  // that would overflow a naive recursive implementation's native call
  // stack must not overflow this one.
  // -------------------------------------------------------------------

  #[test]
  fn test_raise_deeply_nested_app_does_not_overflow_stack() {
    // The exact shape a long curried/piped call chain desugars to
    // (`f a1 a2 ... aN`, left-nested `App`). Built iteratively (not
    // recursively) too, so constructing the fixture itself can't be the
    // thing that overflows.
    let depth = 20_000;
    let fn_path = ModulePath::top("raise_core_test_stack_fn");
    let fn_atom = AtomTable::new().intern(fn_path.clone());
    let paths: Map<Atom, ModulePath> = [(fn_atom, fn_path)].into_iter().collect();
    let mut term = CoreTerm::Free(fn_atom);
    let arg = CoreTerm::Sort { level: 0 };
    for _ in 0..depth {
      term = CoreTerm::App {
        fun: Box::new(term),
        arg: Box::new(arg.clone()),
      };
    }
    let raised = raise_core(&term, &paths);
    match &raised {
      Term::App { .. } => {}
      other => panic!("expected App at the top, got {other:?}"),
    }
    // The resulting `Term`/`CoreTerm` chains are ~20,000 `Box` deep;
    // Rust's default (recursive) `Drop` for nested `Box` fields would
    // itself risk a stack overflow on drop — an orthogonal, pre-existing
    // property of any `Box`-based recursive ADT, not something
    // `raise_core`'s own traversal does. Leak them deliberately so this
    // test stays isolated to what it's actually checking.
    std::mem::forget(term);
    std::mem::forget(raised);
  }

  #[test]
  fn test_raise_deeply_nested_lam_does_not_overflow_stack() {
    // `Anonymous` (gensym'd, no collision scan) deliberately, not a
    // shared `Named` debug name repeated at every level — this test is
    // only about traversal stack depth; `fresh_name_avoiding`'s
    // disambiguation scan against `self.names` is a separate, known
    // O(depth) lookup per binder (fine for realistic nesting, but would
    // make an already-extreme synthetic depth like this one needlessly
    // slow for a property it isn't testing).
    let depth = 20_000;
    let mut term = CoreTerm::Bound(0);
    for _ in 0..depth {
      term = CoreTerm::Lam {
        dbg: DebugName::Anonymous,
        param_typ: Box::new(CoreTerm::Sort { level: 0 }),
        body: Box::new(term),
      };
    }
    let raised = raise_core(&term, &Map::new());
    match &raised {
      Term::Lam { .. } => {}
      other => panic!("expected Lam at the top, got {other:?}"),
    }
    std::mem::forget(term);
    std::mem::forget(raised);
  }
}
