//! Locally-nameless core term for the type checker.
//!
//! See `plans/implementations/typechecker-de-bruijn-core.md`. `CoreTerm` is
//! the type checker's internal representation, distinct from
//! `crate::term::Term` (the parser/macro-facing named surface term, which
//! is unchanged — macro hygiene and `Quote`/reflection fundamentally need
//! names, so they keep operating on `Term`).
//!
//! Representation is *locally nameless* (Chargueraud): a bound variable
//! occurrence is a de Bruijn index (`Bound`), while every free variable —
//! whether a rigid/skolem variable produced by opening a binder, or a
//! unification metavariable — is a small globally-unique atom (`Free`/
//! `Meta`), never a string. Two `CoreTerm`s are `==` iff they are
//! alpha-equivalent: `DebugName`, carried on every binder purely for error
//! messages and pretty-printing, never participates in equality, hashing,
//! or ordering (see its custom impls below).
//!
//! This is Phase 0 of the plan: the type itself, substitution primitives,
//! and a name-environment pretty-printer, with unit tests only — no
//! lowering pass and no unifier yet (Phases 1+).

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::Map;
use crate::term::{F64Wrap, Identifier, ModulePath, Multiplicity, NumSuffix};

// ---------------------------------------------------------------------------
// DebugName — display-only, never used for identity
// ---------------------------------------------------------------------------

/// A name kept solely for error messages/pretty-printing. Never used for
/// identity: binder identity is the `Bound` index (relative occurrences)
/// or the `Atom`/`MetaId` (opened/metavariable occurrences), never this.
#[derive(Debug, Clone)]
pub enum DebugName {
  Named(Identifier),
  Anonymous,
}

impl DebugName {
  pub fn as_str(&self) -> &str {
    match self {
      DebugName::Named(id) => id.as_str(),
      DebugName::Anonymous => "_",
    }
  }
}

// `DebugName` is deliberately excluded from equality/hash/ordering: any two
// `DebugName`s compare equal and hash identically, so a `CoreTerm`'s derived
// `PartialEq`/`Hash`/`Ord` (which recurse into this field like any other)
// end up ignoring it entirely — alpha-equivalence falls out of `derive`
// automatically instead of needing to be remembered at every call site.
impl PartialEq for DebugName {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}
impl Eq for DebugName {}
impl std::hash::Hash for DebugName {
  fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}
impl PartialOrd for DebugName {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for DebugName {
  fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
    std::cmp::Ordering::Equal
  }
}

// ---------------------------------------------------------------------------
// Atom / MetaId — globally-unique identity, never a name
// ---------------------------------------------------------------------------

fn fresh_id() -> u64 {
  static NEXT: AtomicU64 = AtomicU64::new(1);
  NEXT.fetch_add(1, Ordering::SeqCst)
}

/// Identity of one rigid/free variable — an opened binder, or a resolved
/// top-level global reference. Two atoms are equal iff they are the exact
/// same allocation; no two calls to `Atom::fresh()` ever collide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Atom(u64);

impl Atom {
  pub fn fresh() -> Atom {
    Atom(fresh_id())
  }
}

impl fmt::Display for Atom {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "@{}", self.0)
  }
}

/// Identity of one unification metavariable. Distinct type from `Atom` so
/// "rigid variable" and "still-to-be-solved variable" can never be
/// confused at the type level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MetaId(u64);

impl MetaId {
  pub fn fresh() -> MetaId {
    MetaId(fresh_id())
  }
}

impl fmt::Display for MetaId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "?{}", self.0)
  }
}

/// Interning table for `ModulePath` → `Atom`, so that every reference to
/// the same global name — across every lowering-pass call for one
/// checking run, not just within one — resolves to the same `Atom`.
/// Without this, two separate `lower_term` invocations (e.g. lowering two
/// different `def`s that both reference `List.any`) would mint two
/// different atoms for the same global, breaking unification between
/// them. An explicit, caller-owned table (constructed once per checking
/// run and threaded through as a `&mut` parameter — see
/// `lower_core::LowerContext`'s own `atoms` field and every
/// `core_check`/`core_check_module` function that takes `atoms: &mut
/// AtomTable`) rather than a process-wide `OnceLock`/`Mutex`: a global
/// would leak atoms across unrelated checking runs sharing one process
/// (e.g. the CLI test harness, which checks many independent files in a
/// single process) and requires a lock on every single lookup for no
/// benefit, since nothing here is actually run concurrently.
#[derive(Debug, Clone, Default)]
pub struct AtomTable(Map<ModulePath, Atom>);

impl AtomTable {
  pub fn new() -> Self {
    Self::default()
  }

  /// The `Atom` identifying a given global name, allocating one on first
  /// use and reusing it on every subsequent call through THIS table —
  /// the single source of truth both the lowering pass
  /// (`lower_core::LowerContext::global_atom`) and any code needing a
  /// canonical primitive-type atom (e.g. `core_check` inferring a
  /// literal's type) must go through, instead of each keeping its own
  /// private, inconsistent table.
  pub fn intern(&mut self, path: ModulePath) -> Atom {
    *self.0.entry(path).or_insert_with(Atom::fresh)
  }

  /// Reverse lookup for error rendering only — an `Atom`'s originating
  /// `ModulePath`, if this table interned one for it. A linear scan is
  /// fine here: only ever called on an already-failed check's error path
  /// (rendering a handful of `Diagnostic` messages), never in the hot
  /// path of checking itself.
  pub fn path_of(&self, atom: Atom) -> Option<&ModulePath> {
    self.0.iter().find(|(_, a)| **a == atom).map(|(p, _)| p)
  }
}

// ---------------------------------------------------------------------------
// CoreTerm
// ---------------------------------------------------------------------------

/// A single `match` case: binds `dbgs.len()` pattern variables in `value`
/// (as a block of `dbgs.len()` simultaneous binders — see `open_at`'s
/// `Lit::Match` arm). `name` is the constructor tag being matched — a
/// fixed, globally-known label, not a binder, so it stays a plain
/// `Identifier` (no alpha-equivalence concern: two cases naming the same
/// constructor really do mean the same case).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CoreMatchCase {
  pub name: Identifier,
  pub dbgs: Vec<DebugName>,
  pub value: Box<CoreTerm>,
}

/// An inductive constructor application. `name`/`typ_name` identify a
/// fixed, globally-known constructor/type (e.g. `List.cons`/`List`) —
/// like `CoreMatchCase::name`, these are labels, not binders, so plain
/// `Identifier`/`ModulePath` is correct here, not `Atom`. `args` are
/// positional slots (mirrors `crate::term::Constructor`), filled
/// progressively as the constructor is curried — not binders either, just
/// ordinary subterms at the same depth as their parent.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CoreConstructor {
  pub name: Identifier,
  pub typ_name: ModulePath,
  pub num_args: usize,
  pub args: Vec<Option<CoreTerm>>,
}

/// A native/primitive call (mirrors `crate::term::Native`) — same
/// positional-argument shape as `CoreConstructor`, for compiler-builtin
/// operations rather than user-defined constructors.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CoreNative {
  pub native_name: Identifier,
  pub num_args: usize,
  pub args: Vec<Option<CoreTerm>>,
}

/// Mirrors `crate::term::Literal`, minus the two runtime-only variants
/// (`Term`/`Foreign`, which only ever appear as *evaluation results*, not
/// user-written source the type checker needs to check) — see this
/// module's and `lower_core`'s doc comments.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CoreLit {
  Str {
    value: String,
  },
  Char {
    value: char,
  },
  Num {
    value: i64,
    suffix: NumSuffix,
  },
  Float {
    value: F64Wrap,
    suffix: NumSuffix,
  },
  Match {
    scrutinee: Box<CoreTerm>,
    cases: Vec<CoreMatchCase>,
  },
  If {
    cond: Box<CoreTerm>,
    then: Box<CoreTerm>,
    els: Box<CoreTerm>,
  },
  StructLit {
    fields: Map<Identifier, CoreTerm>,
    /// Lowered form of `term::Literal::StructLit`'s optional `{ ... :
    /// StructType }` annotation — resolved to the struct's own atom at
    /// lowering time, the same way any other global name reference is
    /// resolved (`lower_var`/`resolve_free_name`), so `core_check::check`
    /// can look it up in a `StructFields` registry directly instead of
    /// needing to re-resolve a name itself.
    type_name: Option<Atom>,
  },
  /// Unlike `crate::term::Literal::StructUpdate` (whose `base` is a bare
  /// `Identifier`), `base` here is a resolved `CoreTerm` — `base` is a
  /// genuine *variable occurrence* (the struct value being updated), not
  /// a label, so it must go through the same `Bound`/`Free` resolution as
  /// any other variable reference, not stay a name.
  StructUpdate {
    base: Box<CoreTerm>,
    fields: Map<Identifier, CoreTerm>,
  },
}

#[derive(Debug, Clone)]
pub enum CoreTerm {
  /// De Bruijn index: a bound-variable occurrence, counted from its
  /// nearest enclosing binder (0 = innermost).
  Bound(u32),
  /// A rigid/skolem variable — produced by "opening" a binder to inspect
  /// its body, or naming a resolved top-level global. Two `Free`s are the
  /// same variable iff their atoms are equal — never by comparing names.
  Free(Atom),
  /// A unification metavariable, not yet (or provisionally) solved.
  Meta(MetaId),

  Forall {
    dbg: DebugName,
    typ: Box<CoreTerm>,
    body: Box<CoreTerm>,
  },
  Pi {
    dbg: DebugName,
    arg: Box<CoreTerm>,
    ret: Box<CoreTerm>,
    mult: Multiplicity,
  },
  Lam {
    dbg: DebugName,
    param_typ: Box<CoreTerm>,
    body: Box<CoreTerm>,
  },
  App {
    fun: Box<CoreTerm>,
    arg: Box<CoreTerm>,
  },

  Sort {
    level: u64,
  },
  Hole,

  Lit(CoreLit),
  Con(CoreConstructor),
  Ntv(CoreNative),

  /// Transparent source-location wrapper, added for
  /// `plans/implementations/typechecker-de-bruijn-core.md`'s Diagnostics
  /// follow-up — carries a `SourceRange` for error attribution without
  /// being a "real" term shape of its own. `Quote`/`Ann` still stay
  /// surface-only (unrelated to location tracking).
  ///
  /// Deliberately excluded from `PartialEq`/`Eq`/`Hash` (see the manual
  /// impls below, which strip `Ctx` before comparing/hashing) — a
  /// `Ctx`-wrapped term must be indistinguishable from its unwrapped
  /// inner term to every EXISTING equality-based check in the unifier
  /// (fast-path `a == b` comparisons, etc.), exactly like `DebugName` is
  /// excluded for binder names. Anything that inspects a `CoreTerm`'s
  /// *shape* via `match`, on the other hand, cannot be made transparent
  /// this way (Rust's `match` doesn't go through `PartialEq`) — those
  /// call `strip_ctx`/`strip_ctx_loc` explicitly; the compiler flags
  /// every exhaustive match that doesn't handle this variant yet.
  Ctx {
    loc: crate::term::SourceRange,
    term: Box<CoreTerm>,
  },
}

impl CoreTerm {
  /// Peel any number of nested `Ctx` wrappers, returning the innermost
  /// non-`Ctx` term. Every function that inspects a `CoreTerm`'s shape
  /// (rather than just recursing into an already-known field) should
  /// call this — or `strip_ctx_loc` — before matching, so a `Ctx`
  /// wrapper can never cause a real `Forall`/`Pi`/`App`/etc. to look like
  /// an unrecognized shape.
  pub fn strip_ctx(&self) -> &CoreTerm {
    let mut t = self;
    while let CoreTerm::Ctx { term, .. } = t {
      t = term;
    }
    t
  }

  /// Like `strip_ctx`, but also returns the OUTERMOST wrapper's location
  /// (if there was at least one) — the position an error about this term
  /// should be attributed to, since that's the location closest to what
  /// the user actually wrote (an inner `Ctx`, if any, belongs to a
  /// sub-term nested further down, not this term as a whole).
  pub fn strip_ctx_loc(&self) -> (&CoreTerm, Option<&crate::term::SourceRange>) {
    match self {
      CoreTerm::Ctx { loc, term } => (term.strip_ctx(), Some(loc)),
      other => (other, None),
    }
  }

  /// Owned equivalent of `strip_ctx` — for callers that already have (or
  /// need) an owned `CoreTerm` and want to match on it by value (moving
  /// fields out of it) rather than by reference.
  pub fn into_stripped_ctx(self) -> CoreTerm {
    let mut t = self;
    while let CoreTerm::Ctx { term, .. } = t {
      t = *term;
    }
    t
  }
}

impl PartialEq for CoreTerm {
  fn eq(&self, other: &Self) -> bool {
    use CoreTerm::*;
    match (self.strip_ctx(), other.strip_ctx()) {
      (Bound(a), Bound(b)) => a == b,
      (Free(a), Free(b)) => a == b,
      (Meta(a), Meta(b)) => a == b,
      (
        Forall {
          typ: t1, body: b1, ..
        },
        Forall {
          typ: t2, body: b2, ..
        },
      ) => t1 == t2 && b1 == b2,
      (
        Pi {
          arg: a1,
          ret: r1,
          mult: m1,
          ..
        },
        Pi {
          arg: a2,
          ret: r2,
          mult: m2,
          ..
        },
      ) => a1 == a2 && r1 == r2 && m1 == m2,
      (
        Lam {
          param_typ: p1,
          body: b1,
          ..
        },
        Lam {
          param_typ: p2,
          body: b2,
          ..
        },
      ) => p1 == p2 && b1 == b2,
      (App { fun: f1, arg: a1 }, App { fun: f2, arg: a2 }) => f1 == f2 && a1 == a2,
      (Sort { level: l1 }, Sort { level: l2 }) => l1 == l2,
      (Hole, Hole) => true,
      (Lit(a), Lit(b)) => a == b,
      (Con(a), Con(b)) => a == b,
      (Ntv(a), Ntv(b)) => a == b,
      _ => false,
    }
  }
}
impl Eq for CoreTerm {}

impl std::hash::Hash for CoreTerm {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    use CoreTerm::*;
    // Discriminant tag first (on the STRIPPED term, so a `Ctx`-wrapped
    // value hashes identically to its unwrapped form, consistent with
    // the `PartialEq` impl above — required: equal values must hash
    // equally).
    match self.strip_ctx() {
      Bound(i) => {
        0u8.hash(state);
        i.hash(state);
      }
      Free(a) => {
        1u8.hash(state);
        a.hash(state);
      }
      Meta(m) => {
        2u8.hash(state);
        m.hash(state);
      }
      Forall { typ, body, .. } => {
        3u8.hash(state);
        typ.hash(state);
        body.hash(state);
      }
      Pi { arg, ret, mult, .. } => {
        4u8.hash(state);
        arg.hash(state);
        ret.hash(state);
        mult.hash(state);
      }
      Lam {
        param_typ, body, ..
      } => {
        5u8.hash(state);
        param_typ.hash(state);
        body.hash(state);
      }
      App { fun, arg } => {
        6u8.hash(state);
        fun.hash(state);
        arg.hash(state);
      }
      Sort { level } => {
        7u8.hash(state);
        level.hash(state);
      }
      Hole => 8u8.hash(state),
      Lit(l) => {
        9u8.hash(state);
        l.hash(state);
      }
      Con(c) => {
        10u8.hash(state);
        c.hash(state);
      }
      Ntv(n) => {
        11u8.hash(state);
        n.hash(state);
      }
      Ctx { .. } => unreachable!("strip_ctx never returns a Ctx"),
    }
  }
}

/// Discriminant order for `Ord`/`PartialOrd` below — arbitrary (no
/// consumer relies on any particular ordering, only that it's total and
/// consistent with `PartialEq`/`Hash`), matching the tag order already
/// used by the `Hash` impl above.
fn core_term_rank(t: &CoreTerm) -> u8 {
  use CoreTerm::*;
  match t {
    Bound(_) => 0,
    Free(_) => 1,
    Meta(_) => 2,
    Forall { .. } => 3,
    Pi { .. } => 4,
    Lam { .. } => 5,
    App { .. } => 6,
    Sort { .. } => 7,
    Hole => 8,
    Lit(_) => 9,
    Con(_) => 10,
    Ntv(_) => 11,
    Ctx { .. } => unreachable!("only called on an already-stripped term"),
  }
}

impl PartialOrd for CoreTerm {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for CoreTerm {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    use CoreTerm::*;
    let (a, b) = (self.strip_ctx(), other.strip_ctx());
    match (a, b) {
      (Bound(x), Bound(y)) => x.cmp(y),
      (Free(x), Free(y)) => x.cmp(y),
      (Meta(x), Meta(y)) => x.cmp(y),
      (
        Forall {
          typ: t1, body: b1, ..
        },
        Forall {
          typ: t2, body: b2, ..
        },
      ) => t1.cmp(t2).then_with(|| b1.cmp(b2)),
      (
        Pi {
          arg: a1,
          ret: r1,
          mult: m1,
          ..
        },
        Pi {
          arg: a2,
          ret: r2,
          mult: m2,
          ..
        },
      ) => a1.cmp(a2).then_with(|| r1.cmp(r2)).then_with(|| m1.cmp(m2)),
      (
        Lam {
          param_typ: p1,
          body: b1,
          ..
        },
        Lam {
          param_typ: p2,
          body: b2,
          ..
        },
      ) => p1.cmp(p2).then_with(|| b1.cmp(b2)),
      (App { fun: f1, arg: a1 }, App { fun: f2, arg: a2 }) => f1.cmp(f2).then_with(|| a1.cmp(a2)),
      (Sort { level: l1 }, Sort { level: l2 }) => l1.cmp(l2),
      (Hole, Hole) => std::cmp::Ordering::Equal,
      (Lit(x), Lit(y)) => x.cmp(y),
      (Con(x), Con(y)) => x.cmp(y),
      (Ntv(x), Ntv(y)) => x.cmp(y),
      _ => core_term_rank(a).cmp(&core_term_rank(b)),
    }
  }
}

// ---------------------------------------------------------------------------
// Locally-nameless open/close — the only index arithmetic this
// representation needs (no general shift/subst: substituting a solved
// metavariable or a `Free` atom never needs to shift anything, since
// neither ever contains a "loose" `Bound` of its own — see subst_meta
// below).
// ---------------------------------------------------------------------------

/// Replace `Bound(depth)` with `replacement` throughout `term`, where
/// `replacement` must not itself contain any `Bound` occurrence relative to
/// this position (in practice always a `Free`/`Meta` leaf). Indices other
/// than `depth` are left completely untouched: unlike classic de Bruijn
/// substitution, no binder is being removed from the surrounding
/// structure — we're only describing what one binder's body looks like
/// with its own immediate variable swapped out for local inspection, so
/// references to *enclosing* binders (higher indices) stay exactly as they
/// were.
pub(crate) fn open_at(term: &CoreTerm, depth: u32, replacement: &CoreTerm) -> CoreTerm {
  match term {
    CoreTerm::Bound(i) if *i == depth => replacement.clone(),
    CoreTerm::Bound(_)
    | CoreTerm::Free(_)
    | CoreTerm::Meta(_)
    | CoreTerm::Sort { .. }
    | CoreTerm::Hole => term.clone(),
    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(open_at(typ, depth, replacement)),
      body: Box::new(open_at(body, depth + 1, replacement)),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(open_at(arg, depth, replacement)),
      ret: Box::new(open_at(ret, depth + 1, replacement)),
      mult: mult.clone(),
    },
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => CoreTerm::Lam {
      dbg: dbg.clone(),
      param_typ: Box::new(open_at(param_typ, depth, replacement)),
      body: Box::new(open_at(body, depth + 1, replacement)),
    },
    CoreTerm::App { fun, arg } => CoreTerm::App {
      fun: Box::new(open_at(fun, depth, replacement)),
      arg: Box::new(open_at(arg, depth, replacement)),
    },
    CoreTerm::Lit(lit) => CoreTerm::Lit(open_at_lit(lit, depth, replacement)),
    CoreTerm::Con(c) => CoreTerm::Con(CoreConstructor {
      name: c.name.clone(),
      typ_name: c.typ_name.clone(),
      num_args: c.num_args,
      args: open_at_args(&c.args, depth, replacement),
    }),
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: open_at_args(&n.args, depth, replacement),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(open_at(term, depth, replacement)),
    },
  }
}

fn open_at_args(
  args: &[Option<CoreTerm>],
  depth: u32,
  replacement: &CoreTerm,
) -> Vec<Option<CoreTerm>> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| open_at(t, depth, replacement)))
    .collect()
}

fn open_at_lit(lit: &CoreLit, depth: u32, replacement: &CoreTerm) -> CoreLit {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      lit.clone()
    }
    CoreLit::Match { scrutinee, cases } => CoreLit::Match {
      scrutinee: Box::new(open_at(scrutinee, depth, replacement)),
      cases: cases
        .iter()
        .map(|c| CoreMatchCase {
          name: c.name.clone(),
          dbgs: c.dbgs.clone(),
          value: Box::new(open_at(&c.value, depth + c.dbgs.len() as u32, replacement)),
        })
        .collect(),
    },
    CoreLit::If { cond, then, els } => CoreLit::If {
      cond: Box::new(open_at(cond, depth, replacement)),
      then: Box::new(open_at(then, depth, replacement)),
      els: Box::new(open_at(els, depth, replacement)),
    },
    CoreLit::StructLit { fields, type_name } => CoreLit::StructLit {
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), open_at(v, depth, replacement)))
        .collect(),
      type_name: *type_name,
    },
    CoreLit::StructUpdate { base, fields } => CoreLit::StructUpdate {
      base: Box::new(open_at(base, depth, replacement)),
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), open_at(v, depth, replacement)))
        .collect(),
    },
  }
}

/// Open the outermost bound variable of `body` (as extracted from inside a
/// `Forall`/`Pi`/`Lam` node) with a fresh `Free` atom, returning that atom
/// alongside the opened term so callers can push its type onto a typing
/// context and later `close` over it again (e.g. at generalization).
pub fn open(body: &CoreTerm) -> (Atom, CoreTerm) {
  let atom = Atom::fresh();
  (atom, open_at(body, 0, &CoreTerm::Free(atom)))
}

/// Open with a specific replacement term instead of a fresh atom — used
/// for instantiating a `Forall`/`Pi`/`Lam` binder with a concrete argument
/// (beta-reduction-style), rather than opening it for inspection.
/// `replacement` must not contain a `Bound` referring to a binder outside
/// itself (i.e. must be closed relative to this position) — true for both
/// `Free`/`Meta` leaves and for zonked concrete terms built via `open`.
pub fn open_with(body: &CoreTerm, replacement: &CoreTerm) -> CoreTerm {
  open_at(body, 0, replacement)
}

/// Replace every occurrence of `Free(atom)` with `Bound(depth)` — the
/// reverse of `open`, used when re-abstracting a term at generalization
/// (closing a fresh `Forall`/`Pi`/`Lam` binder over a specific atom that
/// occurred free in it).
fn close_at(term: &CoreTerm, depth: u32, atom: Atom) -> CoreTerm {
  match term {
    CoreTerm::Free(a) if *a == atom => CoreTerm::Bound(depth),
    CoreTerm::Bound(_)
    | CoreTerm::Free(_)
    | CoreTerm::Meta(_)
    | CoreTerm::Sort { .. }
    | CoreTerm::Hole => term.clone(),
    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(close_at(typ, depth, atom)),
      body: Box::new(close_at(body, depth + 1, atom)),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(close_at(arg, depth, atom)),
      ret: Box::new(close_at(ret, depth + 1, atom)),
      mult: mult.clone(),
    },
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => CoreTerm::Lam {
      dbg: dbg.clone(),
      param_typ: Box::new(close_at(param_typ, depth, atom)),
      body: Box::new(close_at(body, depth + 1, atom)),
    },
    CoreTerm::App { fun, arg } => CoreTerm::App {
      fun: Box::new(close_at(fun, depth, atom)),
      arg: Box::new(close_at(arg, depth, atom)),
    },
    CoreTerm::Lit(lit) => CoreTerm::Lit(close_at_lit(lit, depth, atom)),
    CoreTerm::Con(c) => CoreTerm::Con(CoreConstructor {
      name: c.name.clone(),
      typ_name: c.typ_name.clone(),
      num_args: c.num_args,
      args: close_at_args(&c.args, depth, atom),
    }),
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: close_at_args(&n.args, depth, atom),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(close_at(term, depth, atom)),
    },
  }
}

fn close_at_args(args: &[Option<CoreTerm>], depth: u32, atom: Atom) -> Vec<Option<CoreTerm>> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| close_at(t, depth, atom)))
    .collect()
}

fn close_at_lit(lit: &CoreLit, depth: u32, atom: Atom) -> CoreLit {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      lit.clone()
    }
    CoreLit::Match { scrutinee, cases } => CoreLit::Match {
      scrutinee: Box::new(close_at(scrutinee, depth, atom)),
      cases: cases
        .iter()
        .map(|c| CoreMatchCase {
          name: c.name.clone(),
          dbgs: c.dbgs.clone(),
          value: Box::new(close_at(&c.value, depth + c.dbgs.len() as u32, atom)),
        })
        .collect(),
    },
    CoreLit::If { cond, then, els } => CoreLit::If {
      cond: Box::new(close_at(cond, depth, atom)),
      then: Box::new(close_at(then, depth, atom)),
      els: Box::new(close_at(els, depth, atom)),
    },
    CoreLit::StructLit { fields, type_name } => CoreLit::StructLit {
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), close_at(v, depth, atom)))
        .collect(),
      type_name: *type_name,
    },
    CoreLit::StructUpdate { base, fields } => CoreLit::StructUpdate {
      base: Box::new(close_at(base, depth, atom)),
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), close_at(v, depth, atom)))
        .collect(),
    },
  }
}

/// Close `term` over `atom` at the outermost binder position — the direct
/// inverse of `open`: `close(open(t).1, open(t).0) == t`.
pub fn close(term: &CoreTerm, atom: Atom) -> CoreTerm {
  close_at(term, 0, atom)
}

/// Close `term` over `atoms` at literal indices `depth..depth+atoms.len()`
/// — the direct inverse of `core_unify::open_n` (an N-ary block of
/// simultaneous binders, e.g. a `match` case's pattern variables).
/// `atoms` must be in the same binder order `open_n` returned them in
/// (index 0 first) — each is closed at its own `depth + i`, independent
/// of the others, so the order the calls happen in doesn't matter, only
/// that each atom pairs with its own original depth.
pub(crate) fn close_n(term: &CoreTerm, depth: u32, atoms: &[Atom]) -> CoreTerm {
  let mut current = term.clone();
  for (i, atom) in atoms.iter().enumerate() {
    current = close_at(&current, depth + i as u32, *atom);
  }
  current
}

/// Replace every occurrence of `Meta(target)` with `replacement`
/// throughout `term`. No index arithmetic is needed (unlike `open`/
/// `close`): a metavariable's solution is only ever built out of atoms
/// already in scope wherever the metavariable was created, so it can
/// never contain a `Bound` index that would need reinterpreting at a
/// different nesting depth — this is precisely the invariant the
/// locally-nameless representation is chosen to provide.
pub fn subst_meta(term: &CoreTerm, target: MetaId, replacement: &CoreTerm) -> CoreTerm {
  match term {
    CoreTerm::Meta(m) if *m == target => replacement.clone(),
    CoreTerm::Bound(_)
    | CoreTerm::Free(_)
    | CoreTerm::Meta(_)
    | CoreTerm::Sort { .. }
    | CoreTerm::Hole => term.clone(),
    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(subst_meta(typ, target, replacement)),
      body: Box::new(subst_meta(body, target, replacement)),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(subst_meta(arg, target, replacement)),
      ret: Box::new(subst_meta(ret, target, replacement)),
      mult: mult.clone(),
    },
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => CoreTerm::Lam {
      dbg: dbg.clone(),
      param_typ: Box::new(subst_meta(param_typ, target, replacement)),
      body: Box::new(subst_meta(body, target, replacement)),
    },
    CoreTerm::App { fun, arg } => CoreTerm::App {
      fun: Box::new(subst_meta(fun, target, replacement)),
      arg: Box::new(subst_meta(arg, target, replacement)),
    },
    CoreTerm::Lit(lit) => CoreTerm::Lit(subst_meta_lit(lit, target, replacement)),
    CoreTerm::Con(c) => CoreTerm::Con(CoreConstructor {
      name: c.name.clone(),
      typ_name: c.typ_name.clone(),
      num_args: c.num_args,
      args: subst_meta_args(&c.args, target, replacement),
    }),
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: subst_meta_args(&n.args, target, replacement),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(subst_meta(term, target, replacement)),
    },
  }
}

fn subst_meta_args(
  args: &[Option<CoreTerm>],
  target: MetaId,
  replacement: &CoreTerm,
) -> Vec<Option<CoreTerm>> {
  args
    .iter()
    .map(|a| a.as_ref().map(|t| subst_meta(t, target, replacement)))
    .collect()
}

fn subst_meta_lit(lit: &CoreLit, target: MetaId, replacement: &CoreTerm) -> CoreLit {
  match lit {
    CoreLit::Str { .. } | CoreLit::Char { .. } | CoreLit::Num { .. } | CoreLit::Float { .. } => {
      lit.clone()
    }
    CoreLit::Match { scrutinee, cases } => CoreLit::Match {
      scrutinee: Box::new(subst_meta(scrutinee, target, replacement)),
      cases: cases
        .iter()
        .map(|c| CoreMatchCase {
          name: c.name.clone(),
          dbgs: c.dbgs.clone(),
          value: Box::new(subst_meta(&c.value, target, replacement)),
        })
        .collect(),
    },
    CoreLit::If { cond, then, els } => CoreLit::If {
      cond: Box::new(subst_meta(cond, target, replacement)),
      then: Box::new(subst_meta(then, target, replacement)),
      els: Box::new(subst_meta(els, target, replacement)),
    },
    CoreLit::StructLit { fields, type_name } => CoreLit::StructLit {
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), subst_meta(v, target, replacement)))
        .collect(),
      type_name: *type_name,
    },
    CoreLit::StructUpdate { base, fields } => CoreLit::StructUpdate {
      base: Box::new(subst_meta(base, target, replacement)),
      fields: fields
        .iter()
        .map(|(k, v)| (k.clone(), subst_meta(v, target, replacement)))
        .collect(),
    },
  }
}

// ---------------------------------------------------------------------------
// Display — a name-environment pretty-printer with shadow disambiguation
// ---------------------------------------------------------------------------

/// Tracks currently-in-scope display names (innermost last, i.e. the last
/// element is what `Bound(0)` currently means) so printing can recover
/// readable names from indices, and disambiguates a binder whose
/// `DebugName` collides with one already in scope by appending `'`
/// (mirroring how GHC/Idris-style pretty-printers handle shadowing) rather
/// than silently printing two different variables with the same name.
#[derive(Default)]
struct Printer {
  names: Vec<String>,
}

impl Printer {
  fn fresh_name(&self, dbg: &DebugName) -> String {
    match dbg {
      DebugName::Anonymous => "_".to_string(),
      DebugName::Named(id) => {
        let base = id.as_str().to_string();
        let mut candidate = base.clone();
        while self.names.iter().any(|n| n == &candidate) {
          candidate.push('\'');
        }
        candidate
      }
    }
  }

  fn print(&mut self, term: &CoreTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match term {
      CoreTerm::Bound(i) => {
        let len = self.names.len() as u32;
        if *i < len {
          write!(f, "{}", self.names[(len - 1 - *i) as usize])
        } else {
          // Dangling index: this `Bound` has no enclosing binder in view
          // (e.g. printing a binder's body in isolation, outside its
          // `Forall`/`Pi`/`Lam`) — fall back to the raw index, matching
          // `NameRef::Index`'s existing `#{i}` display convention.
          write!(f, "#{i}")
        }
      }
      CoreTerm::Free(a) => write!(f, "{a}"),
      CoreTerm::Meta(m) => write!(f, "{m}"),
      CoreTerm::Sort { level } => write!(f, "Sort {level}"),
      CoreTerm::Hole => write!(f, "_"),
      CoreTerm::Forall { dbg, typ, body } => {
        let name = self.fresh_name(dbg);
        write!(f, "{{{name} : ")?;
        self.print(typ, f)?;
        write!(f, "}} -> ")?;
        self.names.push(name);
        let r = self.print(body, f);
        self.names.pop();
        r
      }
      CoreTerm::Pi {
        dbg,
        arg,
        ret,
        mult: _,
      } => {
        let name = self.fresh_name(dbg);
        match dbg {
          DebugName::Anonymous => {
            write!(f, "(")?;
            self.print(arg, f)?;
            write!(f, ") -> ")?;
          }
          DebugName::Named(_) => {
            write!(f, "({name} : ")?;
            self.print(arg, f)?;
            write!(f, ") -> ")?;
          }
        }
        self.names.push(name);
        let r = self.print(ret, f);
        self.names.pop();
        r
      }
      CoreTerm::Lam {
        dbg,
        param_typ,
        body,
      } => {
        let name = self.fresh_name(dbg);
        write!(f, "(fn {name} : ")?;
        self.print(param_typ, f)?;
        write!(f, " => ")?;
        self.names.push(name);
        let r = self.print(body, f);
        self.names.pop();
        write!(f, ")")?;
        r
      }
      CoreTerm::App { fun, arg } => {
        write!(f, "(")?;
        self.print(fun, f)?;
        write!(f, " ")?;
        self.print(arg, f)?;
        write!(f, ")")
      }
      CoreTerm::Lit(lit) => self.print_lit(lit, f),
      CoreTerm::Con(c) => {
        write!(f, "({}", c.name)?;
        for arg in &c.args {
          write!(f, " ")?;
          match arg {
            Some(a) => self.print(a, f)?,
            None => write!(f, "_")?,
          }
        }
        write!(f, ")")
      }
      CoreTerm::Ntv(n) => {
        write!(f, "(native {}", n.native_name)?;
        for arg in &n.args {
          write!(f, " ")?;
          match arg {
            Some(a) => self.print(a, f)?,
            None => write!(f, "_")?,
          }
        }
        write!(f, ")")
      }
      // Transparent for display purposes too: a `Ctx` wrapper is metadata
      // for error attribution, not part of what a term "looks like".
      CoreTerm::Ctx { term, .. } => self.print(term, f),
    }
  }

  fn print_lit(&mut self, lit: &CoreLit, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match lit {
      CoreLit::Str { value } => write!(f, "{value:?}"),
      CoreLit::Char { value } => write!(f, "{value:?}"),
      CoreLit::Num { value, .. } => write!(f, "{value}"),
      CoreLit::Float { value, .. } => write!(f, "{}", value.0),
      CoreLit::If { cond, then, els } => {
        write!(f, "(if ")?;
        self.print(cond, f)?;
        write!(f, " then ")?;
        self.print(then, f)?;
        write!(f, " else ")?;
        self.print(els, f)?;
        write!(f, ")")
      }
      CoreLit::StructLit { fields, type_name } => {
        write!(f, "{{")?;
        for (i, (name, value)) in fields.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{name} = ")?;
          self.print(value, f)?;
        }
        if let Some(atom) = type_name {
          write!(f, " : {atom:?}")?;
        }
        write!(f, "}}")
      }
      CoreLit::StructUpdate { base, fields } => {
        write!(f, "{{")?;
        self.print(base, f)?;
        write!(f, " |")?;
        for (name, value) in fields.iter() {
          write!(f, " {name} = ")?;
          self.print(value, f)?;
        }
        write!(f, "}}")
      }
      CoreLit::Match { scrutinee, cases } => {
        write!(f, "(match ")?;
        self.print(scrutinee, f)?;
        write!(f, " {{")?;
        for case in cases {
          write!(f, " {}", case.name)?;
          let names: Vec<String> = case.dbgs.iter().map(|dbg| self.fresh_name(dbg)).collect();
          for name in &names {
            write!(f, " {name}")?;
          }
          write!(f, " => ")?;
          for name in &names {
            self.names.push(name.clone());
          }
          self.print(&case.value, f)?;
          for _ in &names {
            self.names.pop();
          }
          write!(f, ",")?;
        }
        write!(f, " }})")
      }
    }
  }
}

impl fmt::Display for CoreTerm {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    Printer::default().print(self, f)
  }
}

#[cfg(test)]
mod test {
  use super::*;

  fn named(s: &str) -> DebugName {
    DebugName::Named(Identifier::new(s.to_string()))
  }

  fn sort1() -> CoreTerm {
    CoreTerm::Sort { level: 1 }
  }

  // -------------------------------------------------------------------
  // Alpha-equivalence: the core promise of this redesign. Two terms that
  // differ only in which `DebugName` their binders carry must be equal.
  // -------------------------------------------------------------------

  #[test]
  fn test_alpha_equivalence_lam() {
    let id_x = CoreTerm::Lam {
      dbg: named("x"),
      param_typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Bound(0)),
    };
    let id_y = CoreTerm::Lam {
      dbg: named("y"),
      param_typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Bound(0)),
    };
    assert_eq!(
      id_x, id_y,
      "identity fn named x vs y must be alpha-equivalent"
    );
  }

  #[test]
  fn test_alpha_equivalence_forall() {
    // {A : Type} -> A -> A   vs   {B : Type} -> B -> B
    let mk = |name: &str| CoreTerm::Forall {
      dbg: named(name),
      typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Pi {
        dbg: DebugName::Anonymous,
        arg: Box::new(CoreTerm::Bound(0)),
        ret: Box::new(CoreTerm::Bound(1)),
        mult: Multiplicity::Many,
      }),
    };
    assert_eq!(mk("A"), mk("B"));
  }

  #[test]
  fn test_two_unrelated_foralls_same_name_are_still_distinguished_by_shape() {
    // The actual bug this redesign targets: two *different* generic
    // functions both naming their type parameter "A" must never be
    // conflated. Same name, different shape (body differs) => not equal.
    let a_to_bool = CoreTerm::Forall {
      dbg: named("A"),
      typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Pi {
        dbg: DebugName::Anonymous,
        arg: Box::new(CoreTerm::Bound(0)),
        ret: Box::new(CoreTerm::Sort { level: 0 }),
        mult: Multiplicity::Many,
      }),
    };
    let a_to_a = CoreTerm::Forall {
      dbg: named("A"),
      typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Pi {
        dbg: DebugName::Anonymous,
        arg: Box::new(CoreTerm::Bound(0)),
        ret: Box::new(CoreTerm::Bound(1)),
        mult: Multiplicity::Many,
      }),
    };
    assert_ne!(a_to_bool, a_to_a);
  }

  // -------------------------------------------------------------------
  // open/close round-trip
  // -------------------------------------------------------------------

  #[test]
  fn test_open_close_round_trip_single_binder() {
    // Forall body: A -> A. `Pi.ret` is always one binder deeper than
    // `Pi.arg` (every Pi introduces a binder slot for its return type,
    // dependent or not), so referring to the *outer* Forall's variable
    // from `ret` is `Bound(1)`, not `Bound(0)` — matches
    // test_open_close_round_trip_nested_binder's convention.
    let body = CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(CoreTerm::Bound(0)),
      ret: Box::new(CoreTerm::Bound(1)),
      mult: Multiplicity::Many,
    };
    let (atom, opened) = open(&body);
    match &opened {
      CoreTerm::Pi { arg, ret, .. } => {
        assert_eq!(**arg, CoreTerm::Free(atom));
        assert_eq!(**ret, CoreTerm::Free(atom));
      }
      _ => panic!("expected Pi"),
    }
    let closed = close(&opened, atom);
    assert_eq!(closed, body, "close(open(t)) must round-trip to t");
  }

  #[test]
  fn test_open_close_round_trip_nested_binder() {
    // Forall body containing a nested Pi whose ret references the OUTER
    // Forall's own bound var (Bound(1) once under the Pi's one extra
    // binder level) — checks depth bookkeeping through nesting.
    let body = CoreTerm::Pi {
      dbg: named("x"),
      arg: Box::new(CoreTerm::Bound(0)), // refs the Forall's var (A)
      ret: Box::new(CoreTerm::Bound(1)), // refs the Forall's var (A), one level deeper
      mult: Multiplicity::Many,
    };
    let (atom, opened) = open(&body);
    match &opened {
      CoreTerm::Pi { arg, ret, .. } => {
        assert_eq!(**arg, CoreTerm::Free(atom));
        // ret's Bound(1) referred to the Forall's var, which open() at
        // depth 0 threads through as depth+1 = 1 when descending into
        // Pi's ret — so it should also have become Free(atom).
        assert_eq!(**ret, CoreTerm::Free(atom));
      }
      _ => panic!("expected Pi"),
    }
    assert_eq!(close(&opened, atom), body);
  }

  #[test]
  fn test_open_does_not_touch_outer_indices() {
    // Simulate `body` living one level inside an ALREADY-enclosing binder:
    // Bound(1) here refers to that outer binder, not the one being opened,
    // and must be left completely untouched by opening depth 0.
    let body = CoreTerm::App {
      fun: Box::new(CoreTerm::Bound(0)), // the binder being opened
      arg: Box::new(CoreTerm::Bound(1)), // some outer binder — must survive
    };
    let (atom, opened) = open(&body);
    match &opened {
      CoreTerm::App { fun, arg } => {
        assert_eq!(**fun, CoreTerm::Free(atom));
        assert_eq!(**arg, CoreTerm::Bound(1), "outer index must be untouched");
      }
      _ => panic!("expected App"),
    }
  }

  // -------------------------------------------------------------------
  // Atom / MetaId uniqueness
  // -------------------------------------------------------------------

  #[test]
  fn test_fresh_atoms_are_distinct() {
    let a = Atom::fresh();
    let b = Atom::fresh();
    assert_ne!(a, b);
  }

  #[test]
  fn test_fresh_metas_are_distinct() {
    let a = MetaId::fresh();
    let b = MetaId::fresh();
    assert_ne!(a, b);
  }

  // -------------------------------------------------------------------
  // subst_meta
  // -------------------------------------------------------------------

  #[test]
  fn test_subst_meta_replaces_target_only() {
    let m1 = MetaId::fresh();
    let m2 = MetaId::fresh();
    let term = CoreTerm::App {
      fun: Box::new(CoreTerm::Meta(m1)),
      arg: Box::new(CoreTerm::Meta(m2)),
    };
    let replacement = CoreTerm::Sort { level: 0 };
    let result = subst_meta(&term, m1, &replacement);
    match result {
      CoreTerm::App { fun, arg } => {
        assert_eq!(*fun, replacement);
        assert_eq!(*arg, CoreTerm::Meta(m2));
      }
      _ => panic!("expected App"),
    }
  }

  #[test]
  fn test_subst_meta_under_binder() {
    let m = MetaId::fresh();
    let term = CoreTerm::Lam {
      dbg: named("x"),
      param_typ: Box::new(CoreTerm::Meta(m)),
      body: Box::new(CoreTerm::Bound(0)),
    };
    let replacement = CoreTerm::Sort { level: 1 };
    let result = subst_meta(&term, m, &replacement);
    match result {
      CoreTerm::Lam {
        param_typ, body, ..
      } => {
        assert_eq!(*param_typ, replacement);
        assert_eq!(*body, CoreTerm::Bound(0));
      }
      _ => panic!("expected Lam"),
    }
  }

  // -------------------------------------------------------------------
  // Display: readable output + shadow disambiguation
  // -------------------------------------------------------------------

  #[test]
  fn test_display_forall_pi() {
    // {A : Type} -> A -> A (Pi.ret is one binder deeper than Pi.arg, so the
    // outer Forall's variable is Bound(1) from ret's position — see
    // test_open_close_round_trip_single_binder).
    let t = CoreTerm::Forall {
      dbg: named("A"),
      typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Pi {
        dbg: DebugName::Anonymous,
        arg: Box::new(CoreTerm::Bound(0)),
        ret: Box::new(CoreTerm::Bound(1)),
        mult: Multiplicity::Many,
      }),
    };
    assert_eq!(format!("{t}"), "{A : Sort 1} -> (A) -> A");
  }

  #[test]
  fn test_display_disambiguates_shadowed_names() {
    // (fn x : Sort1 => (fn x : Sort1 => Bound(0))) — inner `x` shadows
    // outer `x`; printer must not show two different variables as `x`.
    let t = CoreTerm::Lam {
      dbg: named("x"),
      param_typ: Box::new(sort1()),
      body: Box::new(CoreTerm::Lam {
        dbg: named("x"),
        param_typ: Box::new(sort1()),
        body: Box::new(CoreTerm::Bound(0)),
      }),
    };
    let printed = format!("{t}");
    assert!(
      printed.contains("x'"),
      "expected disambiguated shadow, got: {printed}"
    );
  }

  // -------------------------------------------------------------------
  // Lit/Con/Match — the extended scope
  // -------------------------------------------------------------------

  fn con(name: &str, args: Vec<Option<CoreTerm>>) -> CoreTerm {
    CoreTerm::Con(CoreConstructor {
      name: Identifier::new(name.to_string()),
      typ_name: ModulePath::top("List"),
      num_args: args.len(),
      args,
    })
  }

  #[test]
  fn test_alpha_equivalence_con_args() {
    // cons x x  vs  cons y y — same shape, differently-named bound
    // occurrences (both refer to their own Lam's single param).
    let mk = |name: &str| CoreTerm::Lam {
      dbg: named(name),
      param_typ: Box::new(sort1()),
      body: Box::new(con(
        "cons",
        vec![Some(CoreTerm::Bound(0)), Some(CoreTerm::Bound(0))],
      )),
    };
    assert_eq!(mk("x"), mk("y"));
  }

  #[test]
  fn test_alpha_equivalence_match_case_args() {
    // match s { cons a t => a }  vs  match s { cons x y => x } — same
    // shape, differently-named pattern binders.
    let mk = |a: &str, t: &str| {
      CoreTerm::Lit(CoreLit::Match {
        scrutinee: Box::new(CoreTerm::Bound(0)),
        cases: vec![CoreMatchCase {
          name: Identifier::new("cons".to_string()),
          dbgs: vec![named(a), named(t)],
          value: Box::new(CoreTerm::Bound(1)), // refs the first pattern arg
        }],
      })
    };
    assert_eq!(mk("a", "t"), mk("x", "y"));
  }

  #[test]
  fn test_open_close_round_trip_through_match_case() {
    // Forall body: match Bound(0) { cons a t => Bound(2) } — the case
    // body references the OUTER Forall's var, two binders further out
    // (one for the Forall itself skipped by opening at depth 0, plus the
    // 2-ary case block) once inside a 2-arg case.
    let body = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(CoreTerm::Bound(0)),
      cases: vec![CoreMatchCase {
        name: Identifier::new("cons".to_string()),
        dbgs: vec![DebugName::Anonymous, DebugName::Anonymous],
        value: Box::new(CoreTerm::Bound(2)),
      }],
    });
    let (atom, opened) = open(&body);
    match &opened {
      CoreTerm::Lit(CoreLit::Match { scrutinee, cases }) => {
        assert_eq!(**scrutinee, CoreTerm::Free(atom));
        assert_eq!(*cases[0].value, CoreTerm::Free(atom));
      }
      other => panic!("expected Lit::Match, got {other:?}"),
    }
    assert_eq!(close(&opened, atom), body);
  }

  #[test]
  fn test_subst_meta_reaches_into_con_and_match() {
    let m = MetaId::fresh();
    let term = con("cons", vec![Some(CoreTerm::Meta(m)), None]);
    let replacement = sort1();
    match subst_meta(&term, m, &replacement) {
      CoreTerm::Con(c) => {
        assert_eq!(c.args[0], Some(replacement));
        assert_eq!(c.args[1], None);
      }
      other => panic!("expected Con, got {other:?}"),
    }

    let match_term = CoreTerm::Lit(CoreLit::Match {
      scrutinee: Box::new(CoreTerm::Meta(m)),
      cases: vec![CoreMatchCase {
        name: Identifier::new("x".to_string()),
        dbgs: vec![],
        value: Box::new(CoreTerm::Meta(m)),
      }],
    });
    match subst_meta(&match_term, m, &sort0()) {
      CoreTerm::Lit(CoreLit::Match { scrutinee, cases }) => {
        assert_eq!(*scrutinee, sort0());
        assert_eq!(*cases[0].value, sort0());
      }
      other => panic!("expected Lit::Match, got {other:?}"),
    }
  }

  fn sort0() -> CoreTerm {
    CoreTerm::Sort { level: 0 }
  }
}
