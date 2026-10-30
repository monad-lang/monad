//! `CoreIr` — the compiled, evaluator-facing representation produced by
//! lowering `CoreTerm` (Phase 1 of
//! `plans/implementations/core-term-closure-evaluator.md`).
//!
//! Keeps the two ideas from `eval_term::EvalTerm` that are genuinely
//! sound: flat-index globals (`Global(u32)`, no scope-chain/name lookup
//! at runtime) and compiling `match`/`if` to constructor-tag dispatch
//! (`Match`, one mechanism for both — see below). Deliberately does
//! *not* carry forward `EvalTerm`'s substitution-based beta-reduction
//! machinery: there is no `subst`/`shift` anywhere in this file, on
//! purpose. `CoreIr` is pure, immutable syntax — the evaluator (a
//! separate crate module, not yet written) reduces it via environment-
//! extending closures instead of rewriting the tree; see the plan's
//! Phase 3/4 sections for why.
//!
//! Deliberately excluded relative to `EvalTerm`: `Sort`/`Region`/
//! `Borrow`/`Proj`/`ProjField` (confirmed dead or pass-through no-ops in
//! `eval_term::eval`; `CoreTerm` itself has no region/borrow concept at
//! all) and `Multiplicity` on `Lam` (a purely static, checker-time
//! property — `eval.rs`'s tree-walker doesn't consult it at runtime
//! either, so dropping it here isn't a new gap). `if` is not a separate
//! variant: it lowers through the same `Match` node `match` does,
//! against `Bool`'s two known constructor tags — one dispatch mechanism,
//! not two.

use std::fmt::Display;
use std::sync::Arc;

use crate::shared_str::SharedStr;

/// Shared handle to a compiled subterm. `Arc` (not `Box`) so a `Global`
/// slot's body and any closure capturing it can be referenced in O(1)
/// without deep-cloning — see `plans/implementations/core-term-closure-
/// evaluator.md`'s Phase 3 (`Env`/`Value`) for how this gets used.
pub type IrRef = Arc<CoreIr>;

/// A scalar literal — mirrors `core_term::CoreLit`'s scalar variants
/// (`Str`/`Char`/`Num`/`Float`), minus everything structural (`Match`/
/// `If`/`StructLit`/`StructUpdate`, all compiled away to `Match`/`Con`
/// by the lowering pass, never reaching this IR as literals).
#[derive(Debug, Clone, PartialEq)]
pub enum IrLit {
  /// Backed by `SharedStr` (`Arc<str>` + byte-range), not a plain
  /// `String` — see `shared_str.rs`'s own doc comment for why: this is
  /// what makes `String.slice`/`String.drop` (`core_native.rs`) O(1)
  /// instead of a full-file-copy per call.
  Str(SharedStr),
  Char(char),
  /// `crate::term::NumSuffix` is reused as-is rather than re-declared
  /// here — it's a plain, already-minimal tag type with no dependency on
  /// `Term`/`CoreTerm`'s own recursive structure.
  Num(i64, crate::term::NumSuffix),
  Float(crate::term::F64Wrap, crate::term::NumSuffix),
  /// A type universe (`Type`, `Prop`, `Pred`, `Sort n`) used as an
  /// ordinary runtime VALUE, e.g. `get_sort Type` — see `lower_core_ir`'s
  /// `CoreTerm::Sort` lowering arm for why this is enough (opaque,
  /// structurally-inert) rather than real universe machinery.
  Sort(u64),
}

impl Display for IrLit {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      IrLit::Str(s) => write!(f, "{s:?}"),
      IrLit::Char(c) => write!(f, "{c:?}"),
      IrLit::Num(v, _) => write!(f, "{v}"),
      IrLit::Float(v, _) => write!(f, "{}", v.0),
      IrLit::Sort(level) => write!(f, "Sort {level}"),
    }
  }
}

/// One arm of a `Match` node. `bind_count` is how many fields the
/// matched constructor carries (and thus how many entries the evaluator
/// must push onto its `Env` before evaluating `body`) — the arm's own
/// `body` is `bind_count` `Lam`-equivalent binders deep, mirroring how
/// `lower_match_case` in `lower.rs` already wraps each case body in one
/// `Lam` per pattern variable rather than opening them inline; here that
/// same shape is expressed directly as nested `Local` references inside
/// `body` at increasing depth, without a separate `Lam` wrapper node.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
  pub bind_count: u32,
  pub body: IrRef,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CoreIr {
  /// De Bruijn index into the *runtime* environment (an `Env`, built by
  /// the evaluator as it descends into `Lam`/`Match` bodies) — same
  /// numbering convention as `CoreTerm::Bound`, carried through lowering
  /// unchanged (no index recomputation needed, unlike `lower.rs`'s
  /// `Term -> EvalTerm` pass, which has to compute de Bruijn indices from
  /// named variables from scratch).
  Local(u32),

  /// Reference to a whole-program global slot — resolved at lowering
  /// time from a `CoreTerm::Free(Atom)` occurrence, via that def's own
  /// `atom_paths` (see `core_program::CheckedCoreDef`) down to a durable
  /// `ModulePath`, then interned into this flat index. Covers both
  /// ordinary def references and constructor/native references used
  /// point-free (see the plan's Phase 2/5 sections — those resolve to a
  /// distinct, synthesized `Value` kind at evaluation time, not a
  /// `CoreIr` body, since a constructor/native has no def body to walk).
  Global(u32),

  /// `param_typ` is dropped — never needed at runtime, only by the
  /// checker (which has already run by the time `CoreTerm` reaches this
  /// lowering pass).
  Lam {
    body: IrRef,
  },

  App {
    fun: IrRef,
    arg: IrRef,
  },

  Lit(IrLit),

  /// Compiled `match`, `if`, dictionary-field-projection, and (Phase 2)
  /// `StructLit`/`StructUpdate` field access — one constructor-tag-
  /// dispatch mechanism for everything CoreTerm expresses as "look at a
  /// value's shape and branch." `arms` is indexed by tag (declaration
  /// order among the scrutinee's inductive's constructors — see
  /// `core_program::CoreInductiveInfo`), not scanned by name. A
  /// single-arm match (any dictionary-field projection, or a struct
  /// field access) is still represented as `Match` with one `MatchArm`
  /// — lowering-time code may choose to skip an actual tag comparison
  /// for that case (there's nothing to compare against), but the IR
  /// shape doesn't need a separate variant for it.
  Match {
    scrutinee: IrRef,
    arms: Vec<MatchArm>,
  },

  /// Synthesized by `lower_core_ir::lower_match` in place of a real arm,
  /// for a constructor tag the SOURCE `match` genuinely never covered
  /// (no named case, no wildcard) — `arms` in `Match` must be a
  /// complete, fixed-size array indexed by tag (unlike the tree-walker,
  /// which dispatches by the scrutinee's actual runtime tag and simply
  /// never reaches an uncovered case in a well-behaved program), so
  /// SOME arm has to occupy that slot. Reaching this arm at runtime
  /// means the program actually produced a value of the one constructor
  /// the programmer asserted (via the missing wildcard) could never
  /// occur — a real, if rare, runtime error (`CoreEvalError::
  /// NonExhaustiveMatch`), not a lowering-time one; the alternative
  /// (refusing to lower the whole def) is strictly worse, since it
  /// breaks even the common case where that constructor is provably
  /// never actually constructed.
  MatchFail {
    inductive: crate::term::ModulePath,
    ctor: crate::term::Identifier,
  },

  /// A (possibly partially applied) constructor. `tag` is this
  /// constructor's position among its inductive's constructors
  /// (declaration order, resolved once at lowering time via
  /// `CoreInductiveInfo` — never a name-keyed lookup at runtime); `arity`
  /// is its total field count. `args.len() <= arity`; the evaluator
  /// fills remaining slots left-to-right as further `App`s apply to the
  /// resulting value (`CoreTerm`'s own `App`/`Bound` are ordinary
  /// left-to-right lambda-calculus application, so no out-of-order slot
  /// addressing — unlike the older `Term`-based `induct_constructor`'s
  /// `NameRef::Index` scheme — is needed here).
  Con {
    tag: u32,
    arity: u32,
    args: Vec<IrRef>,
  },

  /// A (possibly partially applied) native/builtin call. `native_id` is
  /// resolved once at lowering time to a stable index into a shared
  /// name -> id table (mirrors `eval_term::Env::primitives`), not
  /// re-resolved by name at runtime.
  Ntv {
    native_id: u32,
    args: Vec<IrRef>,
  },
}

impl Display for CoreIr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      CoreIr::Local(i) => write!(f, "(local {i})"),
      CoreIr::Global(i) => write!(f, "(global {i})"),
      CoreIr::Lam { body } => write!(f, "(lam {body})"),
      CoreIr::App { fun, arg } => write!(f, "(app {fun} {arg})"),
      CoreIr::Lit(l) => write!(f, "(lit {l})"),
      CoreIr::Match { scrutinee, arms } => {
        write!(f, "(match {scrutinee}")?;
        for arm in arms {
          write!(f, " [{}] {}", arm.bind_count, arm.body)?;
        }
        write!(f, ")")
      }
      CoreIr::MatchFail { inductive, ctor } => {
        write!(f, "(match-fail {inductive}.{ctor})")
      }
      CoreIr::Con { tag, arity, args } => {
        write!(f, "(con #{tag}/{arity}")?;
        for a in args {
          write!(f, " {a}")?;
        }
        write!(f, ")")
      }
      CoreIr::Ntv { native_id, args } => {
        write!(f, "(ntv #{native_id}")?;
        for a in args {
          write!(f, " {a}")?;
        }
        write!(f, ")")
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Helper constructors — mirror eval_term.rs's free-function style
// ---------------------------------------------------------------------------

pub fn local(idx: u32) -> CoreIr {
  CoreIr::Local(idx)
}

pub fn global(idx: u32) -> CoreIr {
  CoreIr::Global(idx)
}

pub fn lam(body: CoreIr) -> CoreIr {
  CoreIr::Lam {
    body: Arc::new(body),
  }
}

pub fn app(fun: CoreIr, arg: CoreIr) -> CoreIr {
  CoreIr::App {
    fun: Arc::new(fun),
    arg: Arc::new(arg),
  }
}

pub fn lit(l: IrLit) -> CoreIr {
  CoreIr::Lit(l)
}

pub fn match_(scrutinee: CoreIr, arms: Vec<MatchArm>) -> CoreIr {
  CoreIr::Match {
    scrutinee: Arc::new(scrutinee),
    arms,
  }
}

pub fn arm(bind_count: u32, body: CoreIr) -> MatchArm {
  MatchArm {
    bind_count,
    body: Arc::new(body),
  }
}

pub fn con(tag: u32, arity: u32, args: Vec<CoreIr>) -> CoreIr {
  CoreIr::Con {
    tag,
    arity,
    args: args.into_iter().map(Arc::new).collect(),
  }
}

pub fn ntv(native_id: u32, args: Vec<CoreIr>) -> CoreIr {
  CoreIr::Ntv {
    native_id,
    args: args.into_iter().map(Arc::new).collect(),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::term::NumSuffix;

  #[test]
  fn test_local_construction() {
    let v = local(0);
    assert_eq!(v, CoreIr::Local(0));
    assert_eq!(v.to_string(), "(local 0)");
  }

  #[test]
  fn test_lam_app_construction() {
    let id_fn = lam(local(0));
    let applied = app(id_fn, lit(IrLit::Num(42, NumSuffix::I64)));
    assert_eq!(applied.to_string(), "(app (lam (local 0)) (lit 42))");
  }

  #[test]
  fn test_match_construction() {
    // match scrutinee { Cons head tail => head, Nil => 0 }
    let m = match_(
      global(0),
      vec![arm(2, local(1)), arm(0, lit(IrLit::Num(0, NumSuffix::I64)))],
    );
    assert_eq!(
      m.to_string(),
      "(match (global 0) [2] (local 1) [0] (lit 0))"
    );
  }

  #[test]
  fn test_con_partial_application() {
    // A partially-applied 2-arity constructor (e.g. `cons` with only its
    // first field supplied) — `args.len() < arity` is a valid, expected
    // shape, not an error.
    let partial = con(0, 2, vec![lit(IrLit::Num(1, NumSuffix::I64))]);
    assert_eq!(partial.to_string(), "(con #0/2 (lit 1))");
  }

  #[test]
  fn test_ntv_construction() {
    let call = ntv(
      3,
      vec![
        lit(IrLit::Num(1, NumSuffix::I64)),
        lit(IrLit::Num(2, NumSuffix::I64)),
      ],
    );
    assert_eq!(call.to_string(), "(ntv #3 (lit 1) (lit 2))");
  }

  #[test]
  fn test_arc_sharing_is_cheap_clone() {
    // The whole point of IrRef = Arc<CoreIr>: cloning a large subterm
    // (as happens whenever the same global is referenced from multiple
    // call sites) is a refcount bump, not a deep copy.
    let big = lam(app(local(0), local(0)));
    let shared: IrRef = Arc::new(big.clone());
    let a = shared.clone();
    let b = shared.clone();
    assert_eq!(Arc::strong_count(&shared), 3);
    assert_eq!(*a, *b);
  }
}
