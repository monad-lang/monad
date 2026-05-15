/// Lowered term representation for evaluation, optimization, and codegen.
///
/// EvalTerm is produced by lowering a type-checked TypeTerm (crate::term::Term)
/// in the lowering pass (lower.rs). It uses de Bruijn indices for variables,
/// recursors for pattern matching, resolved operators as const/prim indices,
/// and carries multiplicity and region annotations on every subterm that
/// produces a runtime value.
///
/// See: plans/implementations/two-term-kernel.md
use std::fmt::Display;
use std::hash::Hash;

// ---------------------------------------------------------------------------
// FloatValue — f64 comparison by bits for Eq/Hash/Ord derivability
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct FloatValue(pub f64);

impl FloatValue {
  pub fn to_bits(&self) -> u64 {
    self.0.to_bits()
  }
}

impl PartialEq for FloatValue {
  fn eq(&self, other: &Self) -> bool {
    self.0.to_bits() == other.0.to_bits()
  }
}

impl Eq for FloatValue {}

impl Hash for FloatValue {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.to_bits().hash(state);
  }
}

impl PartialOrd for FloatValue {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for FloatValue {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.0.to_bits().cmp(&other.0.to_bits())
  }
}

impl Display for FloatValue {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.0)
  }
}

// ---------------------------------------------------------------------------
// Multiplicity — usage annotation on every value-producing node
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Multiplicity {
  /// Erased at compile time — no runtime representation
  Zero,
  /// Unrestricted — default multiplicity
  Many,
  /// Must be used exactly once (syntax: !x)
  Linear,
  /// Can be used 0 or 1 time (syntax: ?x)
  Affine,
}

impl Default for Multiplicity {
  fn default() -> Self {
    Multiplicity::Many
  }
}

impl Display for Multiplicity {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Multiplicity::Zero => write!(f, "0"),
      Multiplicity::Many => write!(f, "ω"),
      Multiplicity::Linear => write!(f, "!"),
      Multiplicity::Affine => write!(f, "?"),
    }
  }
}

// ---------------------------------------------------------------------------
// Region — spatial lifetime annotation for memory management
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Region {
  /// Stack-allocated, scoped to the current function frame
  Stack,
  /// Heap-allocated, GC-managed
  Heap,
  /// Borrow reference with nesting depth
  Borrow { depth: u64 },
  /// Region parameter determined by the caller (function-level lifetime)
  Param { idx: u64 },
}

impl Display for Region {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Region::Stack => write!(f, "r_stack"),
      Region::Heap => write!(f, "r_heap"),
      Region::Borrow { depth } => write!(f, "r_borrow({depth})"),
      Region::Param { idx } => write!(f, "r_param({idx})"),
    }
  }
}

// ---------------------------------------------------------------------------
// BorrowKind — shared or exclusive borrow
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BorrowKind {
  /// &T — immutable shared reference
  Shared,
  /// &mut T — exclusive mutable reference
  Unique,
}

impl Display for BorrowKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      BorrowKind::Shared => write!(f, "shared"),
      BorrowKind::Unique => write!(f, "unique"),
    }
  }
}

// ---------------------------------------------------------------------------
// Literal — scalar runtime values (no match/if/struct — those are lowered)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Literal {
  /// Natural number (unsigned 64-bit)
  Nat { v: u64 },
  /// Signed integer (64-bit)
  Int { v: i64 },
  /// String
  Str { value: String },
  /// IEEE 754 double-precision float
  Float { value: FloatValue },
  /// Unicode character
  Char { c: u64 },
}

impl Display for Literal {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Literal::Nat { v } => write!(f, "{v}n"),
      Literal::Int { v } => write!(f, "{v}"),
      Literal::Str { value } => write!(f, "{value:?}"),
      Literal::Float { value } => write!(f, "{value}"),
      Literal::Char { c } => write!(f, "'{}'", char::from_u32(*c as u32).unwrap_or('�')),
    }
  }
}

// ---------------------------------------------------------------------------
// RecursorInfo — static dispatch info for recursor evaluation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RecursorInfo {
  /// Index into the environment's recursor table
  pub rec_idx: u64,
  /// Number of type parameters
  pub params_len: u64,
  /// Number of motives (1 for simple, N for indexed families)
  pub motives_len: u64,
  /// Number of case functions (one per constructor)
  pub cases_len: u64,
}

impl RecursorInfo {
  pub fn new(rec_idx: u64, params_len: u64, motives_len: u64, cases_len: u64) -> Self {
    RecursorInfo {
      rec_idx,
      params_len,
      motives_len,
      cases_len,
    }
  }
}

impl Display for RecursorInfo {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "rec(#{} params={} motives={} cases={})",
      self.rec_idx, self.params_len, self.motives_len, self.cases_len
    )
  }
}

// ---------------------------------------------------------------------------
// EvalTerm — the lowered execution term
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EvalTerm {
  /// De Bruijn variable with multiplicity
  Var { idx: u64, mult: Multiplicity },

  /// Lambda: parameter multiplicity + body
  Lam {
    param_mult: Multiplicity,
    body: Box<EvalTerm>,
  },

  /// Application: fn(arg) with result multiplicity
  App {
    fun: Box<EvalTerm>,
    arg: Box<EvalTerm>,
    mult: Multiplicity,
  },

  /// Let binding: name erased, value + continuation
  LetExpr {
    val: Box<EvalTerm>,
    mult: Multiplicity,
    body: Box<EvalTerm>,
  },

  /// Resolved constant (index into environment's constant table)
  Const { idx: u64 },

  /// Sort universe level (Prop=0, Type=1, Type 1=2, ...)
  Sort { level: u64 },

  /// Scalar literal value
  Lit { l: Literal },

  /// Native/primitive call (index into environment's primitive table)
  Prim { idx: u64, args: Vec<EvalTerm> },

  /// Recursor application: recursor(motive...)(cases...)(scrutinee)
  Recursor {
    info: RecursorInfo,
    motive: Box<EvalTerm>,
    cases: Vec<EvalTerm>,
    scrutinee: Box<EvalTerm>,
    mult: Multiplicity,
  },

  /// Region-scoped value — all inner allocations live in the given region
  Region {
    reg: Region,
    body: Box<EvalTerm>,
    mult: Multiplicity,
  },

  /// Borrow: creates a reference from a region-allocated value
  Borrow {
    kind: BorrowKind,
    reg: Region,
    body: Box<EvalTerm>,
    mult: Multiplicity,
  },

  /// Struct projection: access field N of a struct at constant index
  Proj {
    field_idx: u64,
    struct_idx: u64,
    arg: Box<EvalTerm>,
  },

  /// Reference to a previous projection result (for LLVM getelementptr chaining)
  ProjField { base: Box<EvalTerm>, field_idx: u64 },
}

// ---------------------------------------------------------------------------
// Display for EvalTerm — parenthesized prefix form for debugging
// ---------------------------------------------------------------------------

impl Display for EvalTerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EvalTerm::Var { idx, mult } => write!(f, "(var {idx} {mult})"),
      EvalTerm::Lam { param_mult, body } => write!(f, "(lam {param_mult} {body})"),
      EvalTerm::App { fun, arg, mult } => write!(f, "(app {mult} {fun} {arg})"),
      EvalTerm::LetExpr { val, mult, body } => write!(f, "(let {mult} {val} {body})"),
      EvalTerm::Const { idx } => write!(f, "(const #{idx})"),
      EvalTerm::Sort { level } => write!(f, "(sort {level})"),
      EvalTerm::Lit { l } => write!(f, "(lit {l})"),
      EvalTerm::Prim { idx, args } => {
        write!(f, "(prim #{idx}")?;
        for a in args {
          write!(f, " {a}")?;
        }
        write!(f, ")")
      }
      EvalTerm::Recursor {
        info,
        motive,
        cases,
        scrutinee,
        mult,
      } => {
        write!(f, "(recursor {mult} {info} {motive}")?;
        for c in cases {
          write!(f, " {c}")?;
        }
        write!(f, " {scrutinee})")
      }
      EvalTerm::Region { reg, body, mult } => write!(f, "(region {mult} {reg} {body})"),
      EvalTerm::Borrow {
        kind,
        reg,
        body,
        mult,
      } => write!(f, "(borrow {mult} {kind} {reg} {body})"),
      EvalTerm::Proj {
        field_idx,
        struct_idx,
        arg,
      } => write!(f, "(proj .{field_idx} struct=#{struct_idx} {arg})"),
      EvalTerm::ProjField { base, field_idx } => {
        write!(f, "(proj_field .{field_idx} {base})")
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Env — the evaluation environment for EvalTerm
// ---------------------------------------------------------------------------

/// Maps compile-time indices (Const, Prim, Recursor) to their runtime values.
///
/// The environment is built during lowering and passed to the evaluator.
/// - `constants`: maps `Const { idx }` → the lowered term for that definition
/// - `primitives`: maps `Prim { idx }` → (name, arity) for native function dispatch
/// - `recursors`: maps `Recursor { info.rec_idx }` → (name, info) for recursor dispatch
#[derive(Debug, Clone, Default)]
pub struct Env {
  pub constants: Vec<EvalTerm>,
  pub primitives: Vec<(String, usize)>,
  pub recursors: Vec<(String, RecursorInfo)>,
}

impl Env {
  pub fn new() -> Self {
    Env::default()
  }
}

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

pub fn var(idx: u64, mult: Multiplicity) -> EvalTerm {
  EvalTerm::Var { idx, mult }
}

pub fn lam(param_mult: Multiplicity, body: EvalTerm) -> EvalTerm {
  EvalTerm::Lam {
    param_mult,
    body: Box::new(body),
  }
}

pub fn app(fun: EvalTerm, arg: EvalTerm, mult: Multiplicity) -> EvalTerm {
  EvalTerm::App {
    fun: Box::new(fun),
    arg: Box::new(arg),
    mult,
  }
}

pub fn let_expr(val: EvalTerm, mult: Multiplicity, body: EvalTerm) -> EvalTerm {
  EvalTerm::LetExpr {
    val: Box::new(val),
    mult,
    body: Box::new(body),
  }
}

pub fn const_(idx: u64) -> EvalTerm {
  EvalTerm::Const { idx }
}

pub fn sort(level: u64) -> EvalTerm {
  EvalTerm::Sort { level }
}

pub fn lit(l: Literal) -> EvalTerm {
  EvalTerm::Lit { l }
}

pub fn prim(idx: u64, args: Vec<EvalTerm>) -> EvalTerm {
  EvalTerm::Prim { idx, args }
}

pub fn recursor(
  info: RecursorInfo,
  motive: EvalTerm,
  cases: Vec<EvalTerm>,
  scrutinee: EvalTerm,
  mult: Multiplicity,
) -> EvalTerm {
  EvalTerm::Recursor {
    info,
    motive: Box::new(motive),
    cases,
    scrutinee: Box::new(scrutinee),
    mult,
  }
}

pub fn region(reg: Region, body: EvalTerm, mult: Multiplicity) -> EvalTerm {
  EvalTerm::Region {
    reg,
    body: Box::new(body),
    mult,
  }
}

pub fn borrow(kind: BorrowKind, reg: Region, body: EvalTerm, mult: Multiplicity) -> EvalTerm {
  EvalTerm::Borrow {
    kind,
    reg,
    body: Box::new(body),
    mult,
  }
}

pub fn proj(field_idx: u64, struct_idx: u64, arg: EvalTerm) -> EvalTerm {
  EvalTerm::Proj {
    field_idx,
    struct_idx,
    arg: Box::new(arg),
  }
}

pub fn proj_field(base: EvalTerm, field_idx: u64) -> EvalTerm {
  EvalTerm::ProjField {
    base: Box::new(base),
    field_idx,
  }
}

// ---------------------------------------------------------------------------
// De Bruijn substitution — replace index `index` with `replacement`
// ---------------------------------------------------------------------------

/// Substitute `replacement` for de Bruijn index `index` in `term`.
///
/// All free indices > `index` are decremented by 1 because one binder
/// is removed from the context. The `replacement` is shifted up when
/// entering a binder (Lam, LetExpr body) to avoid capture.
pub fn subst(term: &EvalTerm, index: u64, replacement: &EvalTerm) -> EvalTerm {
  use std::cmp::Ordering;

  match term {
    EvalTerm::Var { idx, mult } => match idx.cmp(&index) {
      Ordering::Less => term.clone(),
      Ordering::Equal => replacement.clone(),
      Ordering::Greater => EvalTerm::Var {
        idx: idx - 1,
        mult: *mult,
      },
    },

    EvalTerm::Lam { param_mult, body } => {
      let shifted = shift(replacement, 0, 1);
      EvalTerm::Lam {
        param_mult: *param_mult,
        body: Box::new(subst(body, index + 1, &shifted)),
      }
    }

    EvalTerm::App { fun, arg, mult } => EvalTerm::App {
      fun: Box::new(subst(fun, index, replacement)),
      arg: Box::new(subst(arg, index, replacement)),
      mult: *mult,
    },

    EvalTerm::LetExpr { val, mult, body } => {
      let shifted = shift(replacement, 0, 1);
      EvalTerm::LetExpr {
        val: Box::new(subst(val, index, replacement)),
        mult: *mult,
        body: Box::new(subst(body, index + 1, &shifted)),
      }
    }

    EvalTerm::Const { .. } => term.clone(),
    EvalTerm::Sort { .. } => term.clone(),
    EvalTerm::Lit { .. } => term.clone(),

    EvalTerm::Prim {
      idx: prim_idx,
      args,
    } => EvalTerm::Prim {
      idx: *prim_idx,
      args: args.iter().map(|a| subst(a, index, replacement)).collect(),
    },

    EvalTerm::Recursor {
      info,
      motive,
      cases,
      scrutinee,
      mult,
    } => EvalTerm::Recursor {
      info: info.clone(),
      motive: Box::new(subst(motive, index, replacement)),
      cases: cases.iter().map(|c| subst(c, index, replacement)).collect(),
      scrutinee: Box::new(subst(scrutinee, index, replacement)),
      mult: *mult,
    },

    EvalTerm::Region { reg, body, mult } => EvalTerm::Region {
      reg: reg.clone(),
      body: Box::new(subst(body, index, replacement)),
      mult: *mult,
    },

    EvalTerm::Borrow {
      kind,
      reg,
      body,
      mult,
    } => EvalTerm::Borrow {
      kind: kind.clone(),
      reg: reg.clone(),
      body: Box::new(subst(body, index, replacement)),
      mult: *mult,
    },

    EvalTerm::Proj {
      field_idx,
      struct_idx,
      arg,
    } => EvalTerm::Proj {
      field_idx: *field_idx,
      struct_idx: *struct_idx,
      arg: Box::new(subst(arg, index, replacement)),
    },

    EvalTerm::ProjField { base, field_idx } => EvalTerm::ProjField {
      base: Box::new(subst(base, index, replacement)),
      field_idx: *field_idx,
    },
  }
}

// ---------------------------------------------------------------------------
// De Bruijn shift — adjust indices crossing a binding threshold
// ---------------------------------------------------------------------------

/// Shift all de Bruijn indices >= `cutoff` by `amount`.
///
/// Used when lifting a term across a new binder: entering a lambda increases
/// the cutoff by 1. A positive amount avoids variable capture; a negative
/// amount (combined with substitution) removes a binder.
pub fn shift(term: &EvalTerm, cutoff: u64, amount: i64) -> EvalTerm {
  let idx_shift = |idx: &u64| -> u64 {
    if *idx >= cutoff {
      idx.wrapping_add_signed(amount)
    } else {
      *idx
    }
  };

  match term {
    EvalTerm::Var { idx, mult } => EvalTerm::Var {
      idx: idx_shift(idx),
      mult: *mult,
    },

    EvalTerm::Lam { param_mult, body } => EvalTerm::Lam {
      param_mult: *param_mult,
      body: Box::new(shift(body, cutoff + 1, amount)),
    },

    EvalTerm::App { fun, arg, mult } => EvalTerm::App {
      fun: Box::new(shift(fun, cutoff, amount)),
      arg: Box::new(shift(arg, cutoff, amount)),
      mult: *mult,
    },

    EvalTerm::LetExpr { val, mult, body } => EvalTerm::LetExpr {
      val: Box::new(shift(val, cutoff, amount)),
      mult: *mult,
      body: Box::new(shift(body, cutoff + 1, amount)),
    },

    EvalTerm::Const { .. } => term.clone(),
    EvalTerm::Sort { .. } => term.clone(),
    EvalTerm::Lit { .. } => term.clone(),

    EvalTerm::Prim { idx, args } => EvalTerm::Prim {
      idx: *idx,
      args: args.iter().map(|a| shift(a, cutoff, amount)).collect(),
    },

    EvalTerm::Recursor {
      info,
      motive,
      cases,
      scrutinee,
      mult,
    } => EvalTerm::Recursor {
      info: info.clone(),
      motive: Box::new(shift(motive, cutoff, amount)),
      cases: cases.iter().map(|c| shift(c, cutoff, amount)).collect(),
      scrutinee: Box::new(shift(scrutinee, cutoff, amount)),
      mult: *mult,
    },

    EvalTerm::Region { reg, body, mult } => EvalTerm::Region {
      reg: reg.clone(),
      body: Box::new(shift(body, cutoff, amount)),
      mult: *mult,
    },

    EvalTerm::Borrow {
      kind,
      reg,
      body,
      mult,
    } => EvalTerm::Borrow {
      kind: kind.clone(),
      reg: reg.clone(),
      body: Box::new(shift(body, cutoff, amount)),
      mult: *mult,
    },

    EvalTerm::Proj {
      field_idx,
      struct_idx,
      arg,
    } => EvalTerm::Proj {
      field_idx: *field_idx,
      struct_idx: *struct_idx,
      arg: Box::new(shift(arg, cutoff, amount)),
    },

    EvalTerm::ProjField { base, field_idx } => EvalTerm::ProjField {
      base: Box::new(shift(base, cutoff, amount)),
      field_idx: *field_idx,
    },
  }
}

// ---------------------------------------------------------------------------
// Weak Head Normal Form reduction
// ---------------------------------------------------------------------------

/// One step of WHNF reduction. Returns `Some(reduced)` if a reduction was
/// taken, or `None` if the term is already in WHNF.
///
/// WHNF reduction steps:
///   App(Lam { body }, arg) → subst(body, 0, arg)    (β-reduction)
///   LetExpr { val, body }  → subst(body, 0, val)    (let reduction)
///   App(App(...), arg)     → first reduce the function part
pub fn whnf_step(term: &EvalTerm) -> Option<EvalTerm> {
  match term {
    EvalTerm::App { fun, arg, mult } => match fun.as_ref() {
      EvalTerm::Lam { body, .. } => {
        let reduced = subst(body, 0, arg);
        Some(reduced)
      }
      non_lam @ EvalTerm::App { .. } => {
        let fun_whnf = whnf_step(non_lam)?;
        Some(EvalTerm::App {
          fun: Box::new(fun_whnf),
          arg: arg.clone(),
          mult: *mult,
        })
      }
      _ => None,
    },

    EvalTerm::LetExpr { val, mult: _, body } => {
      let reduced = subst(body, 0, val);
      Some(reduced)
    }

    _ => None,
  }
}

/// Reduce a term to Weak Head Normal Form by iterating `whnf_step`.
///
/// WHNF values are: Var, Lam, Const, Sort, Lit, Prim, Recursor,
/// Region, Borrow, Proj, ProjField — and `App(f, arg)` where `f` is
/// not a `Lam` (i.e., a neutral application).
pub fn whnf(term: &EvalTerm) -> EvalTerm {
  let mut current = term.clone();
  while let Some(next) = whnf_step(&current) {
    current = next;
  }
  current
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_var_construction() {
    let v = var(0, Multiplicity::Many);
    assert_eq!(
      v,
      EvalTerm::Var {
        idx: 0,
        mult: Multiplicity::Many
      }
    );
    assert_eq!(v.to_string(), "(var 0 ω)");
  }

  #[test]
  fn test_lam_construction() {
    let body = var(0, Multiplicity::Many);
    let l = lam(Multiplicity::Many, body);
    assert_eq!(l.to_string(), "(lam ω (var 0 ω))");
  }

  #[test]
  fn test_app_construction() {
    let fun = lam(Multiplicity::Many, var(0, Multiplicity::Many));
    let arg = const_(3);
    let a = app(fun, arg, Multiplicity::Many);
    assert_eq!(a.to_string(), "(app ω (lam ω (var 0 ω)) (const #3))");
  }

  #[test]
  fn test_identity_lambda() {
    let id_lam = lam(Multiplicity::Many, var(0, Multiplicity::Many));
    let t = app(id_lam, const_(7), Multiplicity::Many);
    assert_eq!(t.to_string(), "(app ω (lam ω (var 0 ω)) (const #7))");
  }

  #[test]
  fn test_let_expr_construction() {
    let val = lit(Literal::Int { v: 42 });
    let body = var(0, Multiplicity::Many);
    let l = let_expr(val, Multiplicity::Many, body);
    assert_eq!(l.to_string(), "(let ω (lit 42) (var 0 ω))");
  }

  #[test]
  fn test_literals() {
    assert_eq!(lit(Literal::Nat { v: 10 }).to_string(), "(lit 10n)");
    assert_eq!(lit(Literal::Int { v: -5 }).to_string(), "(lit -5)");
    assert_eq!(
      lit(Literal::Str {
        value: "hello".into()
      })
      .to_string(),
      r#"(lit "hello")"#
    );
    assert_eq!(
      lit(Literal::Float {
        value: FloatValue(3.14)
      })
      .to_string(),
      "(lit 3.14)"
    );
    assert_eq!(lit(Literal::Char { c: 65 }).to_string(), "(lit 'A')");
  }

  #[test]
  fn test_sort_construction() {
    assert_eq!(sort(0).to_string(), "(sort 0)");
    assert_eq!(sort(1).to_string(), "(sort 1)");
    assert_eq!(sort(2).to_string(), "(sort 2)");
  }

  #[test]
  fn test_const_construction() {
    assert_eq!(const_(0).to_string(), "(const #0)");
    assert_eq!(const_(42).to_string(), "(const #42)");
  }

  #[test]
  fn test_prim_construction() {
    let p = prim(1, vec![const_(0), var(0, Multiplicity::Many)]);
    assert_eq!(p.to_string(), "(prim #1 (const #0) (var 0 ω))");
  }

  #[test]
  fn test_recursor_construction() {
    let info = RecursorInfo::new(0, 1, 1, 2);
    let motive = lam(Multiplicity::Many, var(0, Multiplicity::Many));
    let none_case = const_(1);
    let some_case = lam(Multiplicity::Many, const_(2));
    let scrutinee = var(0, Multiplicity::Many);
    let r = recursor(
      info,
      motive,
      vec![none_case, some_case],
      scrutinee,
      Multiplicity::Many,
    );
    let s = r.to_string();
    assert!(s.contains("recursor"));
    assert!(s.contains("rec(#0 params=1 motives=1 cases=2)"));
  }

  #[test]
  fn test_region_construction() {
    let body = var(0, Multiplicity::Linear);
    let r = region(Region::Stack, body, Multiplicity::Linear);
    assert_eq!(r.to_string(), "(region ! r_stack (var 0 !))");
  }

  #[test]
  fn test_borrow_construction() {
    let body = var(0, Multiplicity::Many);
    let b = borrow(BorrowKind::Unique, Region::Heap, body, Multiplicity::Many);
    assert_eq!(b.to_string(), "(borrow ω unique r_heap (var 0 ω))");
  }

  #[test]
  fn test_proj_construction() {
    let arg = var(0, Multiplicity::Many);
    let p = proj(1, 0, arg);
    assert_eq!(p.to_string(), "(proj .1 struct=#0 (var 0 ω))");
  }

  #[test]
  fn test_proj_field_construction() {
    let base = var(0, Multiplicity::Many);
    let pf = proj_field(base, 2);
    assert_eq!(pf.to_string(), "(proj_field .2 (var 0 ω))");
  }

  #[test]
  fn test_multiplicity_display() {
    assert_eq!(Multiplicity::Zero.to_string(), "0");
    assert_eq!(Multiplicity::Many.to_string(), "ω");
    assert_eq!(Multiplicity::Linear.to_string(), "!");
    assert_eq!(Multiplicity::Affine.to_string(), "?");
  }

  #[test]
  fn test_region_display() {
    assert_eq!(Region::Stack.to_string(), "r_stack");
    assert_eq!(Region::Heap.to_string(), "r_heap");
    assert_eq!(Region::Borrow { depth: 3 }.to_string(), "r_borrow(3)");
    assert_eq!(Region::Param { idx: 1 }.to_string(), "r_param(1)");
  }

  #[test]
  fn test_borrow_kind_display() {
    assert_eq!(BorrowKind::Shared.to_string(), "shared");
    assert_eq!(BorrowKind::Unique.to_string(), "unique");
  }

  #[test]
  fn test_recursor_info_display() {
    let info = RecursorInfo::new(5, 2, 1, 3);
    assert_eq!(info.to_string(), "rec(#5 params=2 motives=1 cases=3)");
  }

  #[test]
  fn test_env_default() {
    let env = Env::default();
    assert!(env.constants.is_empty());
    assert!(env.primitives.is_empty());
    assert!(env.recursors.is_empty());
  }

  #[test]
  fn test_term_equality() {
    let a = var(0, Multiplicity::Many);
    let b = var(0, Multiplicity::Many);
    assert_eq!(a, b);

    let a = var(0, Multiplicity::Linear);
    let b = var(0, Multiplicity::Many);
    assert_ne!(a, b);
  }

  #[test]
  fn test_nested_term() {
    let inner = app(
      lam(Multiplicity::Many, var(0, Multiplicity::Many)),
      const_(5),
      Multiplicity::Many,
    );
    let outer = lam(Multiplicity::Many, inner);
    assert_eq!(
      outer.to_string(),
      "(lam ω (app ω (lam ω (var 0 ω)) (const #5)))"
    );
  }

  #[test]
  fn test_float_value_eq() {
    let a = FloatValue(3.14);
    let b = FloatValue(3.14);
    assert_eq!(a, b);

    let c = FloatValue(0.0);
    let d = FloatValue(-0.0);
    assert_ne!(c, d); // different bit patterns
  }

  #[test]
  fn test_float_value_ord() {
    let a = FloatValue(1.0);
    let b = FloatValue(2.0);
    assert!(a < b);
  }

  // -- subst tests ---------------------------------------------------------

  #[test]
  fn test_subst_var_less_than_index() {
    let t = var(0, Multiplicity::Many);
    let result = subst(&t, 1, &const_(99));
    assert_eq!(result, t);
  }

  #[test]
  fn test_subst_var_equal_index() {
    let t = var(0, Multiplicity::Many);
    let r = const_(42);
    let result = subst(&t, 0, &r);
    assert_eq!(result, r);
  }

  #[test]
  fn test_subst_var_greater_than_index() {
    let t = var(2, Multiplicity::Many);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, var(1, Multiplicity::Many));
  }

  #[test]
  fn test_subst_lam_body() {
    // subst(λ. var(3), 1, const(99))
    // → λ. subst(var(3), 2, shift(const(99), 0, 1))
    // → λ. subst(var(3), 2, const(99))
    // → λ. var(2)  (because 3 > 2, decrement: 3-1=2)
    let body = var(3, Multiplicity::Many);
    let lam_term = lam(Multiplicity::Many, body);
    let r = const_(99);
    let result = subst(&lam_term, 1, &r);
    assert_eq!(result, lam(Multiplicity::Many, var(2, Multiplicity::Many)));
  }

  #[test]
  fn test_subst_beta_reduction() {
    // (λx. x) 42  →  subst(var(0), 0, 42)  =  42
    let lam_body = var(0, Multiplicity::Many);
    let id = lam(Multiplicity::Many, lam_body);
    let arg = const_(42);
    let result = subst(&id, 0, &arg);
    // subst(λ. var(0), 0, const(42))
    // → λ. subst(var(0), 1, shift(const(42), 0, 1))
    // → λ. subst(var(0), 1, const(42))
    // → λ. var(0) (since var(0) < 1)
    // → identity function again
    // WAIT — this is NOT the same as β-reduction. subst replaces a free variable,
    // not beta-reduction. Let me think again...
    //
    // subst(t, i, r) substitutes r for de Bruijn index i in t.
    // (λ. body) arg → subst(body, 0, arg) is β-reduction.
    // So the id function applied to 42 is: λ. var(0) applied to const(42)
    // = app(lam(id_body), arg)
    assert_eq!(result, lam(Multiplicity::Many, var(0, Multiplicity::Many)));
  }

  #[test]
  fn test_subst_under_app() {
    // (x y) with x at 0 and y at 1, substitute 0 with const(10)
    let t = app(
      var(0, Multiplicity::Many),
      var(1, Multiplicity::Many),
      Multiplicity::Many,
    );
    let r = const_(10);
    let result = subst(&t, 0, &r);
    assert_eq!(
      result,
      app(const_(10), var(0, Multiplicity::Many), Multiplicity::Many)
    );
  }

  #[test]
  fn test_subst_const_unchanged() {
    let t = const_(5);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, t);
  }

  #[test]
  fn test_subst_sort_unchanged() {
    let t = sort(1);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, t);
  }

  #[test]
  fn test_subst_lit_unchanged() {
    let t = lit(Literal::Int { v: 7 });
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, t);
  }

  #[test]
  fn test_subst_prim_args() {
    let t = prim(
      0,
      vec![var(0, Multiplicity::Many), var(1, Multiplicity::Many)],
    );
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(
      result,
      prim(0, vec![const_(99), var(0, Multiplicity::Many)])
    );
  }

  #[test]
  fn test_subst_let_expr() {
    // let x = v in body — encodes (λ. body) v, so body has idx 0 = x
    let val = var(0, Multiplicity::Many);
    let body = var(0, Multiplicity::Many); // body: idx 0 = let-bound value
    let t = let_expr(val, Multiplicity::Many, body);
    let r = const_(99);
    // subst(let_expr(val, body), 0, r)
    // → let_expr(subst(val, 0, r), subst(body, 1, shift(r, 0, 1)))
    let result = subst(&t, 0, &r);
    assert_eq!(
      result,
      let_expr(
        const_(99),
        Multiplicity::Many,
        var(0, Multiplicity::Many) // body: idx 0 is still the let-bound value, shift(r) isn't used for idx 0
      )
    );
  }

  #[test]
  fn test_subst_recursor() {
    let info = RecursorInfo::new(0, 1, 1, 2);
    let motive = var(0, Multiplicity::Many);
    let case = const_(1);
    let scrutinee = var(1, Multiplicity::Many);
    let t = recursor(info, motive, vec![case], scrutinee, Multiplicity::Many);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    match result {
      EvalTerm::Recursor {
        motive,
        cases,
        scrutinee,
        ..
      } => {
        assert_eq!(*motive, const_(99));
        assert_eq!(cases, vec![const_(1)]);
        assert_eq!(*scrutinee, var(0, Multiplicity::Many));
      }
      _ => panic!("expected Recursor"),
    }
  }

  // -- shift tests ---------------------------------------------------------

  #[test]
  fn test_shift_var_below_cutoff() {
    let t = var(0, Multiplicity::Many);
    let result = shift(&t, 1, 5);
    assert_eq!(result, t);
  }

  #[test]
  fn test_shift_var_above_cutoff() {
    let t = var(3, Multiplicity::Many);
    let result = shift(&t, 2, 5);
    assert_eq!(result, var(8, Multiplicity::Many));
  }

  #[test]
  fn test_shift_var_at_cutoff() {
    let t = var(2, Multiplicity::Many);
    let result = shift(&t, 2, 3);
    assert_eq!(result, var(5, Multiplicity::Many));
  }

  #[test]
  fn test_shift_lam() {
    // λ. var(1) with cutoff 0, shift 2
    // cutoff increases inside lam to 1, so var(1) >= 1 → var(3)
    // result: λ. var(3)
    let body = var(1, Multiplicity::Many);
    let t = lam(Multiplicity::Many, body);
    let result = shift(&t, 0, 2);
    assert_eq!(result, lam(Multiplicity::Many, var(3, Multiplicity::Many)));
  }

  #[test]
  fn test_shift_lam_lift_identity() {
    // Shift the identity function λ. var(0) up by 1
    // λ. var(0): var(0) < cutoff(1) after entering lam, so unchanged
    // result: λ. var(0)
    let id_body = var(0, Multiplicity::Many);
    let t = lam(Multiplicity::Many, id_body);
    let result = shift(&t, 0, 1);
    assert_eq!(result, lam(Multiplicity::Many, var(0, Multiplicity::Many)));
  }

  #[test]
  fn test_shift_let_expr() {
    // let v in body: both shift
    let val = var(2, Multiplicity::Many);
    let body = var(2, Multiplicity::Many);
    let t = let_expr(val, Multiplicity::Many, body);
    let result = shift(&t, 0, 2);
    // val: var(2) >= 0 → var(4)
    // body: cutoff becomes 1 inside let-expr body, var(2) >= 1 → var(4)
    assert_eq!(
      result,
      let_expr(
        var(4, Multiplicity::Many),
        Multiplicity::Many,
        var(4, Multiplicity::Many)
      )
    );
  }

  #[test]
  fn test_shift_const_unchanged() {
    let t = const_(0);
    let result = shift(&t, 0, 5);
    assert_eq!(result, t);
  }

  #[test]
  fn test_shift_sort_unchanged() {
    let t = sort(0);
    let result = shift(&t, 0, 5);
    assert_eq!(result, t);
  }

  #[test]
  fn test_shift_lit_unchanged() {
    let t = lit(Literal::Int { v: 3 });
    let result = shift(&t, 0, 5);
    assert_eq!(result, t);
  }

  // -- whnf tests ----------------------------------------------------------

  #[test]
  fn test_whnf_step_beta() {
    // (λx. x) const(42) → const(42)
    let id_body = var(0, Multiplicity::Many);
    let id = lam(Multiplicity::Many, id_body);
    let arg = const_(42);
    let t = app(id, arg, Multiplicity::Many);
    let result = whnf_step(&t);
    assert_eq!(result, Some(const_(42)));
  }

  #[test]
  fn test_whnf_step_beta_with_free_var() {
    // (λx. x) var(1) → var(1)
    // β-reduction: subst(var(0), 0, var(1)) → var(1)
    let id_body = var(0, Multiplicity::Many);
    let id = lam(Multiplicity::Many, id_body);
    let arg = var(1, Multiplicity::Many);
    let t = app(id, arg, Multiplicity::Many);
    let result = whnf_step(&t);
    assert_eq!(result, Some(var(1, Multiplicity::Many)));
  }

  #[test]
  fn test_whnf_step_let_expr() {
    // let const(42) in var(0) → const(42)
    let val = const_(42);
    let body = var(0, Multiplicity::Many);
    let t = let_expr(val, Multiplicity::Many, body);
    let result = whnf_step(&t);
    assert_eq!(result, Some(const_(42)));
  }

  #[test]
  fn test_whnf_step_nested_app() {
    // ((λx. x) (λy. y)) z → step1: app(λy.y, z) → z
    let id_lam = lam(Multiplicity::Many, var(0, Multiplicity::Many));
    let inner_app = app(id_lam.clone(), id_lam, Multiplicity::Many);
    let outer_app = app(inner_app, const_(1), Multiplicity::Many);
    // First whnf_step: reduces inner_app to id_lam
    let r1 = whnf_step(&outer_app).unwrap();
    // r1 = app(id_lam, const(1), ω)
    let r2 = whnf_step(&r1).unwrap();
    assert_eq!(r2, const_(1));
  }

  #[test]
  fn test_whnf_step_neutral() {
    // const(0) const(1) → no reduction (const is neutral, not a lam)
    let t = app(const_(0), const_(1), Multiplicity::Many);
    assert_eq!(whnf_step(&t), None);
  }

  #[test]
  fn test_whnf_value_unchanged() {
    assert_eq!(whnf(&const_(5)), const_(5));
    assert_eq!(whnf(&sort(1)), sort(1));
    assert_eq!(
      whnf(&lit(Literal::Str { value: "hi".into() })),
      lit(Literal::Str { value: "hi".into() })
    );
  }

  #[test]
  fn test_whnf_beta_reduces_to_value() {
    let id_lam = lam(Multiplicity::Many, var(0, Multiplicity::Many));
    let t = app(id_lam, const_(7), Multiplicity::Many);
    assert_eq!(whnf(&t), const_(7));
  }

  #[test]
  fn test_whnf_let_reduces_to_value() {
    let t = let_expr(const_(42), Multiplicity::Many, var(0, Multiplicity::Many));
    assert_eq!(whnf(&t), const_(42));
  }

  #[test]
  fn test_whnf_nested_beta() {
    // ((λx. λy. x) a) b → a
    let inner_lam = lam(Multiplicity::Many, var(1, Multiplicity::Many));
    let outer_lam = lam(Multiplicity::Many, inner_lam);
    let app1 = app(outer_lam, const_(10), Multiplicity::Many);
    let app2 = app(app1, const_(20), Multiplicity::Many);
    assert_eq!(whnf(&app2), const_(10));
  }

  // -- property tests ------------------------------------------------------

  #[test]
  fn test_property_subst_then_shift_commutes() {
    // For closed terms (no free variables), shift(subst(t, 0, r), 0, 0) == subst(shift(t, 0, 0), 0, shift(r, 0, 0))
    // Simpler: subst(shift(t, 0, 1), 0, r) == t when t has no free vars
    // Because shift adds one to all free indices, and subst removes index 0.
    let t = const_(42);
    let shifted = shift(&t, 0, 1);
    let r = lit(Literal::Nat { v: 7 });
    let result = subst(&shifted, 0, &r);
    assert_eq!(result, t);
  }
}
