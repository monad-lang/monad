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

use crate::Map;

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
  /// Boolean (0 = false, 1 = true, enforced by constructors)
  Bool { v: u8 },
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
      Literal::Bool { v } => write!(f, "{}", if *v == 0 { "false" } else { "true" }),
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
  /// De Bruijn variable
  Var { idx: u64 },

  /// Lambda: parameter multiplicity + body
  Lam {
    param_mult: Multiplicity,
    body: Box<EvalTerm>,
  },

  /// Application: fn(arg)
  App {
    fun: Box<EvalTerm>,
    arg: Box<EvalTerm>,
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
  },

  /// Region-scoped value — all inner allocations live in the given region
  Region { reg: Region, body: Box<EvalTerm> },

  /// Borrow: creates a reference from a region-allocated value
  Borrow {
    kind: BorrowKind,
    reg: Region,
    body: Box<EvalTerm>,
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
      EvalTerm::Var { idx } => write!(f, "(var {idx})"),
      EvalTerm::Lam { param_mult, body } => write!(f, "(lam {param_mult} {body})"),
      EvalTerm::App { fun, arg } => write!(f, "(app {fun} {arg})"),
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
      } => {
        write!(f, "(recursor {info} {motive}")?;
        for c in cases {
          write!(f, " {c}")?;
        }
        write!(f, " {scrutinee})")
      }
      EvalTerm::Region { reg, body } => write!(f, "(region {reg} {body})"),
      EvalTerm::Borrow { kind, reg, body } => write!(f, "(borrow {kind} {reg} {body})"),
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
  /// Maps const_idx → Vec<(recursor_idx, case_idx)> for recursor dispatch.
  /// Each const can be a constructor in multiple inductive types.
  pub constructor_tags: Map<u64, Vec<(u64, u64)>>,
}

impl Env {
  pub fn new() -> Self {
    Env::default()
  }
}

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

pub fn var(idx: u64) -> EvalTerm {
  EvalTerm::Var { idx }
}

pub fn lam(param_mult: Multiplicity, body: EvalTerm) -> EvalTerm {
  EvalTerm::Lam {
    param_mult,
    body: Box::new(body),
  }
}

pub fn app(fun: EvalTerm, arg: EvalTerm) -> EvalTerm {
  EvalTerm::App {
    fun: Box::new(fun),
    arg: Box::new(arg),
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
) -> EvalTerm {
  EvalTerm::Recursor {
    info,
    motive: Box::new(motive),
    cases,
    scrutinee: Box::new(scrutinee),
  }
}

pub fn region(reg: Region, body: EvalTerm) -> EvalTerm {
  EvalTerm::Region {
    reg,
    body: Box::new(body),
  }
}

pub fn borrow(kind: BorrowKind, reg: Region, body: EvalTerm) -> EvalTerm {
  EvalTerm::Borrow {
    kind,
    reg,
    body: Box::new(body),
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
/// entering a binder (Lam body) to avoid capture.
pub fn subst(term: &EvalTerm, index: u64, replacement: &EvalTerm) -> EvalTerm {
  use std::cmp::Ordering;

  match term {
    EvalTerm::Var { idx } => match idx.cmp(&index) {
      Ordering::Less => term.clone(),
      Ordering::Equal => replacement.clone(),
      Ordering::Greater => EvalTerm::Var { idx: idx - 1 },
    },

    EvalTerm::Lam { param_mult, body } => {
      let shifted = shift(replacement, 0, 1);
      EvalTerm::Lam {
        param_mult: *param_mult,
        body: Box::new(subst(body, index + 1, &shifted)),
      }
    }

    EvalTerm::App { fun, arg } => EvalTerm::App {
      fun: Box::new(subst(fun, index, replacement)),
      arg: Box::new(subst(arg, index, replacement)),
    },

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
    } => EvalTerm::Recursor {
      info: info.clone(),
      motive: Box::new(subst(motive, index, replacement)),
      cases: cases.iter().map(|c| subst(c, index, replacement)).collect(),
      scrutinee: Box::new(subst(scrutinee, index, replacement)),
    },

    EvalTerm::Region { reg, body } => EvalTerm::Region {
      reg: reg.clone(),
      body: Box::new(subst(body, index, replacement)),
    },

    EvalTerm::Borrow { kind, reg, body } => EvalTerm::Borrow {
      kind: kind.clone(),
      reg: reg.clone(),
      body: Box::new(subst(body, index, replacement)),
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
    EvalTerm::Var { idx } => EvalTerm::Var {
      idx: idx_shift(idx),
    },

    EvalTerm::Lam { param_mult, body } => EvalTerm::Lam {
      param_mult: *param_mult,
      body: Box::new(shift(body, cutoff + 1, amount)),
    },

    EvalTerm::App { fun, arg } => EvalTerm::App {
      fun: Box::new(shift(fun, cutoff, amount)),
      arg: Box::new(shift(arg, cutoff, amount)),
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
    } => EvalTerm::Recursor {
      info: info.clone(),
      motive: Box::new(shift(motive, cutoff, amount)),
      cases: cases.iter().map(|c| shift(c, cutoff, amount)).collect(),
      scrutinee: Box::new(shift(scrutinee, cutoff, amount)),
    },

    EvalTerm::Region { reg, body } => EvalTerm::Region {
      reg: reg.clone(),
      body: Box::new(shift(body, cutoff, amount)),
    },

    EvalTerm::Borrow { kind, reg, body } => EvalTerm::Borrow {
      kind: kind.clone(),
      reg: reg.clone(),
      body: Box::new(shift(body, cutoff, amount)),
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
/// WHNF reduction step:
///   App(Lam { body }, arg) → subst(body, 0, arg)    (β-reduction)
pub fn whnf_step(term: &EvalTerm) -> Option<EvalTerm> {
  match term {
    EvalTerm::App { fun, arg } => match fun.as_ref() {
      EvalTerm::Lam { body, .. } => {
        let reduced = subst(body, 0, arg);
        Some(reduced)
      }
      non_lam @ EvalTerm::App { .. } => {
        let fun_whnf = whnf_step(non_lam)?;
        Some(EvalTerm::App {
          fun: Box::new(fun_whnf),
          arg: arg.clone(),
        })
      }
      _ => None,
    },

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
// EvalError — evaluation failures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum EvalError {
  UnboundVariable(usize),
  UnknownConstant(usize),
  UnknownPrimitive(usize),
  UnknownRecursor(usize),
  NoScrutineeForDispatch,
  ConstructorTagNotFound(u64, u64),
  CaseIndexOutOfBounds(u64, u64),
  PrimCallFailed(String),
  NotAFunction(EvalTerm),
}

impl Display for EvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EvalError::UnboundVariable(i) => write!(f, "unbound de Bruijn variable #{i}"),
      EvalError::UnknownConstant(i) => write!(f, "unknown constant #{i}"),
      EvalError::UnknownPrimitive(i) => write!(f, "unknown primitive #{i}"),
      EvalError::UnknownRecursor(i) => write!(f, "unknown recursor #{i}"),
      EvalError::NoScrutineeForDispatch => write!(f, "recursor dispatch with no scrutinee"),
      EvalError::ConstructorTagNotFound(rec, con) => {
        write!(f, "constructor #{con} not found in recursor #{rec}")
      }
      EvalError::CaseIndexOutOfBounds(rec, idx) => {
        write!(f, "case index {idx} out of bounds for recursor #{rec}")
      }
      EvalError::PrimCallFailed(msg) => write!(f, "primitive call failed: {msg}"),
      EvalError::NotAFunction(t) => write!(f, "not a function: {t}"),
    }
  }
}

// ---------------------------------------------------------------------------
// Eval — recursive small-step evaluator for EvalTerm
// ---------------------------------------------------------------------------

/// Evaluate `term` in the given context of local de Bruijn values and global Env.
///
/// The evaluator reduces to weak head normal form (WHNF):
///   App(Lam { body }, arg) → subst(body, 0, arg)    (β-reduction)
///   Var { idx }            → locals[locals.len()-1-idx]
///   Const { idx }          → env.constants[idx] (then evaluate)
///   Lam, Sort, Lit         → values (no further reduction)
///
/// Recursor and Prim are driven by their own dispatch logic.
pub fn eval(term: &EvalTerm, locals: &[EvalTerm], env: &Env) -> Result<EvalTerm, EvalError> {
  match term {
    // -- Application ------------------------------------------------------
    EvalTerm::App { fun, arg } => {
      let reduced_fun = eval(fun, locals, env)?;
      match reduced_fun {
        EvalTerm::Lam { body, .. } => {
          let reduced = subst(&body, 0, arg);
          eval(&reduced, locals, env)
        }
        EvalTerm::Const { idx } => {
          let resolved = resolve_const(idx, env)?;
          match resolved {
            EvalTerm::Lam { .. } => eval(&app(resolved, arg.as_ref().clone()), locals, env),
            EvalTerm::Prim {
              idx: p_idx,
              args: ref p_args,
            } => eval_prim_app(p_idx, p_args, arg, env, locals),
            _ => Ok(app(resolved, arg.as_ref().clone())),
          }
        }
        EvalTerm::Prim {
          idx: p_idx,
          args: ref p_args,
        } => eval_prim_app(p_idx, p_args, arg, env, locals),
        other => Ok(app(other, arg.as_ref().clone())),
      }
    }

    // -- Variable lookup --------------------------------------------------
    EvalTerm::Var { idx } => {
      let idx = *idx as usize;
      if idx < locals.len() {
        Ok(locals[locals.len() - 1 - idx].clone())
      } else {
        Err(EvalError::UnboundVariable(idx))
      }
    }

    // -- Sort / Literal / Lambda / Const — values --------------------------
    EvalTerm::Sort { .. }
    | EvalTerm::Lit { .. }
    | EvalTerm::Lam { .. }
    | EvalTerm::Const { .. } => Ok(term.clone()),

    // -- Recursor dispatch ------------------------------------------------
    EvalTerm::Recursor {
      info,
      motive: _motive,
      cases,
      scrutinee,
    } => {
      let reduced_scrutinee = eval(scrutinee, locals, env)?;
      dispatch_recursor(&reduced_scrutinee, info, cases, locals, env)
    }

    // -- Primitive call ---------------------------------------------------
    EvalTerm::Prim { idx, args } => {
      let arity = env
        .primitives
        .get(*idx as usize)
        .map(|(_, a)| *a)
        .unwrap_or(0);
      let evaluated_args: Vec<EvalTerm> = args
        .iter()
        .map(|a| eval(a, locals, env))
        .collect::<Result<Vec<_>, _>>()?;
      if arity > 0 && evaluated_args.len() >= arity {
        exec_prim(*idx, &evaluated_args, env)
      } else {
        Ok(EvalTerm::Prim {
          idx: *idx,
          args: evaluated_args,
        })
      }
    }

    // -- Region / Borrow / Proj — evaluate body ----------------------------
    EvalTerm::Region { body, .. } => eval(body, locals, env),
    EvalTerm::Borrow { body, .. } => eval(body, locals, env),
    EvalTerm::Proj { arg, .. } => eval(arg, locals, env),
    EvalTerm::ProjField { base, .. } => eval(base, locals, env),
  }
}

/// Top-level entry point: evaluate with an empty local environment.
pub fn eval_entry(term: &EvalTerm, env: &Env) -> Result<EvalTerm, EvalError> {
  eval(term, &[], env)
}

// ---------------------------------------------------------------------------
// Recursor dispatch
// ---------------------------------------------------------------------------

fn dispatch_recursor(
  scrutinee: &EvalTerm,
  info: &RecursorInfo,
  cases: &[EvalTerm],
  locals: &[EvalTerm],
  env: &Env,
) -> Result<EvalTerm, EvalError> {
  let rec_idx = info.rec_idx;

  let case_idx = match scrutinee {
    EvalTerm::Lit {
      l: Literal::Bool { v },
    } => {
      if *v == 0 {
        1
      } else {
        0
      }
    }

    _ => {
      let con_idx = match scrutinee {
        EvalTerm::Const { idx } => *idx,
        EvalTerm::App { fun, .. } => match fun.as_ref() {
          EvalTerm::Const { idx } => *idx,
          _ => {
            return Err(EvalError::NotAFunction(scrutinee.clone()));
          }
        },
        _ => {
          return Err(EvalError::NotAFunction(scrutinee.clone()));
        }
      };
      find_constructor_tag(rec_idx, con_idx, env)?
    }
  };

  if case_idx >= cases.len() as u64 {
    return Err(EvalError::CaseIndexOutOfBounds(rec_idx, case_idx));
  }

  let case_fn = &cases[case_idx as usize];

  // Apply case function to constructor arguments (if any)
  let result = match scrutinee {
    EvalTerm::App { arg, .. } => app(case_fn.clone(), arg.as_ref().clone()),
    _ => case_fn.clone(),
  };

  eval(&result, locals, env)
}

fn find_constructor_tag(rec_idx: u64, con_idx: u64, env: &Env) -> Result<u64, EvalError> {
  let tags = env
    .constructor_tags
    .get(&con_idx)
    .ok_or(EvalError::ConstructorTagNotFound(rec_idx, con_idx))?;

  for (r_idx, c_idx) in tags {
    if *r_idx == rec_idx {
      return Ok(*c_idx);
    }
  }

  Err(EvalError::ConstructorTagNotFound(rec_idx, con_idx))
}

// ---------------------------------------------------------------------------
// Primitive execution
// ---------------------------------------------------------------------------

fn exec_prim(idx: u64, args: &[EvalTerm], env: &Env) -> Result<EvalTerm, EvalError> {
  let idx = idx as usize;
  let (name, _arity) = env
    .primitives
    .get(idx)
    .ok_or(EvalError::UnknownPrimitive(idx))?;

  match name.as_str() {
    "i8_add" | "i16_add" | "i32_add" | "i64_add" | "u8_add" | "u16_add" | "u32_add" | "u64_add" => {
      kernel_int_binop(args, |a, b| a.wrapping_add(b))
    }
    "i8_sub" | "i16_sub" | "i32_sub" | "i64_sub" | "u8_sub" | "u16_sub" | "u32_sub" | "u64_sub" => {
      kernel_int_binop(args, |a, b| a.wrapping_sub(b))
    }
    "i8_mul" | "i16_mul" | "i32_mul" | "i64_mul" | "u8_mul" | "u16_mul" | "u32_mul" | "u64_mul" => {
      kernel_int_binop(args, |a, b| a.wrapping_mul(b))
    }
    "i8_div" | "i16_div" | "i32_div" | "i64_div" | "u8_div" | "u16_div" | "u32_div" | "u64_div" => {
      kernel_int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_div(b) })
    }
    "i8_eq" | "i16_eq" | "i32_eq" | "i64_eq" | "u8_eq" | "u16_eq" | "u32_eq" | "u64_eq" => {
      kernel_int_cmp(args, |a, b| a == b)
    }
    "u8_lt" => kernel_int_cmp(args, |a, b| a < b),
    "u8_gt" => kernel_int_cmp(args, |a, b| a > b),
    "f32_add" | "f64_add" => kernel_float_binop(args, |a, b| a + b),
    "f32_sub" | "f64_sub" => kernel_float_binop(args, |a, b| a - b),
    "f32_mul" | "f64_mul" => kernel_float_binop(args, |a, b| a * b),
    "f32_div" | "f64_div" => kernel_float_binop(args, |a, b| a / b),
    "f32_eq" | "f64_eq" => kernel_float_cmp(args, |a, b| a == b),
    "string_eq" => kernel_string_eq(args),
    "string_concat" => kernel_string_concat(args),
    "string_length" => kernel_string_length(args),
    "string_starts_with" => kernel_string_starts_with(args),
    "string_slice" => kernel_string_slice(args),
    "string_drop" => kernel_string_drop(args),
    "i8_to_string" => kernel_int_to_string(args, |v| (v as i8).to_string()),
    "i16_to_string" => kernel_int_to_string(args, |v| (v as i16).to_string()),
    "i32_to_string" => kernel_int_to_string(args, |v| (v as i32).to_string()),
    "i64_to_string" => kernel_int_to_string(args, |v| v.to_string()),
    "u8_to_string" => kernel_int_to_string(args, |v| (v as u8).to_string()),
    "u16_to_string" => kernel_int_to_string(args, |v| (v as u16).to_string()),
    "u32_to_string" => kernel_int_to_string(args, |v| (v as u32).to_string()),
    "u64_to_string" => kernel_int_to_string(args, |v| (v as u64).to_string()),
    "f32_to_string" | "f64_to_string" => kernel_float_to_string(args),
    "print_str" => kernel_print_str(args),
    _ => Ok(EvalTerm::Prim {
      idx: idx as u64,
      args: args.to_vec(),
    }),
  }
}

fn extract_int(arg: &EvalTerm) -> Result<i64, EvalError> {
  match arg {
    EvalTerm::Lit {
      l: Literal::Int { v },
    } => Ok(*v),
    _ => Err(EvalError::PrimCallFailed(format!(
      "expected int literal, got {arg}"
    ))),
  }
}

fn extract_string(arg: &EvalTerm) -> Result<String, EvalError> {
  match arg {
    EvalTerm::Lit {
      l: Literal::Str { value },
    } => Ok(value.clone()),
    _ => Err(EvalError::PrimCallFailed(format!(
      "expected string literal, got {arg}"
    ))),
  }
}

fn kernel_int_binop(args: &[EvalTerm], op: fn(i64, i64) -> i64) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("int binop needs 2 args".into()));
  }
  let a = extract_int(&args[0])?;
  let b = extract_int(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Int { v: op(a, b) },
  })
}

fn kernel_int_cmp(args: &[EvalTerm], op: fn(i64, i64) -> bool) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("int cmp needs 2 args".into()));
  }
  let a = extract_int(&args[0])?;
  let b = extract_int(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Bool {
      v: if op(a, b) { 1 } else { 0 },
    },
  })
}

fn kernel_string_eq(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("string_eq needs 2 args".into()));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Bool {
      v: if a == b { 1 } else { 0 },
    },
  })
}

fn kernel_string_concat(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed(
      "string_concat needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Str { value: a + &b },
  })
}

/// Resolve a constant index to its definition in the environment.
/// Returns the definition term (which may be a Lam, Lit, etc.).
fn eval_prim_app(
  p_idx: u64,
  existing_args: &[EvalTerm],
  extra_arg: &EvalTerm,
  env: &Env,
  locals: &[EvalTerm],
) -> Result<EvalTerm, EvalError> {
  let mut all_args: Vec<EvalTerm> = existing_args.to_vec();
  all_args.push(extra_arg.clone());
  let arity = env
    .primitives
    .get(p_idx as usize)
    .map(|(_, a)| *a)
    .unwrap_or(0);
  let evaluated: Vec<EvalTerm> = all_args
    .iter()
    .map(|a| eval(a, locals, env))
    .collect::<Result<Vec<_>, _>>()?;
  if arity > 0 && evaluated.len() >= arity {
    exec_prim(p_idx, &evaluated, env)
  } else {
    Ok(EvalTerm::Prim {
      idx: p_idx,
      args: evaluated,
    })
  }
}

fn resolve_const(idx: u64, env: &Env) -> Result<EvalTerm, EvalError> {
  let idx = idx as usize;
  env
    .constants
    .get(idx)
    .cloned()
    .ok_or(EvalError::UnknownConstant(idx))
}

fn extract_float(arg: &EvalTerm) -> Result<f64, EvalError> {
  match arg {
    EvalTerm::Lit {
      l: Literal::Float { value },
    } => Ok(value.0),
    _ => Err(EvalError::PrimCallFailed(format!(
      "expected float literal, got {arg}"
    ))),
  }
}

fn kernel_float_binop(args: &[EvalTerm], op: fn(f64, f64) -> f64) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("float binop needs 2 args".into()));
  }
  let a = extract_float(&args[0])?;
  let b = extract_float(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Float {
      value: FloatValue(op(a, b)),
    },
  })
}

fn kernel_float_cmp(args: &[EvalTerm], op: fn(f64, f64) -> bool) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("float cmp needs 2 args".into()));
  }
  let a = extract_float(&args[0])?;
  let b = extract_float(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Bool {
      v: if op(a, b) { 1 } else { 0 },
    },
  })
}

fn kernel_string_length(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 1 {
    return Err(EvalError::PrimCallFailed(
      "string_length needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  Ok(EvalTerm::Lit {
    l: Literal::Int { v: s.len() as i64 },
  })
}

fn kernel_int_to_string(args: &[EvalTerm], fmt: fn(i64) -> String) -> Result<EvalTerm, EvalError> {
  let v = extract_int(&args[0])?;
  Ok(EvalTerm::Lit {
    l: Literal::Str { value: fmt(v) },
  })
}

fn kernel_float_to_string(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  let v = extract_float(&args[0])?;
  Ok(EvalTerm::Lit {
    l: Literal::Str {
      value: v.to_string(),
    },
  })
}

fn kernel_string_starts_with(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed(
      "string_starts_with needs 2 args".into(),
    ));
  }
  let prefix = extract_string(&args[0])?;
  let s = extract_string(&args[1])?;
  Ok(EvalTerm::Lit {
    l: Literal::Bool {
      v: if s.starts_with(&prefix) { 1 } else { 0 },
    },
  })
}

fn kernel_string_slice(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 3 {
    return Err(EvalError::PrimCallFailed(
      "string_slice needs 3 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let start = extract_int(&args[1])?.max(0) as usize;
  let len = extract_int(&args[2])?.max(0) as usize;
  let end = (start + len).min(s.len());
  let result = if start <= s.len() {
    s[start..end].to_string()
  } else {
    String::new()
  };
  Ok(EvalTerm::Lit {
    l: Literal::Str { value: result },
  })
}

fn kernel_string_drop(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.len() < 2 {
    return Err(EvalError::PrimCallFailed("string_drop needs 2 args".into()));
  }
  let n = extract_int(&args[0])?.max(0) as usize;
  let s = extract_string(&args[1])?;
  let result = if n >= s.len() {
    String::new()
  } else {
    s[n..].to_string()
  };
  Ok(EvalTerm::Lit {
    l: Literal::Str { value: result },
  })
}

fn kernel_print_str(args: &[EvalTerm]) -> Result<EvalTerm, EvalError> {
  if args.is_empty() {
    return Err(EvalError::PrimCallFailed("print_str needs 1 arg".into()));
  }
  let s = extract_string(&args[0])?;
  println!("{s}");
  Ok(EvalTerm::Lit {
    l: Literal::Str { value: s },
  })
}

// --------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_var_construction() {
    let v = var(0);
    assert_eq!(v, EvalTerm::Var { idx: 0 });
    assert_eq!(v.to_string(), "(var 0)");
  }

  #[test]
  fn test_lam_construction() {
    let body = var(0);
    let l = lam(Multiplicity::Many, body);
    assert_eq!(l.to_string(), "(lam ω (var 0))");
  }

  #[test]
  fn test_app_construction() {
    let fun = lam(Multiplicity::Many, var(0));
    let arg = const_(3);
    let a = app(fun, arg);
    assert_eq!(a.to_string(), "(app (lam ω (var 0)) (const #3))");
  }

  #[test]
  fn test_identity_lambda() {
    let id_lam = lam(Multiplicity::Many, var(0));
    let t = app(id_lam, const_(7));
    assert_eq!(t.to_string(), "(app (lam ω (var 0)) (const #7))");
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
    let p = prim(1, vec![const_(0), var(0)]);
    assert_eq!(p.to_string(), "(prim #1 (const #0) (var 0))");
  }

  #[test]
  fn test_recursor_construction() {
    let info = RecursorInfo::new(0, 1, 1, 2);
    let motive = lam(Multiplicity::Many, var(0));
    let none_case = const_(1);
    let some_case = lam(Multiplicity::Many, const_(2));
    let scrutinee = var(0);
    let r = recursor(info, motive, vec![none_case, some_case], scrutinee);
    let s = r.to_string();
    assert!(s.contains("recursor"));
    assert!(s.contains("rec(#0 params=1 motives=1 cases=2)"));
  }

  #[test]
  fn test_region_construction() {
    let body = var(0);
    let r = region(Region::Stack, body);
    assert_eq!(r.to_string(), "(region r_stack (var 0))");
  }

  #[test]
  fn test_borrow_construction() {
    let body = var(0);
    let b = borrow(BorrowKind::Unique, Region::Heap, body);
    assert_eq!(b.to_string(), "(borrow unique r_heap (var 0))");
  }

  #[test]
  fn test_proj_construction() {
    let arg = var(0);
    let p = proj(1, 0, arg);
    assert_eq!(p.to_string(), "(proj .1 struct=#0 (var 0))");
  }

  #[test]
  fn test_proj_field_construction() {
    let base = var(0);
    let pf = proj_field(base, 2);
    assert_eq!(pf.to_string(), "(proj_field .2 (var 0))");
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
    let a = var(0);
    let b = var(0);
    assert_eq!(a, b);

    let a = var(0);
    let b = var(1);
    assert_ne!(a, b);
  }

  #[test]
  fn test_nested_term() {
    let inner = app(lam(Multiplicity::Many, var(0)), const_(5));
    let outer = lam(Multiplicity::Many, inner);
    assert_eq!(
      outer.to_string(),
      "(lam ω (app (lam ω (var 0)) (const #5)))"
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
    let t = var(0);
    let result = subst(&t, 1, &const_(99));
    assert_eq!(result, t);
  }

  #[test]
  fn test_subst_var_equal_index() {
    let t = var(0);
    let r = const_(42);
    let result = subst(&t, 0, &r);
    assert_eq!(result, r);
  }

  #[test]
  fn test_subst_var_greater_than_index() {
    let t = var(2);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, var(1));
  }

  #[test]
  fn test_subst_lam_body() {
    // subst(λ. var(3), 1, const(99))
    // → λ. subst(var(3), 2, shift(const(99), 0, 1))
    // → λ. subst(var(3), 2, const(99))
    // → λ. var(2)  (because 3 > 2, decrement: 3-1=2)
    let body = var(3);
    let lam_term = lam(Multiplicity::Many, body);
    let r = const_(99);
    let result = subst(&lam_term, 1, &r);
    assert_eq!(result, lam(Multiplicity::Many, var(2)));
  }

  #[test]
  fn test_subst_beta_reduction() {
    // (λx. x) 42  →  subst(var(0), 0, 42)  =  42
    let lam_body = var(0);
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
    assert_eq!(result, lam(Multiplicity::Many, var(0)));
  }

  #[test]
  fn test_subst_under_app() {
    // (x y) with x at 0 and y at 1, substitute 0 with const(10)
    let t = app(var(0), var(1));
    let r = const_(10);
    let result = subst(&t, 0, &r);
    assert_eq!(result, app(const_(10), var(0)));
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
    let t = prim(0, vec![var(0), var(1)]);
    let r = const_(99);
    let result = subst(&t, 0, &r);
    assert_eq!(result, prim(0, vec![const_(99), var(0)]));
  }

  // -- shift tests ---------------------------------------------------------

  #[test]
  fn test_shift_var_below_cutoff() {
    let t = var(0);
    let result = shift(&t, 1, 5);
    assert_eq!(result, t);
  }

  #[test]
  fn test_shift_var_above_cutoff() {
    let t = var(3);
    let result = shift(&t, 2, 5);
    assert_eq!(result, var(8));
  }

  #[test]
  fn test_shift_var_at_cutoff() {
    let t = var(2);
    let result = shift(&t, 2, 3);
    assert_eq!(result, var(5));
  }

  #[test]
  fn test_shift_lam() {
    // λ. var(1) with cutoff 0, shift 2
    // cutoff increases inside lam to 1, so var(1) >= 1 → var(3)
    // result: λ. var(3)
    let body = var(1);
    let t = lam(Multiplicity::Many, body);
    let result = shift(&t, 0, 2);
    assert_eq!(result, lam(Multiplicity::Many, var(3)));
  }

  #[test]
  fn test_shift_lam_lift_identity() {
    // Shift the identity function λ. var(0) up by 1
    // λ. var(0): var(0) < cutoff(1) after entering lam, so unchanged
    // result: λ. var(0)
    let id_body = var(0);
    let t = lam(Multiplicity::Many, id_body);
    let result = shift(&t, 0, 1);
    assert_eq!(result, lam(Multiplicity::Many, var(0)));
  }

  // -- whnf tests ----------------------------------------------------------

  #[test]
  fn test_whnf_step_beta() {
    // (λx. x) const(42) → const(42)
    let id_body = var(0);
    let id = lam(Multiplicity::Many, id_body);
    let arg = const_(42);
    let t = app(id, arg);
    let result = whnf_step(&t);
    assert_eq!(result, Some(const_(42)));
  }

  #[test]
  fn test_whnf_step_beta_with_free_var() {
    // (λx. x) var(1) → var(1)
    // β-reduction: subst(var(0), 0, var(1)) → var(1)
    let id_body = var(0);
    let id = lam(Multiplicity::Many, id_body);
    let arg = var(1);
    let t = app(id, arg);
    let result = whnf_step(&t);
    assert_eq!(result, Some(var(1)));
  }

  #[test]
  fn test_whnf_step_nested_app() {
    // ((λx. x) (λy. y)) z → step1: app(λy.y, z) → z
    let id_lam = lam(Multiplicity::Many, var(0));
    let inner_app = app(id_lam.clone(), id_lam);
    let outer_app = app(inner_app, const_(1));
    // First whnf_step: reduces inner_app to id_lam
    let r1 = whnf_step(&outer_app).unwrap();
    // r1 = app(id_lam, const(1), ω)
    let r2 = whnf_step(&r1).unwrap();
    assert_eq!(r2, const_(1));
  }

  #[test]
  fn test_whnf_step_neutral() {
    // const(0) const(1) → no reduction (const is neutral, not a lam)
    let t = app(const_(0), const_(1));
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
    let id_lam = lam(Multiplicity::Many, var(0));
    let t = app(id_lam, const_(7));
    assert_eq!(whnf(&t), const_(7));
  }

  #[test]
  fn test_whnf_nested_beta() {
    // ((λx. λy. x) a) b → a
    let inner_lam = lam(Multiplicity::Many, var(1));
    let outer_lam = lam(Multiplicity::Many, inner_lam);
    let app1 = app(outer_lam, const_(10));
    let app2 = app(app1, const_(20));
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

  // -- eval tests ----------------------------------------------------------

  fn env_with_consts(vals: Vec<EvalTerm>) -> Env {
    let mut env = Env::new();
    for v in vals {
      env.constants.push(v);
    }
    env
  }

  #[test]
  fn test_eval_lit() {
    let env = Env::new();
    let t = lit(Literal::Int { v: 42 });
    assert_eq!(eval(&t, &[], &env).unwrap(), t);
  }

  #[test]
  fn test_eval_sort() {
    let env = Env::new();
    let t = sort(1);
    assert_eq!(eval(&t, &[], &env).unwrap(), t);
  }

  #[test]
  fn test_eval_lam() {
    let env = Env::new();
    let t = lam(Multiplicity::Many, var(0));
    assert_eq!(eval(&t, &[], &env).unwrap(), t);
  }

  #[test]
  fn test_eval_app_beta() {
    let env = Env::new();
    let id = lam(Multiplicity::Many, var(0));
    let t = app(id, const_(0));
    assert_eq!(eval(&t, &[], &env).unwrap(), const_(0));
  }

  #[test]
  fn test_eval_app_chain() {
    let env = env_with_consts(vec![
      lit(Literal::Int { v: 99 }), // const(0) = 99
    ]);
    // (λx. x) const(0) → const(0) → needs env to resolve const(0)
    // Simple: (λx.x)(λy.y) → λy.y
    let id = lam(Multiplicity::Many, var(0));
    let t = app(id, lit(Literal::Int { v: 42 }));
    assert_eq!(eval(&t, &[], &env).unwrap(), lit(Literal::Int { v: 42 }));
  }

  #[test]
  fn test_eval_var_from_locals() {
    let env = Env::new();
    let locals = vec![const_(99), const_(100)];
    assert_eq!(eval(&var(0), &locals, &env).unwrap(), const_(100));
    assert_eq!(eval(&var(1), &locals, &env).unwrap(), const_(99));
  }

  #[test]
  fn test_eval_const_is_value() {
    let env = Env::new();
    // Const is a value — it should evaluate to itself
    assert_eq!(eval(&const_(0), &[], &env).unwrap(), const_(0));
    assert_eq!(eval(&const_(5), &[], &env).unwrap(), const_(5));
  }

  #[test]
  fn test_eval_const_reduced_in_app() {
    // const(0) = λx. x — evaluated only when applied
    let env = env_with_consts(vec![lam(Multiplicity::Many, var(0))]);
    let t = app(const_(0), lit(Literal::Int { v: 7 }));
    assert_eq!(eval(&t, &[], &env).unwrap(), lit(Literal::Int { v: 7 }));
  }

  #[test]
  fn test_eval_unbound_var_is_error() {
    let env = Env::new();
    assert!(eval(&var(0), &[], &env).is_err());
  }

  #[test]
  fn test_eval_irreducible_app() {
    let env = env_with_consts(vec![
      lit(Literal::Int { v: 1 }), // const(0) = 1
    ]);
    let t = app(const_(0), const_(1));
    // const(0) resolves to lit(1), then app(lit(1), const(1)) is irreducible
    let result = eval(&t, &[], &env).unwrap();
    match result {
      EvalTerm::App { fun, arg } => {
        assert_eq!(*fun, lit(Literal::Int { v: 1 }));
        assert_eq!(*arg, const_(1));
      }
      _ => panic!("expected App, got {result}"),
    }
  }

  #[test]
  fn test_eval_recursor_option_none() {
    let mut env = Env::new();
    let info = RecursorInfo::new(0, 1, 1, 2);
    env.recursors.push(("Option.rec".into(), info.clone()));
    // Register const(0) = none, const(1) = some as their own values
    env.constants.push(const_(0)); // const(0) evaluates to itself
    env.constants.push(const_(1)); // const(1) evaluates to itself
    env.constructor_tags.insert(0, vec![(0, 0)]); // const(0) = none constructor, case 0
    env.constructor_tags.insert(1, vec![(0, 1)]); // const(1) = some constructor, case 1

    let motive = lam(Multiplicity::Many, sort(1));
    let none_case = lit(Literal::Int { v: 1 });
    let some_case = lam(Multiplicity::Many, lit(Literal::Int { v: 2 }));
    let t = recursor(info, motive, vec![none_case, some_case], const_(0));
    assert_eq!(eval(&t, &[], &env).unwrap(), lit(Literal::Int { v: 1 }));
  }

  #[test]
  fn test_eval_nested_lam_app() {
    let env = Env::new();
    // (λf. f 5) (λx. x) → (λx. x) 5 → 5
    let inner_app = app(var(0), const_(5));
    let call_f = lam(Multiplicity::Many, inner_app);
    let id = lam(Multiplicity::Many, var(0));
    let t = app(call_f, id);
    assert_eq!(eval(&t, &[], &env).unwrap(), const_(5));
  }

  fn env_with_prims(prims: Vec<(String, usize)>) -> Env {
    let mut env = Env::new();
    env.primitives = prims;
    env
  }

  #[test]
  fn test_eval_print_str() {
    let env = env_with_prims(vec![("print_str".into(), 1)]);
    // We need to prime the const for the string result — but
    // print_str returns a literal, not a const, so this works without
    // consts. The primitive accumulates args and fires print_str.
    let hello = lit(Literal::Str {
      value: "hello".to_string(),
    });
    let t = prim(0, vec![hello.clone()]);
    let result = eval(&t, &[], &env).unwrap();
    assert_eq!(result, hello);
  }

  #[test]
  fn test_eval_prim_insufficient_args_is_value() {
    let env = env_with_prims(vec![("print_str".into(), 1)]);
    let t = prim(0, vec![]);
    let result = eval(&t, &[], &env).unwrap();
    assert!(matches!(result, EvalTerm::Prim { .. }));
  }

  #[test]
  fn test_eval_print_str_app() {
    let env = env_with_prims(vec![("print_str".into(), 1)]);
    // Simulate: App(Prim(print_str), "world") — print_str accumulates arg
    let hello = lit(Literal::Str {
      value: "world".to_string(),
    });
    let t = app(prim(0, vec![]), hello.clone());
    let result = eval(&t, &[], &env).unwrap();
    assert_eq!(result, hello);
  }
}
