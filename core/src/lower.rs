use crate::Map;
/// Lowering pass: TypeTerm (crate::term::Term) → EvalTerm (crate::eval_term::EvalTerm).
///
/// Runs after type checking, before evaluation. Performs:
///   1. Name resolution → de Bruijn indices or const/prim/recursor indices
///   2. Match/If → recursor compilation
///   3. Multiplicity propagation from the type checker's Pi annotations
///   4. Region inference (stack for linear, heap for many)
///   5. Erasure of type-level constructs (Forall, Pi)
///
/// See: plans/implementations/two-term-kernel.md
use crate::eval_term::{self, EvalTerm, Literal as ELiteral, Multiplicity, RecursorInfo};
use crate::term::module::Scope;
use crate::term::{
  Constructor, Identifier, Literal, MatchCase, ModulePath, NameRef, Named, Native, Par, Term,
};
use std::fmt::Display;

#[derive(Debug, Clone)]
pub enum LowerError {
  UnresolvedName(String),
  Unsupported(String),
  UnexpectedHole,
  NotAConstructor(ModulePath),
}

impl Display for LowerError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LowerError::UnresolvedName(name) => write!(f, "unresolved name: {name}"),
      LowerError::Unsupported(msg) => write!(f, "unsupported: {msg}"),
      LowerError::UnexpectedHole => write!(f, "unexpected hole during lowering"),
      LowerError::NotAConstructor(path) => write!(f, "not a constructor: {path}"),
    }
  }
}

// ---------------------------------------------------------------------------
// LowerContext — state tracked during lowering
// ---------------------------------------------------------------------------

pub struct LowerContext<'a> {
  scope: &'a Scope<'a>,
  /// De Bruijn level stack: (name, multiplicity). Most recent at the end.
  bound_vars: Vec<(Identifier, Multiplicity)>,
  /// Maps global paths → const indices (assign on first encounter).
  const_indices: Map<ModulePath, u64>,
  /// Maps native names → prim indices.
  prim_indices: Map<Identifier, u64>,
  /// Maps inductive type paths → recursor indices.
  recursor_indices: Map<ModulePath, u64>,
  /// Recursor metadata: (name, RecursorInfo) for each index.
  recursor_infos: Vec<(String, RecursorInfo)>,
}

impl<'a> LowerContext<'a> {
  pub fn new(scope: &'a Scope<'a>) -> Self {
    LowerContext {
      scope,
      bound_vars: Vec::new(),
      const_indices: Map::new(),
      prim_indices: Map::new(),
      recursor_indices: Map::new(),
      recursor_infos: Vec::new(),
    }
  }

  fn push(&mut self, name: Identifier, mult: Multiplicity) {
    self.bound_vars.push((name, mult));
  }

  fn pop(&mut self) {
    self.bound_vars.pop();
  }

  fn find_bound(&self, name: &Identifier) -> Option<(u64, Multiplicity)> {
    for (i, (n, mult)) in self.bound_vars.iter().enumerate().rev() {
      if n == name {
        let idx = (self.bound_vars.len() - 1 - i) as u64;
        return Some((idx, *mult));
      }
    }
    None
  }

  fn get_or_create_const(&mut self, path: &ModulePath) -> u64 {
    if let Some(&idx) = self.const_indices.get(path) {
      idx
    } else {
      let idx = self.const_indices.len() as u64;
      self.const_indices.insert(path.clone(), idx);
      idx
    }
  }

  fn get_or_create_prim(&mut self, name: &Identifier) -> u64 {
    if let Some(&idx) = self.prim_indices.get(name) {
      idx
    } else {
      let idx = self.prim_indices.len() as u64;
      self.prim_indices.insert(name.clone(), idx);
      idx
    }
  }

  fn get_or_create_recursor(&mut self, inductive_path: &ModulePath, info: RecursorInfo) -> u64 {
    if let Some(&idx) = self.recursor_indices.get(inductive_path) {
      idx
    } else {
      let idx = self.recursor_indices.len() as u64;
      self.recursor_indices.insert(inductive_path.clone(), idx);
      self.recursor_infos.push((inductive_path.to_string(), info));
      idx
    }
  }

  fn multiplicity_for_param(&self, param: &Par) -> Multiplicity {
    match param {
      Par::P(p) => eval_multiplicity(&p.mult),
      Par::I { mult, .. } => eval_multiplicity(mult),
    }
  }
}

/// Map crate::term::Multiplicity → crate::eval_term::Multiplicity.
fn eval_multiplicity(m: &crate::term::Multiplicity) -> Multiplicity {
  match m {
    crate::term::Multiplicity::Zero => Multiplicity::Zero,
    crate::term::Multiplicity::Many => Multiplicity::Many,
    crate::term::Multiplicity::Linear => Multiplicity::Linear,
    crate::term::Multiplicity::Affine => Multiplicity::Affine,
  }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn lower_term(term: &Term, scope: &Scope) -> Result<EvalTerm, LowerError> {
  let mut ctx = LowerContext::new(scope);
  ctx.lower(term)
}

// ---------------------------------------------------------------------------
// Lowering dispatch
// ---------------------------------------------------------------------------

impl<'a> LowerContext<'a> {
  fn lower(&mut self, term: &Term) -> Result<EvalTerm, LowerError> {
    match term {
      Term::Var { name } => self.lower_var(name),
      Term::Lam { param, body } => self.lower_lam(param, body),
      Term::App { fun, arg } => self.lower_app(fun, arg),
      Term::Ann { term, .. } => self.lower(term),
      Term::Lit { value } => self.lower_lit(value),
      Term::Ntv { native } => self.lower_ntv(native),
      Term::Con(con) => self.lower_con(con),
      Term::Ctx { term, .. } => self.lower(term),
      Term::Sort { level } => Ok(eval_term::sort(*level)),
      Term::Forall { body, .. } => self.lower(body),
      Term::Pi { .. } => Ok(eval_term::sort(1)),
      Term::Hole => Err(LowerError::UnexpectedHole),
      Term::Quote { .. } => Err(LowerError::Unsupported("Quote".into())),
    }
  }

  // -- Var lowering -------------------------------------------------------

  fn lower_var(&mut self, name: &NameRef) -> Result<EvalTerm, LowerError> {
    match name {
      NameRef::Id(ident) => {
        if let Some((idx, mult)) = self.find_bound(ident) {
          Ok(eval_term::var(idx, mult))
        } else {
          Err(LowerError::UnresolvedName(format!(
            "free variable: {ident}"
          )))
        }
      }

      NameRef::P(path) => {
        let const_idx = self.get_or_create_const(path);
        Ok(eval_term::const_(const_idx))
      }

      NameRef::Op(op) => {
        let infix = self
          .scope
          .global()
          .find_infix(op)
          .map_err(|e| LowerError::UnresolvedName(format!("{e}")))?;
        let path = infix.name().clone();
        let const_idx = self.get_or_create_const(&path);
        Ok(eval_term::const_(const_idx))
      }

      NameRef::Index(i) => {
        let mult = self.find_bound_at_index(*i).unwrap_or(Multiplicity::Many);
        Ok(eval_term::var(*i as u64, mult))
      }

      NameRef::Macro(_) => Err(LowerError::Unsupported(
        "macros must be expanded before lowering".into(),
      )),
    }
  }

  fn find_bound_at_index(&self, idx: usize) -> Option<Multiplicity> {
    let target = self.bound_vars.len().checked_sub(1)?;
    let target = target.checked_sub(idx)?;
    self.bound_vars.get(target).map(|(_, m)| *m)
  }

  // -- Lam lowering -------------------------------------------------------

  fn lower_lam(&mut self, param: &Par, body: &Term) -> Result<EvalTerm, LowerError> {
    let mult = self.multiplicity_for_param(param);

    let name = match param {
      Par::P(p) => p.name.clone(),
      Par::I { .. } => return self.lower(body),
    };

    self.push(name, mult);
    let lowered = self.lower(body)?;
    self.pop();

    Ok(eval_term::lam(mult, lowered))
  }

  // -- App lowering -------------------------------------------------------

  fn lower_app(&mut self, fun: &Term, arg: &Term) -> Result<EvalTerm, LowerError> {
    let lowered_fun = self.lower(fun)?;
    let lowered_arg = self.lower(arg)?;
    let mult = Multiplicity::Many;
    Ok(eval_term::app(lowered_fun, lowered_arg, mult))
  }

  // -- Literal lowering ---------------------------------------------------

  fn lower_lit(&mut self, value: &Literal) -> Result<EvalTerm, LowerError> {
    match value {
      Literal::Str { value } => Ok(eval_term::lit(ELiteral::Str {
        value: value.clone(),
      })),
      Literal::Num { value, .. } => Ok(eval_term::lit(ELiteral::Int { v: *value })),
      Literal::Float { value, .. } => Ok(eval_term::lit(ELiteral::Float {
        value: eval_term::FloatValue(value.0),
      })),
      Literal::Match { value, cases } => self.lower_match(value, cases),
      Literal::If { value, then, els } => {
        let then_name = crate::term::id("true");
        let else_name = crate::term::id("false");
        let match_cases = vec![
          MatchCase {
            name: then_name,
            args: vec![],
            value: then.clone(),
          },
          MatchCase {
            name: else_name,
            args: vec![],
            value: els.clone(),
          },
        ];
        let match_term = crate::term::match_term(value.as_ref().clone(), match_cases);
        self.lower(&match_term)
      }
      Literal::StructLit { .. } => Err(LowerError::Unsupported(
        "struct literals must be desugared before lowering".into(),
      )),
      Literal::StructUpdate { .. } => Err(LowerError::Unsupported(
        "struct updates must be desugared before lowering".into(),
      )),
      Literal::Term(inner) => self.lower(inner),
    }
  }

  // -- Match → Recursor compilation --------------------------------------

  fn lower_match(&mut self, scrutinee: &Term, cases: &[MatchCase]) -> Result<EvalTerm, LowerError> {
    let lowered_scrutinee = self.lower(scrutinee)?;

    let inductive_path = self.infer_inductive_path(cases)?;

    let info = self.build_recursor_info(&inductive_path, cases)?;
    let rec_idx = self.get_or_create_recursor(&inductive_path, info.clone());

    let info_with_idx =
      RecursorInfo::new(rec_idx, info.params_len, info.motives_len, info.cases_len);

    let motive = synthesize_motive();

    let lowered_cases: Vec<EvalTerm> = cases
      .iter()
      .map(|c| self.lower_match_case(c))
      .collect::<Result<Vec<_>, _>>()?;

    Ok(eval_term::recursor(
      info_with_idx,
      motive,
      lowered_cases,
      lowered_scrutinee,
      Multiplicity::Many,
    ))
  }

  fn infer_inductive_path(&self, cases: &[MatchCase]) -> Result<ModulePath, LowerError> {
    for case in cases {
      let name = &case.name;
      let inductives = self.scope.global().inductives();
      for inductive in inductives {
        if inductive.find_cons(name).is_some() {
          return Ok(inductive.name().clone());
        }
      }
    }
    Err(LowerError::Unsupported(
      "match with no recognized constructor patterns".into(),
    ))
  }

  fn build_recursor_info(
    &self,
    inductive_path: &ModulePath,
    _cases: &[MatchCase],
  ) -> Result<RecursorInfo, LowerError> {
    let inductive = self
      .scope
      .global()
      .find_inductive(inductive_path)
      .ok_or_else(|| LowerError::UnresolvedName(format!("inductive: {inductive_path}")))?;

    let num_constructors = inductive.constructors().len();
    let num_type_params = inductive.params().len();

    Ok(RecursorInfo::new(
      0,
      num_type_params as u64,
      1,
      num_constructors as u64,
    ))
  }

  fn lower_match_case(&mut self, case: &MatchCase) -> Result<EvalTerm, LowerError> {
    for name in &case.args {
      self.push(name.clone(), Multiplicity::Many);
    }

    let lowered_body = self.lower(&case.value)?;

    for _ in 0..case.args.len() {
      self.pop();
    }

    let mut result = lowered_body;
    for _ in 0..case.args.len() {
      result = eval_term::lam(Multiplicity::Many, result);
    }

    Ok(result)
  }

  // -- Native lowering ----------------------------------------------------

  fn lower_ntv(&mut self, native: &Native) -> Result<EvalTerm, LowerError> {
    let prim_idx = self.get_or_create_prim(&native.native_name);
    let lowered_args: Vec<EvalTerm> = native
      .args()
      .iter()
      .filter_map(|opt| opt.as_ref())
      .map(|arg| self.lower(arg))
      .collect::<Result<Vec<_>, _>>()?;

    Ok(eval_term::prim(prim_idx, lowered_args))
  }

  // -- Constructor lowering -----------------------------------------------

  fn lower_con(&mut self, con: &Constructor) -> Result<EvalTerm, LowerError> {
    let path = con.typ_name().append(vec![con.name().clone()]);
    let const_idx = self.get_or_create_const(&path);

    let lowered_args: Vec<EvalTerm> = con
      .args()
      .iter()
      .filter_map(|opt| opt.as_ref())
      .map(|arg| self.lower(arg))
      .collect::<Result<Vec<_>, _>>()?;

    let mut result: EvalTerm = eval_term::const_(const_idx);
    for arg in lowered_args {
      result = eval_term::app(result, arg, Multiplicity::Many);
    }

    Ok(result)
  }
}

/// Synthetic motive for simple (non-dependent) matches: `λ_. Sort 1`.
fn synthesize_motive() -> EvalTerm {
  eval_term::lam(Multiplicity::Many, eval_term::sort(1))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use crate::eval_term::{self, Literal as ELit, Multiplicity as EMult};
  use crate::term::{
    Literal as TLit, ModulePath, NameRef, NumSuffix, Term,
    module::{LoadedModules, ParsedModule, module},
  };

  fn empty_loaded() -> LoadedModules {
    let mut loaded = LoadedModules::empty();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    loaded.add_module(module(
      path,
      ParsedModule {
        decls: vec![],
        module_doc: None,
      },
    ));
    loaded
  }

  #[test]
  fn test_lower_sort() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Sort { level: 0 };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(0));

    let t = Term::Sort { level: 1 };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(1));
  }

  #[test]
  fn test_lower_var_de_bruijn() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Var {
      name: NameRef::Index(0),
    };
    assert_eq!(
      lower_term(&t, &scope).unwrap(),
      eval_term::var(0, EMult::Many)
    );

    let t = Term::Var {
      name: NameRef::Index(3),
    };
    assert_eq!(
      lower_term(&t, &scope).unwrap(),
      eval_term::var(3, EMult::Many)
    );
  }

  #[test]
  fn test_lower_lit_num() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Lit {
      value: TLit::Num {
        value: 42,
        suffix: NumSuffix::I64,
      },
    };
    assert_eq!(
      lower_term(&t, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 42 })
    );
  }

  #[test]
  fn test_lower_lit_str() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Lit {
      value: TLit::Str {
        value: "hello".into(),
      },
    };
    assert_eq!(
      lower_term(&t, &scope).unwrap(),
      eval_term::lit(ELit::Str {
        value: "hello".into()
      })
    );
  }

  #[test]
  fn test_lower_lit_float() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Lit {
      value: TLit::Float {
        value: crate::term::F64Wrap(3.14),
        suffix: NumSuffix::F64,
      },
    };
    assert_eq!(
      lower_term(&t, &scope).unwrap(),
      eval_term::lit(ELit::Float {
        value: eval_term::FloatValue(3.14)
      })
    );
  }

  #[test]
  fn test_lower_ann_erased() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let inner = Term::Sort { level: 0 };
    let t = Term::Ann {
      term: Box::new(inner),
      typ: Box::new(Term::Sort { level: 1 }),
    };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(0));
  }

  #[test]
  fn test_lower_ctx_unwrapped() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let inner = Term::Sort { level: 2 };
    let t = Term::Ctx {
      loc: Default::default(),
      term: Box::new(inner),
    };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(2));
  }

  #[test]
  fn test_lower_forall_erased() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let body = Term::Sort { level: 1 };
    let t = Term::Forall {
      name: crate::term::id("A"),
      typ: Box::new(Term::Sort { level: 1 }),
      body: Box::new(body),
    };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(1));
  }

  #[test]
  fn test_lower_pi_sorts() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Pi {
      arg_name: None,
      arg: Box::new(Term::Sort { level: 1 }),
      ret: Box::new(Term::Sort { level: 1 }),
      mult: crate::term::Multiplicity::Many,
    };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::sort(1));
  }

  #[test]
  fn test_lower_hole_errors() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    assert!(lower_term(&Term::Hole, &scope).is_err());
  }

  #[test]
  fn test_lower_quote_errors() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Quote {
      term: Box::new(Term::Sort { level: 0 }),
    };
    assert!(lower_term(&t, &scope).is_err());
  }

  #[test]
  fn test_lower_free_var_errors() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Var {
      name: NameRef::Id(crate::term::id("x")),
    };
    assert!(lower_term(&t, &scope).is_err());
  }

  #[test]
  fn test_lower_struct_lit_errors() {
    let loaded = empty_loaded();
    let path = ModulePath::new(vec![crate::term::id("'test")]);
    let scopes = loaded.scopes();
    let global = scopes.global(&path).unwrap();
    let scope = Scope::new(&global);

    let t = Term::Lit {
      value: TLit::StructLit {
        fields: crate::Map::new(),
      },
    };
    assert!(lower_term(&t, &scope).is_err());
  }
}
