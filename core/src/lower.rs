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
  /// Maps prim indices → arity (number of arguments before the native fires).
  prim_arities: Map<u64, usize>,
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
      prim_arities: Map::new(),
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
        if let Some((idx, _)) = self.find_bound(ident) {
          Ok(eval_term::var(idx))
        } else {
          self.lower_free_id(ident, name)
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
        let _mult = self.find_bound_at_index(*i).unwrap_or(Multiplicity::Many);
        Ok(eval_term::var(*i as u64))
      }

      NameRef::Macro(_) => Err(LowerError::Unsupported(
        "macros must be expanded before lowering".into(),
      )),
    }
  }

  fn lower_free_id(&mut self, ident: &Identifier, name: &NameRef) -> Result<EvalTerm, LowerError> {
    let resolved = self
      .scope
      .resolve_name(name)
      .map_err(|_| LowerError::UnresolvedName(format!("free variable: {ident}")))?;
    let path = constructor_fqn(resolved).unwrap_or_else(|| ModulePath::single(ident.clone()));
    let const_idx = self.get_or_create_const(&path);
    Ok(eval_term::const_(const_idx))
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
    Ok(eval_term::app(lowered_fun, lowered_arg))
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

    let inductive = self
      .scope
      .global()
      .find_inductive(&inductive_path)
      .ok_or_else(|| LowerError::UnresolvedName(format!("inductive: {inductive_path}")))?;

    let mut indexed_cases: Vec<(usize, &MatchCase)> = cases
      .iter()
      .map(|c| {
        let cons_idx = inductive
          .constructors()
          .iter()
          .position(|ctor| ctor.name().last() == &c.name)
          .ok_or_else(|| {
            LowerError::UnresolvedName(format!(
              "constructor {} not found in {}",
              c.name,
              inductive_path.to_string()
            ))
          })?;
        Ok((cons_idx, c))
      })
      .collect::<Result<Vec<_>, _>>()?;
    indexed_cases.sort_by_key(|(idx, _)| *idx);

    let lowered_cases: Vec<EvalTerm> = indexed_cases
      .iter()
      .map(|(_, c)| self.lower_match_case(c))
      .collect::<Result<Vec<_>, _>>()?;

    Ok(eval_term::recursor(
      info_with_idx,
      motive,
      lowered_cases,
      lowered_scrutinee,
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

    self.prim_arities.insert(prim_idx, native.num_args);
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
      result = eval_term::app(result, arg);
    }

    Ok(result)
  }

  /// Build an evaluation environment from the lowering context and scope.
  ///
  /// Resolves all const bodies from the scope's def_refs, lowering each
  /// recursively. Primitives are collected by name. Recursor metadata is
  /// copied directly. Constructor tags are built from the scope's inductives.
  pub fn finish(&mut self, scope: &Scope) -> Result<eval_term::Env, LowerError> {
    use std::collections::BTreeSet;

    let n_consts = self.const_indices.len();

    // --- constants --------------------------------------------------------
    // Each const body must be lowered (may in turn reference other consts).
    // We iterate to a fixpoint, processing consts whose bodies haven't been
    // lowered yet.
    let mut constants: Vec<EvalTerm> = vec![eval_term::sort(0); n_consts];
    let mut lowered_mask: Vec<bool> = vec![false; n_consts];

    // Map from module paths that are known to be constructors (NOT defs).
    let constructor_paths: BTreeSet<ModulePath> = {
      let mut s = BTreeSet::new();
      let global = scope.global();
      for inductive in global.inductives() {
        for ctor in &inductive.constructors {
          s.insert(ctor.name().clone());
        }
      }
      s
    };

    loop {
      // Snapshot current const_indices
      let snapshot: Vec<(ModulePath, u64)> = self
        .const_indices
        .iter()
        .map(|(k, v)| (k.clone(), *v))
        .collect();
      let mut work_done = false;

      for (path, idx) in &snapshot {
        let idx = *idx as usize;
        if idx >= constants.len() {
          constants.resize(idx + 1, eval_term::sort(0));
          lowered_mask.resize(idx + 1, false);
        }
        if lowered_mask[idx] {
          continue;
        }

        // Skip constructors — they have no def body
        if constructor_paths.contains(path) {
          lowered_mask[idx] = true;
          constants[idx] = eval_term::const_(idx as u64);
          work_done = true;
          continue;
        }

        // Try to find a def body via scope
        let global = scope.global();
        if let Some(def_ref) = global.find_ref(path) {
          let body = def_ref.term();
          let lowered = self.lower(body)?;
          constants[idx] = lowered;
          lowered_mask[idx] = true;
          work_done = true;
        } else {
          // Not a def, not a constructor — leave as placeholder
          lowered_mask[idx] = true;
          work_done = true;
        }
      }
      if !work_done {
        break;
      }
    }

    // --- primitives (after const loop, which may create new prims) ---------
    let n_prims = self.prim_indices.len();
    let mut primitives = vec![("".to_string(), 0usize); n_prims];
    for (name, idx) in &self.prim_indices {
      let idx_u = *idx as usize;
      if idx_u < primitives.len() {
        let arity = self.prim_arities.get(idx).copied().unwrap_or(0);
        primitives[idx_u] = (name.to_string(), arity);
      }
    }

    // --- recursors --------------------------------------------------------
    let recursors: Vec<(String, RecursorInfo)> = self.recursor_infos.clone();

    // --- constructor_tags -------------------------------------------------
    let mut constructor_tags: Map<u64, Vec<(u64, u64)>> = Map::new();
    {
      let global = scope.global();
      for inductive in global.inductives() {
        if let Some(&rec_idx) = self.recursor_indices.get(inductive.name()) {
          for (case_idx, ctor) in inductive.constructors.iter().enumerate() {
            if let Some(&const_idx) = self.const_indices.get(ctor.name()) {
              constructor_tags
                .entry(const_idx)
                .or_default()
                .push((rec_idx, case_idx as u64));
            }
          }
        }
      }
    }

    Ok(eval_term::Env {
      constants,
      primitives,
      recursors,
      constructor_tags,
    })
  }
}

/// Synthetic motive for simple (non-dependent) matches: `λ_. Sort 1`.
fn synthesize_motive() -> EvalTerm {
  eval_term::lam(Multiplicity::Many, eval_term::sort(1))
}

/// Extract the fully qualified constructor name from a resolved term.
/// Unwraps leading lambdas (for parameterized constructors like `some`).
fn constructor_fqn(term: &Term) -> Option<ModulePath> {
  match term {
    Term::Con(con) => Some(con.typ_name().append(vec![con.name().clone()])),
    Term::Lam { body, .. } => constructor_fqn(body),
    _ => None,
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
  use super::*;
  use crate::eval_term::{self, Literal as ELit};
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
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::var(0));

    let t = Term::Var {
      name: NameRef::Index(3),
    };
    assert_eq!(lower_term(&t, &scope).unwrap(), eval_term::var(3));
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

// ---------------------------------------------------------------------------
// Integration tests (parse → type-check → lower → eval)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod integration_tests {
  use super::*;
  use crate::eval::r#type::type_check;
  use crate::eval_term::{self, Literal as ELit, eval_entry};
  use crate::parser::{ReplInput, repl_parser};
  use crate::term::{
    Hole, ModulePath, app, lam,
    module::{LoadedModules, ParsedModule, Scope, default_modules, module},
    num, param, var,
  };

  fn eval_lowered(term: Term, scope: &Scope) -> Result<eval_term::EvalTerm, String> {
    let typed = type_check(term, Hole, scope).map_err(|e| format!("type check failed: {e}"))?;
    let mut ctx = LowerContext::new(scope);
    let lowered = ctx
      .lower(&typed.term)
      .map_err(|e| format!("lower failed: {e}"))?;
    let env = ctx
      .finish(scope)
      .map_err(|e| format!("env build failed: {e}"))?;
    eval_entry(&lowered, &env).map_err(|e| format!("eval failed: {e}"))
  }

  fn test_scope() -> Scope<'static> {
    let loaded: &'static mut LoadedModules = Box::leak(Box::new(default_modules().unwrap()));
    let path: &'static ModulePath =
      Box::leak(Box::new(ModulePath::new(vec![crate::term::id("'test")])));
    loaded.add_module(module(
      path.clone(),
      ParsedModule {
        decls: vec![],
        module_doc: None,
      },
    ));
    let global: &'static _ = Box::leak(Box::new(loaded.global(path).unwrap()));
    Scope::new(global)
  }

  #[test]
  fn test_integration_lit() {
    let scope = test_scope();

    let result = eval_lowered(num(42), &scope).unwrap();
    assert_eq!(result, eval_term::lit(ELit::Int { v: 42 }));
  }

  #[test]
  fn test_integration_lam_id() {
    let scope = test_scope();

    let term = app(lam(param(crate::term::id("x"), Hole), var("x")), num(42));

    let result = eval_lowered(term, &scope).unwrap();
    assert_eq!(result, eval_term::lit(ELit::Int { v: 42 }));
  }

  #[test]
  fn test_integration_nested_app() {
    let scope = test_scope();

    let const_fun_app = app(
      lam(param(crate::term::id("f"), Hole), app(var("f"), num(99))),
      lam(param(crate::term::id("x"), Hole), var("x")),
    );

    let result = eval_lowered(const_fun_app, &scope).unwrap();
    assert_eq!(result, eval_term::lit(ELit::Int { v: 99 }));
  }

  #[test]
  fn test_integration_lam_chain() {
    let scope = test_scope();

    let k = lam(
      param(crate::term::id("x"), Hole),
      lam(param(crate::term::id("y"), Hole), var("x")),
    );
    let term = app(app(k, num(10)), num(20));

    let result = eval_lowered(term, &scope).unwrap();
    assert_eq!(result, eval_term::lit(ELit::Int { v: 10 }));
  }

  #[test]
  fn test_integration_string_lit() {
    let scope = test_scope();

    let term = crate::term::str("hello");
    let result = eval_lowered(term, &scope).unwrap();
    assert_eq!(
      result,
      eval_term::lit(ELit::Str {
        value: "hello".to_string()
      })
    );
  }

  #[test]
  fn test_integration_arithmetic() {
    let scope = test_scope();

    let input = "1 + 2";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 3 })
    );
  }

  #[test]
  fn test_integration_list_empty_parse() {
    let scope = test_scope();

    let input = "List.empty";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };

    let result = eval_lowered(term, &scope);
    assert!(result.is_ok(), "pipeline error: {:?}", result.err());
  }

  #[test]
  fn test_integration_string_concat() {
    let scope = test_scope();

    let input = r#""hello" ++ " world""#;
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };

    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Str {
        value: "hello world".to_string()
      })
    );
  }

  #[test]
  fn test_integration_if_true() {
    let scope = test_scope();

    let input = "if true then 42 else 0";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 42 })
    );
  }

  #[test]
  fn test_integration_if_false() {
    let scope = test_scope();

    let input = "if false then 42 else 0";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 0 })
    );
  }

  #[test]
  fn test_integration_if_nested() {
    let scope = test_scope();

    let input = "if (if true then false else true) then 1 else 2";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 2 })
    );
  }

  #[test]
  fn test_integration_bool_not() {
    let scope = test_scope();

    let input = "Bool.not true";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };

    let result = eval_lowered(term, &scope);
    assert!(result.is_ok(), "pipeline error: {:?}", result.err());
    // Bool.not true → false (constructor const — opaque value)
    assert!(
      matches!(&result, Ok(eval_term::EvalTerm::Const { .. })),
      "expected constructor const, got {result:?}"
    );
  }

  #[test]
  fn test_integration_bool_eq() {
    let scope = test_scope();

    let input = "5 == 5";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Bool { v: 1 })
    );
  }

  #[test]
  fn test_integration_if_arithmetic_cmp() {
    let scope = test_scope();

    let input = "if (5 == 5) then 100 else 0";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 100 })
    );

    let scope = test_scope();
    let input = "if (5 == 3) then 100 else 0";
    let ReplInput::Term(term) = repl_parser(input).unwrap() else {
      panic!("expected term")
    };
    assert_eq!(
      eval_lowered(term, &scope).unwrap(),
      eval_term::lit(ELit::Int { v: 0 })
    );
  }
}
