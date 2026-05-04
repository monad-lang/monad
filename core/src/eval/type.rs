use std::fmt::Display;

use crate::{
  Map, Set, empty_set, set_of,
  term::{
    Ann, ClassDefRef, Decl, Def, Identifier, Inductive, InductiveVariant, Instance, InstanceKey,
    Literal, ModulePath, Multiplicity, NameRef, Named, NumSuffix, SourceContext,
    Term::{Forall, Hole, Pi},
    TypeConstraint, Typed, TypedTerm, VarRef, app, bvar, ctx, forall, lam_par,
    module::{LoadedModules, names_of_decls},
    mpvar, num_suffix, param, pi, pi_typs, type_u, type0, typed_term, var,
  },
  vec_fmt,
};

use super::*;

use crate::term::module::Scope;

fn is_known_type_name(name: &ModulePath, scope: &Scope) -> bool {
  scope.find_inductive(name).is_ok()
    || scope.global().find_ref(name).is_some()
    || scope.global().find_class_def(name).is_some()
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
  MismatchingBranches(Term, Term),
  ConstructorMismatch {
    params: Vec<Param>,
    args: Vec<Identifier>,
  },
  InductiveMismatch {
    name: ModulePath,
    params: Vec<Param>,
    args: Vec<Term>,
  },
  ConstructorUnknown(Identifier),
  Scope(ScopeError),
  ExpectedInductive(Term),
  ExpectedPi(Term),
  ExpectedType(Term),
  Context {
    name: Option<ModulePath>,
    loc: SourceRange,
    err: Box<TypeError>,
  },
  InstanceDecl(String),
  Instance(InstanceError),
  MissingField(Identifier),
  Generic(String),
  ArgumentMismatch {
    expected: Term,
    actual: Term,
  },
  TypeMismatch {
    expected: Term,
    actual: Term,
  },
  FreeVarMismatch {
    name: NameRef,
    expected: Term,
    actual: Term,
    locals: Map<Identifier, Term>,
  },
  Overflow {
    value: i64,
    target: &'static str,
  },
  Many(Vec<TypeError>),
  // Linear type errors
  LinearUsedMultipleTimes(Identifier),
  LinearUnused(Identifier),
  AffineUsedMultipleTimes(Identifier),
}

impl From<ScopeError> for TypeError {
  fn from(value: ScopeError) -> Self {
    Self::Scope(value)
  }
}

impl Display for TypeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TypeError::MismatchingBranches(t1, t2) => write!(f, "Mismatching branches {t1} != {t2}"),
      TypeError::Scope(scope_error) => write!(f, "{scope_error}"),
      TypeError::ExpectedPi(s) => write!(f, "Expected function type found: {}", s),
      TypeError::Context { loc, err, name } => {
        write!(f, "{} at {}:{}", err, loc.start.line, loc.start.line_offset)?;
        if let Some(name) = name {
          write!(f, " in {name}")?;
        }
        Ok(())
      }
      TypeError::InstanceDecl(i) => write!(f, "{}", i),
      TypeError::Generic(s) => write!(f, "{}", s),
      TypeError::Many(type_errors) => {
        for (i, t) in type_errors.iter().enumerate() {
          writeln!(f, "{}. {}", i + 1, t)?;
        }
        Ok(())
      }
      TypeError::ConstructorMismatch { params, args } => {
        write!(
          f,
          "Constructor mismatch {} != {}",
          vec_fmt(params),
          vec_fmt(args)
        )
      }
      TypeError::ExpectedType(e) => write!(f, "Expected Type found {e}"),
      TypeError::FreeVarMismatch {
        name,
        expected,
        actual,
        locals,
      } => write!(
        f,
        "Variable mismatch, expected {name} to be {expected} found {actual} with local vars [{}]",
        locals
          .iter()
          .map(|(name, typ)| format!("{name} : {typ}"))
          .collect::<Vec<_>>()
          .join(", ")
      ),
      TypeError::TypeMismatch { expected, actual } => {
        write!(f, "Type mismatch, expected {expected} found {actual}")
      }
      TypeError::MissingField(identifier) => write!(f, "Missing field {identifier}"),
      TypeError::ArgumentMismatch { expected, actual } => {
        write!(f, "Argument mismatch, expected {expected} found {actual}")
      }
      TypeError::Instance(instance_error) => write!(f, "instance {instance_error}"),
      TypeError::InductiveMismatch { name, params, args } => write!(
        f,
        "Inductive {name} params mismatch {} != {}",
        vec_fmt(params),
        vec_fmt(args)
      ),
      TypeError::ConstructorUnknown(identifier) => write!(f, "Unknown constructor {identifier}"),
      TypeError::ExpectedInductive(term) => write!(f, "Expected inductive found {term}"),
      TypeError::Overflow { value, target } => {
        write!(f, "Integer overflow: {value} does not fit in {target}")
      }
      TypeError::LinearUsedMultipleTimes(id) => {
        write!(f, "Linear variable '{}' used more than once", id)
      }
      TypeError::LinearUnused(id) => {
        write!(f, "Linear variable '{}' must be used exactly once", id)
      }
      TypeError::AffineUsedMultipleTimes(id) => {
        write!(f, "Affine variable '{}' used more than once", id)
      }
    }
  }
}

fn generic_terr(s: String) -> TypeError {
  TypeError::Generic(s)
}

fn t_context(err: TypeError, name: Option<ModulePath>, loc: SourceRange) -> TypeError {
  TypeError::Context {
    loc,
    err: Box::new(err),
    name,
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum InstanceError {
  MissingTypeArgs(Vec<Identifier>),
  MissingImplementation(Identifier),
  Generic(String),
}

impl Display for InstanceError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      InstanceError::MissingTypeArgs(identifiers) => {
        write!(f, "missing type args {}", vec_fmt(identifiers))
      }
      InstanceError::MissingImplementation(identifier) => {
        write!(f, "missing implementation of {identifier}")
      }
      InstanceError::Generic(s) => write!(f, "{s}"),
    }
  }
}

impl From<InstanceError> for TypeError {
  fn from(value: InstanceError) -> Self {
    TypeError::Instance(value)
  }
}

/// Tracks variable usage counts for linear type checking (compile-time only)
#[derive(Debug, Clone)]
pub struct UsageEnv {
  usages: Map<Identifier, (Multiplicity, usize)>,
}

impl UsageEnv {
  pub fn new() -> Self {
    UsageEnv { usages: Map::new() }
  }

  /// Register a new variable with its multiplicity
  pub fn register(&mut self, name: Identifier, mult: Multiplicity) {
    self.usages.insert(name, (mult, 0));
  }

  /// Check if a variable can be used (based on its multiplicity)
  pub fn check_usage(&self, name: &Identifier) -> Result<(), TypeError> {
    if let Some((mult, count)) = self.usages.get(name) {
      match mult {
        Multiplicity::Linear => {
          if *count >= 1 {
            return Err(TypeError::LinearUsedMultipleTimes(name.clone()));
          }
        }
        Multiplicity::Affine => {
          if *count >= 1 {
            return Err(TypeError::AffineUsedMultipleTimes(name.clone()));
          }
        }
        Multiplicity::Many => {
          // Always ok
        }
      }
    }
    Ok(())
  }

  /// Mark a variable as used (increment usage count)
  pub fn mark_used(&mut self, name: &Identifier) {
    if let Some((_, count)) = self.usages.get_mut(name) {
      *count += 1;
    }
  }

  /// Verify all linear variables were used exactly once
  pub fn verify_linear_usage(&self) -> Result<(), TypeError> {
    for (name, (mult, count)) in &self.usages {
      if *mult == Multiplicity::Linear && *count != 1 {
        return Err(TypeError::LinearUnused(name.clone()));
      }
    }
    Ok(())
  }
}

pub fn derive_instance_key(class_def: &ClassDefRef, typ: &Term) -> Result<InstanceKey, TypeError> {
  use FreeVar::*;
  use InstanceError::*;
  let free_vars: FreeVars = class_def
    .class
    .params
    .iter()
    .map(|p| (&p.name, Unknown { typ: &p.typ }))
    .collect();
  let param_names: Set<Identifier> = free_vars.names();
  let type_args = match_determine_type_vars(class_def.typ(), typ, free_vars)?;
  let (args, errs) = join_many_results(
    param_names
      .into_iter()
      .map(|name| {
        if let Some(Detected { typ: _, term }) = type_args.get_free_var(&name) {
          Ok(param(name, (*term).clone()))
        } else {
          Err(name)
        }
      })
      .collect::<Vec<Result<Param, Identifier>>>(),
  );
  if !errs.is_empty() {
    Err(MissingTypeArgs(errs))?;
  }

  let key = InstanceKey::new(
    class_def.class.name().clone(),
    class_def.class.constraints.clone(),
    args,
  );
  Ok(key)
}

pub fn type_check_inductive(inductive: Inductive, _scope: &Scope) -> Result<Inductive, TypeError> {
  for _cons in inductive.constructors.iter() {
    //
  }

  Ok(inductive)
}
pub fn type_check_instance<'a>(
  mut instance: Instance,
  class: &'a Inductive,
  scope: &Scope<'a>,
) -> Result<Instance, TypeError> {
  use InstanceError::*;
  if &instance.class_name != class.name() {
    Err(Generic("wrong class name".into()))?;
  }

  // Collect type variables from constraints and instance args FIRST
  let mut type_vars: crate::Map<Identifier, Term> = crate::Map::new();
  let default_type = Term::Type { universe: 0 };
  for constraint in &instance.constraints {
    for var in constraint.vars() {
      type_vars.insert(var.clone(), default_type.clone());
    }
  }
  for arg in &instance.args {
    if let Term::Var { name } = arg {
      if let Some(id) = name.as_id() {
        let path = id.clone().to_path();
        if !is_known_type_name(&path, scope) {
          type_vars.entry(id.clone()).or_insert(default_type.clone());
        }
      }
    }
  }

  // Also collect free type variables from class constructor param types
  let cons = class
    .constructors
    .first()
    .expect("Class needs to have at least one constructor");
  for param in &cons.params {
    let param_typ = param.typ();
    for fv in free_vars(param_typ, &empty_set()) {
      let path = fv.clone().to_path();
      if !is_known_type_name(&path, scope) {
        type_vars.entry(fv).or_insert(default_type.clone());
      }
    }
  }

  // Add type variables to scope BEFORE type checking args
  let mut scope = scope.clone();
  for (var, typ) in &type_vars {
    scope = scope.with_forall(var, typ);
  }

  let mut usage = UsageEnv::new();
  for (param, arg) in class.params.iter().zip(instance.args.iter()) {
    type_check_with_env(arg.clone(), *param.typ.clone(), &scope, &mut usage, true)?;
  }

  let cons = class
    .constructors
    .first()
    .expect("Class needs to have at least one constructor");
  let class_defs = cons.params.iter();
  for param in class_defs {
    if let Some(impl_def) = instance.impls_map.get_mut(&param.name) {
      let class_def_type = param.typ();
      let typ = match_resolve_type(class_def_type, &impl_def.typ, &scope)?;
      let (term, _) =
        type_check_with_env(impl_def.term.clone(), typ.clone(), &scope, &mut usage, true)?
          .to_tuple();
      impl_def.term = term;
      // Wrap type with forall bindings for type variables
      impl_def.typ = wrap_with_foralls(typ, &type_vars);
    } else {
      Err(MissingImplementation(param.name.clone()))?;
    }
  }
  Ok(instance)
}

/// Wrap a type with forall bindings for the given type variables.
fn wrap_with_foralls(typ: Term, vars: &crate::Map<Identifier, Term>) -> Term {
  use crate::term::Term::Forall;
  let mut result = typ;
  for (name, param_typ) in vars {
    result = Forall {
      name: name.clone(),
      typ: Box::new(param_typ.clone()),
      body: Box::new(result),
    };
  }
  result
}

pub fn join_many_results<T, E>(list: Vec<Result<T, E>>) -> (Vec<T>, Vec<E>) {
  let mut oks = Vec::new();
  let mut errs = Vec::new();
  for r in list {
    match r {
      Ok(o) => oks.push(o),
      Err(e) => errs.push(e),
    }
  }
  (oks, errs)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FreeVar<'a> {
  Unknown { typ: &'a Term },
  Detected { typ: &'a Term, term: &'a Term },
}

impl<'a> Display for FreeVar<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      FreeVar::Unknown { typ } => write!(f, "unknown {typ}"),
      FreeVar::Detected { typ, term } => write!(f, "detected {typ} => {term}"),
    }
  }
}

impl<'a> From<&'a (Term, Option<Term>)> for FreeVar<'a> {
  fn from((typ, value): &'a (Term, Option<Term>)) -> Self {
    use FreeVar::*;
    match value {
      Some(term) => Detected { typ, term },
      None => Unknown { typ },
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FreeVars<'a> {
  vars: Map<&'a Identifier, FreeVar<'a>>,
  keep_vars: Map<&'a Identifier, &'a Term>,
}

impl<'a> Display for FreeVars<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let vars = self
      .vars
      .iter()
      .map(|(n, f)| format!("{n} => ({f})"))
      .collect::<Vec<_>>()
      .join(", ");
    let keep = self
      .keep_vars
      .iter()
      .map(|(n, v)| format!("{n} => ({v})"))
      .collect::<Vec<_>>()
      .join(", ");
    write!(f, "vars=[{vars}] keep=[{keep}]")
  }
}

impl<'a> FromIterator<(&'a Identifier, FreeVar<'a>)> for FreeVars<'a> {
  fn from_iter<T: IntoIterator<Item = (&'a Identifier, FreeVar<'a>)>>(iter: T) -> Self {
    let map = iter.into_iter().collect();
    FreeVars {
      vars: map,
      keep_vars: Map::new(),
    }
  }
}

impl<'a> Default for FreeVars<'a> {
  fn default() -> Self {
    Self::new()
  }
}

impl<'a> FreeVars<'a> {
  pub fn new() -> Self {
    Self {
      vars: Map::new(),
      keep_vars: Map::new(),
    }
  }
  pub fn from_locals(scope: &'a Scope<'a>) -> FreeVars<'a> {
    let keep_vars = scope
      .local_foralls()
      .into_iter()
      .map(|(i, local)| (i, local.typ()))
      .collect();
    FreeVars {
      vars: Map::new(),
      keep_vars,
    }
  }
  pub fn get_free_var(&self, name: &Identifier) -> Option<&FreeVar<'a>> {
    self.vars.get(name)
  }

  fn insert_free_var(&mut self, name: &'a Identifier, var: FreeVar<'a>) {
    self.vars.insert(name, var);
  }
  fn add_var_to_keep(&mut self, name: &'a Identifier, typ: &'a Term) {
    self.keep_vars.insert(name, typ);
  }

  fn names(&self) -> Set<Identifier> {
    self.vars.keys().map(|&k| k.clone()).collect()
  }

  pub fn keep_vars(&self) -> &Map<&Identifier, &Term> {
    &self.keep_vars
  }

  pub fn free_vars(&self) -> &Map<&Identifier, FreeVar<'_>> {
    &self.vars
  }

  fn contains_name_ref(&self, nref: &NameRef) -> bool {
    if nref.is_id() {
      let id = nref.as_id().unwrap();
      self.vars.contains_key(id)
    } else {
      false
    }
  }
}

/// Match left with right and resolve the type
pub fn match_resolve_type<'a>(
  left: &'a Term,
  right: &'a Term,
  scope: &Scope<'a>,
) -> Result<Term, TypeError> {
  if !right.is_known() {
    return Ok(left.clone());
  }
  if let Var { name } = right
    && name.is_id()
  {
    return Ok(left.clone());
  }
  let free_vars = FreeVars::from_locals(scope);
  let free_vars = match_determine_type_vars(left, right, free_vars)?;
  let typ = apply_free_type_vars(left.clone(), &free_vars);
  Ok(typ)
}

pub fn match_determine_type_vars<'a>(
  left: &'a Term,
  right: &'a Term,
  mut free_vars: FreeVars<'a>,
) -> Result<FreeVars<'a>, TypeError> {
  let similar = match_resolve_type_inner(left, right, &mut free_vars);
  if similar {
    Ok(free_vars)
  } else {
    Err(TypeError::TypeMismatch {
      expected: left.clone(),
      actual: right.clone(),
    })
  }
}

fn apply_free_type_vars(typ: Term, free_vars: &FreeVars) -> Term {
  let typ = substitute_forall(typ, free_vars);

  add_forall_to_type(typ, free_vars.keep_vars())
}

/// Is previously encountered type arg
fn check_free_vars<'a>(
  name: &'a Identifier,
  current_type: &'a Term,
  free_vars: &mut FreeVars<'a>,
) -> bool {
  use FreeVar::*;
  if let Some(free_var) = free_vars.get_free_var(name) {
    match free_var {
      Detected { term: detected, .. } => {
        let b = compare_types(detected, current_type, free_vars);
        if !b {
          println!("{detected} != {current_type}");
        }
        b
      }
      Unknown { typ } => {
        free_vars.insert_free_var(
          name,
          Detected {
            typ,
            term: current_type,
          },
        );
        true
      }
    }
  } else {
    false
  }
}

pub fn compare_types(left: &Term, right: &Term, free_vars: &FreeVars) -> bool {
  match (left, right) {
    (App { fun: f1, arg: a1 }, App { fun: f2, arg: a2 }) => {
      let f_res = compare_types(f1, f2, free_vars);
      let a_res = compare_types(a1, a2, free_vars);
      f_res && a_res
    }
    (
      Pi {
        ret: r1, arg: a1, ..
      },
      Pi {
        ret: f2, arg: a2, ..
      },
    ) => {
      let f_res = compare_types(r1, f2, free_vars);
      let a_res = compare_types(a1, a2, free_vars);
      f_res && a_res
    }
    (Var { name: n1 }, Var { name: n2 }) => {
      if free_vars.contains_name_ref(n1) || free_vars.contains_name_ref(n2) {
        return true;
      }
      if n1.is_name() {
        n1.clone().to_path() == n2.clone().to_path()
      } else {
        n1 == n2
      }
    }
    _ => left == right,
  }
}
fn match_resolve_type_inner<'a>(
  left: &'a Term,
  right: &'a Term,
  free_vars: &mut FreeVars<'a>,
) -> bool {
  use FreeVar::*;
  match (left, right) {
    (Forall { name, typ, body }, _) => {
      free_vars.insert_free_var(name, Unknown { typ });
      match_resolve_type_inner(body, right, free_vars)
    }
    (_, Forall { name, typ, body }) => {
      free_vars.add_var_to_keep(name, typ);

      match_resolve_type_inner(left, body, free_vars)
    }
    (
      Pi {
        arg: a_arg,
        ret: a_ret,
        arg_name,
        ..
      },
      Pi {
        arg: b_arg,
        ret: b_ret,
        arg_name: _,
        ..
      },
    ) => {
      if let Some(name) = arg_name {
        free_vars.insert_free_var(name, Unknown { typ: a_arg });
      }
      let arg = match_resolve_type_inner(a_arg, b_arg, free_vars);
      let ret = match_resolve_type_inner(a_ret, b_ret, free_vars);
      let b = arg && ret;
      if !b {
        println!("{left} != {right} arg={arg} ret={ret} vars={free_vars}");
      }
      b
    }
    (App { fun: f1, arg: a1 }, App { fun: f2, arg: a2 }) => {
      let f_res = match_resolve_type_inner(f1, f2, free_vars);
      let a_res = match_resolve_type_inner(a1, a2, free_vars);
      let b = f_res && a_res;
      if !b {
        println!("app {left} != {right}");
      }
      b
    }
    (Hole, _) => true,
    (_, Hole) => true,
    (Ctx { loc: _, term }, _) => match_resolve_type_inner(term, right, free_vars),
    (_, Ctx { loc: _, term }) => match_resolve_type_inner(left, term, free_vars),
    (Var { name: n1 }, Var { name: n2 }) => {
      if n1.is_name() {
        if check_free_vars(n1.as_id().unwrap(), right, free_vars) {
          true
        } else {
          n1.clone().to_path() == n2.clone().to_path()
        }
      } else {
        n1 == n2
      }
    }
    (Type { universe: _ }, Var { name: Id(name) }) => name.as_str() == "Type",
    (Var { name: Id(name) }, Type { universe: _ }) => name.as_str() == "Type",
    (Var { name: Id(name) }, _) => check_free_vars(name, right, free_vars),
    _ => compare_types(left, right, free_vars),
  }
}

/// Try to desugar a method call pattern `x.fun` to `A.fun x` where `x: A`.
/// Also handles `x.fun arg` -> `A.fun arg x`.
/// Returns `None` if the term is not a method call pattern.
pub fn try_desugar_method_call(term: Term, scope: &Scope) -> Option<Term> {
  use NameRef::P;
  use Term::Var;

  match term {
    // Pattern: x.fun (no args)
    Var { name: P(path) } if path.len() >= 2 => {
      let (_type_name, method_path, receiver_id) = get_method_call_info(&path, scope)?;
      Some(app(
        Var {
          name: P(method_path),
        },
        Var {
          name: NameRef::Id(receiver_id),
        },
      ))
    }
    // Pattern: x.fun arg (with args)
    App { fun, arg } => {
      if let Var { name: P(path) } = *fun {
        if path.len() >= 2 {
          let (_type_name, method_path, receiver_id) = get_method_call_info(&path, scope)?;
          return Some(app(
            app(
              Var {
                name: P(method_path),
              },
              *arg,
            ),
            Var {
              name: NameRef::Id(receiver_id),
            },
          ));
        }
      }
      None
    }
    _ => None,
  }
}

/// Helper to extract method call info from a path, checking the receiver is a local var.
/// Returns (type_name, method_path, receiver_id).
fn get_method_call_info(
  path: &ModulePath,
  scope: &Scope,
) -> Option<(Identifier, ModulePath, Identifier)> {
  let parts = path.clone().to_vec();
  let receiver_id = &parts[0];

  // Check if receiver is a local variable
  let local_var = scope.find_local(receiver_id)?;
  let receiver_type = local_var.typ().clone();

  // Extract the type name from the receiver's type
  let type_name = extract_type_name(&receiver_type)?;

  // Build the method path: A.fun
  let method_parts: Vec<Identifier> = parts[1..].to_vec();
  let method_path = ModulePath::new(
    std::iter::once(type_name.clone())
      .chain(method_parts.into_iter())
      .collect(),
  );

  Some((type_name, method_path, receiver_id.clone()))
}

/// Extract the type name from a type term.
/// Returns `None` for complex types like `App(List, A)` or `Hole`.
fn extract_type_name(typ: &Term) -> Option<Identifier> {
  match typ {
    Term::Var { name } => match name {
      NameRef::Id(id) => Some(id.clone()),
      NameRef::P(path) if path.len() == 1 => Some(path.last().clone()),
      _ => None,
    },
    _ => None,
  }
}

pub fn type_check_free_var(
  mut term: Term,
  expected_type: Term,
  nref: &NameRef,
  scope: &Scope,
) -> Result<TypedTerm, TypeError> {
  use TypeError::*;
  let defined = scope.find_var_ref_of(nref, &expected_type)?;
  match defined {
    VarRef::UpdateRef {
      new_path,
      term: _,
      typ: _,
    } => {
      term = Var {
        name: new_path.clone().into(),
      };
    }
    _ => {
      if let NameRef::Op(op) = nref {
        if let Ok(infix) = scope.global().find_infix(op) {
          term = Var {
            name: NameRef::P(infix.name().clone()),
          };
        }
      }
    }
  }
  let defined_type = defined.typ();
  if !expected_type.is_known() {
    let typ = defined_type.clone();
    Ok(typed_term(term, typ))
  } else if let Ok(typ) = match_resolve_type(defined_type, &expected_type, scope) {
    Ok(typed_term(term, typ))
  } else {
    Err(FreeVarMismatch {
      name: nref.clone(),
      actual: defined_type.clone(),
      expected: expected_type,
      locals: scope.local_bindings(),
    })
  }
}

fn extract_first_name(term: &Term) -> Option<(ModulePath, Vec<Term>)> {
  match term {
    Var { name } => name.clone().to_path().map(|p| (p, Vec::new())),
    App { fun, arg } => extract_first_name(fun).map(|(p, mut args)| {
      args.push(*arg.clone());
      (p, args)
    }),
    _ => None,
  }
}

/// Find unknown identifiers in a type
pub fn free_vars(typ: &Term, known_names: &Set<&ModulePath>) -> Set<Identifier> {
  match typ {
    Pi {
      arg, ret, arg_name, ..
    } => {
      let mut a = free_vars(arg, known_names);
      if let Some(name) = arg_name {
        let mut known_names = known_names.clone();
        let name = name.clone().to_path();
        known_names.insert(&name);
        let r = free_vars(ret, &known_names);
        a.extend(r);
      } else {
        let r = free_vars(ret, known_names);
        a.extend(r);
      }
      a
    }
    Var { name } if name.is_name() && !known_names.contains(&name.to_path().unwrap()) => {
      set_of(vec![name.as_id().unwrap().clone()].into_iter())
    }
    App { fun, arg } => {
      let mut f = free_vars(fun, known_names);
      let a = free_vars(arg, known_names);
      f.extend(a);
      f
    }
    Forall { name, typ: _, body } => {
      let mut known_names = known_names.clone();
      let name = ModulePath::single(name.clone());
      known_names.insert(&name);
      free_vars(body, &known_names)
    }
    _ => empty_set(),
  }
}

pub fn add_forall_to_scope<'a>(typ: &'a Term, scope: Scope<'a>) -> Scope<'a> {
  match typ {
    Forall { name, typ, body } => add_forall_to_scope(body, scope.with_forall(name, typ.as_ref())),
    _ => scope,
  }
}

pub fn unwrap_forall(typ: Term) -> (Map<Identifier, Term>, Term) {
  match typ {
    Forall { name, typ, body } => {
      let (mut map, term) = unwrap_forall(*body);
      map.insert(name, *typ);
      (map, term)
    }
    _ => (Map::new(), typ),
  }
}
/// Substitue forall variable in expression given scope
pub fn substitute_forall(typ_: Term, free_vars: &FreeVars) -> Term {
  match typ_ {
    Forall { name, typ, body } => {
      if let Some(FreeVar::Detected { typ: _, term }) = free_vars.get_free_var(&name) {
        let res = substitute(*body, &Id(name), term);

        substitute_forall(res, free_vars)
      } else {
        let res = substitute_forall(*body, free_vars);
        forall(param(name, *typ), res)
      }
    }
    _ => typ_,
  }
}

pub fn substitute_params(mut term: Term, params: &[Param], args: &[Term]) -> Term {
  for (param, arg) in params.iter().zip(args.iter()) {
    let name = param.name.clone();
    term = substitute(term, &Id(name), arg);
  }
  term
}
pub fn add_params_to_scope<'a>(params: &[Param], args: &[Term], scope: Scope<'a>) -> Scope<'a> {
  for (param, arg) in params.iter().zip(args.iter()) {
    scope.with_local_var(&param.name, arg);
  }
  scope
}

pub fn pi_of_forall_types(arg_type: Term, return_type: Term) -> Term {
  let (return_foralls, return_type) = unwrap_forall(return_type);
  let (arg_foralls, arg_type) = unwrap_forall(arg_type);
  let (forall_vars, return_type) = return_foralls.into_iter().fold(
    (arg_foralls, return_type),
    |(mut vars, return_type), (name, typ)| {
      if vars.contains_key(&name) {
        let new_name = name.rename();
        let return_type = rename_variable(return_type, new_name.clone(), name);
        vars.insert(new_name, typ);
        (vars, return_type)
      } else {
        vars.insert(name, typ);
        (vars, return_type)
      }
    },
  );
  let fun_type = pi(arg_type, return_type);
  let forall_vars = forall_vars.iter().collect();

  add_forall_to_type(fun_type, &forall_vars)
}

const INT_SUFFIXES: [NumSuffix; 8] = [
  NumSuffix::I8,
  NumSuffix::I16,
  NumSuffix::I32,
  NumSuffix::I64,
  NumSuffix::U8,
  NumSuffix::U16,
  NumSuffix::U32,
  NumSuffix::U64,
];

const FLOAT_SUFFIXES: [NumSuffix; 2] = [NumSuffix::F32, NumSuffix::F64];

fn is_number_type_name(name: &str) -> bool {
  INT_SUFFIXES.iter().any(|s| s.type_name() == name)
    || FLOAT_SUFFIXES.iter().any(|s| s.type_name() == name)
}

fn suffix_from_type_name(name: &str) -> Option<NumSuffix> {
  INT_SUFFIXES
    .iter()
    .chain(FLOAT_SUFFIXES.iter())
    .find(|s| s.type_name() == name)
    .copied()
}

fn resolve_num_literal_type(
  expected: &Term,
  _default: NumSuffix,
  _scope: &Scope,
) -> Result<NumSuffix, TypeError> {
  if let Term::Var { name } = expected
    && let NameRef::Id(id) = name
  {
    let name_str = id.as_str();
    if is_number_type_name(name_str)
      && let Some(suffix) = suffix_from_type_name(name_str)
      && suffix.is_int()
    {
      return Ok(suffix);
    }
  }
  Ok(NumSuffix::I64)
}

fn resolve_float_literal_type(
  expected: &Term,
  _default: NumSuffix,
  _scope: &Scope,
) -> Result<NumSuffix, TypeError> {
  if let Term::Var { name } = expected
    && let NameRef::Id(id) = name
  {
    let name_str = id.as_str();
    if is_number_type_name(name_str)
      && let Some(suffix) = suffix_from_type_name(name_str)
      && suffix.is_float()
    {
      return Ok(suffix);
    }
  }
  Ok(NumSuffix::F64)
}

fn convert_int_literal(value: i64, suffix: NumSuffix) -> Result<Term, TypeError> {
  let fits = match suffix {
    NumSuffix::I8 => value >= i64::from(i8::MIN) && value <= i64::from(i8::MAX),
    NumSuffix::I16 => value >= i64::from(i16::MIN) && value <= i64::from(i16::MAX),
    NumSuffix::I32 => value >= i64::from(i32::MIN) && value <= i64::from(i32::MAX),
    NumSuffix::I64 => true,
    NumSuffix::U8 => value >= 0 && value <= i64::from(u8::MAX),
    NumSuffix::U16 => value >= 0 && value <= i64::from(u16::MAX),
    NumSuffix::U32 => value >= 0 && value <= i64::from(u32::MAX),
    NumSuffix::U64 => value >= 0,
    _ => return Ok(num_suffix(value, suffix)),
  };
  if fits {
    Ok(num_suffix(value, suffix))
  } else {
    Err(TypeError::Overflow {
      value,
      target: suffix.type_name(),
    })
  }
}

/// Check and compute the Type of a Term
/// Resolves type classes
/// Public wrapper that creates a fresh UsageEnv if not present
pub fn type_check(term: Term, expected_type: Term, scope: &Scope) -> Result<TypedTerm, TypeError> {
  let mut usage = UsageEnv::new();
  type_check_with_env(term, expected_type, scope, &mut usage, true)
}

/// Internal type check with UsageEnv for linear type tracking
/// `usage` is passed separately from Scope to avoid cloning issues.
/// `track_usage` controls whether linear/affine usage is counted
/// (false for verification-only passes that should not re-count).
fn type_check_with_env(
  term: Term,
  expected_type: Term,
  scope: &Scope,
  usage: &mut UsageEnv,
  track_usage: bool,
) -> Result<TypedTerm, TypeError> {
  use TypeError::*;
  let scope = add_forall_to_scope(&expected_type, scope.clone());
  match term {
    App { fun, arg } => {
      // Try desugaring method calls with args (x.fun arg -> A.fun arg x)
      if let Some(desugared) = try_desugar_method_call(
        App {
          fun: fun.clone(),
          arg: arg.clone(),
        },
        &scope,
      ) {
        return type_check(desugared, expected_type.clone(), &scope);
      }
      let arg = *arg;
      // First check: infer arg type (counts usage for linear tracking)
      let (arg, arg_type) = type_check_with_env(arg.clone(), Hole, &scope, usage, true)
        .map(|tt| tt.to_tuple())
        .unwrap_or_else(|_| (arg, Hole));
      let fun_type = pi_of_forall_types(arg_type.clone(), expected_type.clone());
      // Check function against expected type with the inferred arg type
      let (fun, fun_type) =
        type_check_with_env(*fun, fun_type, &scope, usage, track_usage)?.to_tuple();
      let (fun_vars, fun_typ_pi) = unwrap_forall(fun_type);
      if let Pi {
        arg: arg_type,
        ret,
        arg_name: _,
        ..
      } = fun_typ_pi
      {
        let fun_forall_vars: Map<&Identifier, &Term> = fun_vars.iter().collect();
        let mut arg_type = *arg_type.clone();
        arg_type = add_forall_to_type(arg_type, &fun_forall_vars);
        // Second check: verify arg against expected type (DON'T count usage again)
        let (arg, _) = if arg_type.is_known() {
          type_check_with_env(arg, arg_type, &scope, usage, false)?.to_tuple()
        } else {
          (arg, arg_type)
        };
        let term = app(fun, arg);
        let ret_type = *ret.clone();
        let ret_type = add_forall_to_type(ret_type, &fun_forall_vars);
        Ok(typed_term(term, ret_type))
      } else {
        Err(ExpectedPi(fun_typ_pi.clone()))
      }
    }
    Lit {
      value: Literal::Map { ref value },
    } => {
      if let Var { name } = &expected_type
        && let Some(name) = name.to_path()
      {
        let ind = scope.find_inductive(&name)?;
        let stru = ind
          .constructors
          .first()
          .ok_or_else(|| generic_terr("Structs must have at least one constructor".to_string()))?;
        let map = &value.value;
        // TODO default values
        if map.len() != stru.params.len() {
          return Err(generic_terr(format!(
            "to few args in struct {:?} {:?}",
            map, stru.params
          )));
        }
        for Param { name, typ, .. } in stru.params.iter() {
          let term = map.get(name).ok_or_else(|| MissingField(name.clone()))?;
          type_check_with_env(term.clone(), *typ.clone(), &scope, usage, track_usage)?;
        }
        Ok(typed_term(term, expected_type.clone()))
      } else {
        Err(generic_terr(format!(
          "Expected name for struct found {expected_type}"
        )))
      }
    }
    Lit {
      value: Literal::Match {
        ref value,
        ref cases,
      },
    } => {
      let con = type_check_with_env(*value.clone(), Hole, &scope, usage, track_usage)?;

      if let Some((ind_name, ind_args)) = extract_first_name(con.typ()) {
        let ind = scope.find_inductive(&ind_name)?;
        let ind_params = &ind.params;
        if ind_params.len() != ind_args.len() {
          return Err(InductiveMismatch {
            name: ind_name,
            params: ind_params.clone(),
            args: ind_args,
          });
        }
        let mut branch_t = expected_type.clone();
        for case in cases {
          if let Some(ind_cons) = ind.find_cons(&case.name) {
            let mut scope = scope.clone();
            if ind_cons.params.len() != case.args.len() {
              return Err(ConstructorMismatch {
                params: ind_cons.params.clone(),
                args: case.args.clone(),
              });
            }
            for (name, param) in case.args.iter().zip(ind_cons.params.iter()) {
              let typ = substitute_params(*param.typ.clone(), ind_params, &ind_args);
              scope = add_params_to_scope(ind_params, &ind_args, scope);
              scope = scope.with_type_owned(name, typ);
            }
            let t = type_check_with_env(
              *case.value.clone(),
              branch_t.clone(),
              &scope,
              usage,
              track_usage,
            )?;
            if let Ok(typ) = match_resolve_type(&branch_t, t.typ(), &scope) {
              branch_t = typ;
            } else {
              return Err(MismatchingBranches(branch_t, t.typ().clone()));
            }
          } else {
            return Err(ConstructorUnknown(case.name.clone()));
          }
        }
        Ok(typed_term(term, branch_t.clone()))
      } else {
        Err(ExpectedInductive(con.typ().clone()))
      }
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let b = type_check_with_env(*value, var("Bool"), &scope, usage, track_usage)?;
      let t1 = type_check_with_env(*then, expected_type.clone(), &scope, usage, track_usage)?;
      let t2 = type_check_with_env(*els, expected_type.clone(), &scope, usage, track_usage)?;
      if let Ok(typ) = match_resolve_type(t1.typ(), t2.typ(), &scope) {
        let new_term = Lit {
          value: Literal::If {
            value: Box::new(b.term().clone()),
            then: Box::new(t1.term().clone()),
            els: Box::new(t2.term().clone()),
          },
        };
        Ok(typed_term(new_term, typ))
      } else {
        Err(TypeError::MismatchingBranches(
          t1.typ().clone(),
          t2.typ().clone(),
        ))
      }
    }
    Lit { ref value } => match value {
      Literal::Str { value: _ } => {
        let typ = match_resolve_type(&var("String"), &expected_type, &scope)?;
        Ok(typed_term(term, typ))
      }
      Literal::Num { value, suffix } => {
        if suffix.is_int() {
          let target = resolve_num_literal_type(&expected_type, *suffix, &scope)?;
          let converted = convert_int_literal(*value, target)?;
          Ok(typed_term(converted, var(target.type_name())))
        } else {
          let typ = match_resolve_type(&var("F64"), &expected_type, &scope)?;
          Ok(typed_term(term, typ))
        }
      }
      Literal::Float { value, suffix } => {
        if suffix.is_float() {
          let target = resolve_float_literal_type(&expected_type, *suffix, &scope)?;
          Ok(typed_term(
            Term::Lit {
              value: Literal::Float {
                value: *value,
                suffix: target,
              },
            },
            var(target.type_name()),
          ))
        } else {
          let typ = match_resolve_type(&var("F64"), &expected_type, &scope)?;
          Ok(typed_term(term, typ))
        }
      }
      _ => panic!("Lit branch not covered {value}"),
    },
    Var { ref name } => {
      // Try desugaring method calls (x.fun -> A.fun x)
      if let NameRef::P(path) = name {
        if path.len() >= 2
          && let Some(desugared) = try_desugar_method_call(term.clone(), &scope)
        {
          return type_check(desugared, expected_type.clone(), &scope);
        }
      }
      let name = name.clone();
      // Check usage for linear/affine variables (only when tracking)
      if track_usage {
        if let NameRef::Id(ref id) = name {
          usage.check_usage(id)?;
          usage.mark_used(id);
        }
      }
      type_check_free_var(term, expected_type.clone(), &name, &scope)
    }
    Lam { param, body } => {
      if expected_type.is_known() {
        let (vars, typ) = unwrap_forall(expected_type.clone());
        let vars = vars.iter().collect();
        if let Pi {
          arg,
          ret,
          arg_name: _,
          ..
        } = typ
        {
          let arg_type = *arg.clone();
          let arg_type = add_forall_to_type(arg_type, &vars);
          let param_type = param.typ();
          let arg_type = match_resolve_type(&arg_type, param_type, &scope).map_err(|_| {
            TypeError::ArgumentMismatch {
              expected: *arg.clone(),
              actual: param.typ().clone(),
            }
          })?;
          // Register param in usage env (before body check)
          if let Par::P(ref p) = param {
            usage.register(p.name.clone(), p.mult.clone());
          }
          let scope = scope.with_param(&param);
          let return_type = *ret.clone();
          let return_type = add_forall_to_type(return_type, &vars);
          let (body, return_type) =
            type_check_with_env(*body.clone(), return_type, &scope, usage, track_usage)?.to_tuple();
          // Verify linear params were used
          usage.verify_linear_usage()?;
          let lam_type = pi_of_forall_types(arg_type.clone(), return_type);
          let term = lam_par(param.with_type(arg_type), body);
          Ok(typed_term(term, lam_type))
        } else {
          Err(TypeError::ExpectedPi(typ.clone()))
        }
      } else {
        let param_type = param.typ();
        // Register param in usage env (before body check)
        if let Par::P(ref p) = param {
          usage.register(p.name.clone(), p.mult.clone());
        }
        let scope = scope.with_param(&param);
        let (body, body_type) =
          type_check_with_env(*body.clone(), Hole, &scope, usage, track_usage)?.to_tuple();
        // Verify linear params were used
        usage.verify_linear_usage()?;
        let lam_type = pi(param_type.clone(), body_type);
        let term = lam_par(param, body);
        Ok(typed_term(term, lam_type))
      }
    }
    Type { universe } => {
      if let Type { universe: u2 } = expected_type
        && u2 > universe
      {
        let universe = universe + 1;
        Ok(typed_term(term, type_u(universe)))
      } else {
        Err(TypeError::ExpectedType(term))
      }
    }
    Ntv { native: _ } => Ok(typed_term(term.clone(), expected_type.clone())),
    Con(Constructor {
      ref typ_name,
      ref args,
      ref name,
      num_args: _,
    }) => {
      let inductive = scope.find_inductive(typ_name)?;
      let cons = inductive
        .find_cons(name)
        .ok_or_else(|| ConstructorUnknown(name.clone()))?;
      let (arg_res, errs) = join_many_results(
        args
          .iter()
          .zip(cons.params.iter())
          .filter_map(|(o_arg, param)| {
            o_arg.as_ref().map(|arg| {
              type_check_with_env(arg.clone(), *param.typ.clone(), &scope, usage, track_usage)
            })
          })
          .collect(),
      );
      if !errs.is_empty() {
        return Err(Many(errs));
      }
      let ind_type = apps(
        mpvar(inductive.name().clone()),
        inductive.params().iter().map(|_| Hole).collect(),
      );
      let lam_types: Vec<Term> = arg_res.into_iter().map(|tt| tt.to_tuple().1).collect();
      let cons_type = if !lam_types.is_empty() {
        pi_typs(lam_types, ind_type)
      } else {
        ind_type
      };
      let cons_type = match_resolve_type(&cons_type, &expected_type, &scope)?;
      Ok(typed_term(term.clone(), cons_type))
    }
    Ctx { ref loc, term } => {
      let mut tt = type_check_with_env(*term, expected_type.clone(), &scope, usage, track_usage)
        .map_err(|err| t_context(err, None, loc.clone()))?;

      *tt.mut_term() = ctx(tt.term().clone(), loc.clone());
      Ok(tt)
    }
    Forall {
      name: _,
      typ: _,
      body: _,
    } => Ok(typed_term(term, expected_type)),
    Pi {
      ref arg,
      ref ret,
      arg_name: _,
      ..
    } => {
      if expected_type.is_type() {
        let _arg = type_check_with_env(*arg.clone(), type0(), &scope, usage, track_usage)?;
        let _ret = type_check_with_env(*ret.clone(), type0(), &scope, usage, track_usage)?;
        Ok(typed_term(term.clone(), type0()))
      } else {
        Err(TypeError::ExpectedType(expected_type.clone()))
      }
    }
    Term::Prop => Ok(typed_term(term, type0())),
    Hole => Ok(typed_term(term, expected_type)),
    Ann { term, typ } => {
      let tt = type_check_with_env(*term, *typ, &scope, usage, track_usage)?;
      let typ = match_resolve_type(tt.typ(), &expected_type, &scope)?;
      Ok(typed_term(tt.term, typ))
    }
  }
}

/// Replace local var identifiers with index
pub fn substitute_local_var_with_index(term: Term, name: &Identifier) -> Term {
  substitute_var_with_index_inner(term, name, 1)
}

fn substitute_var_with_index_inner(term: Term, name: &Identifier, index: usize) -> Term {
  match &term {
    Var {
      name: NameRef::Id(id),
    } if id == name => bvar(index),
    Lam { param, body } => match param {
      Par::P(param) if &param.name == name => term,
      _ => {
        let body = substitute_var_with_index_inner(*body.clone(), name, index + 1);
        Lam {
          param: param.clone(),
          body: Box::new(body),
        }
      }
    },
    // TODO
    _ => term,
  }
}

pub fn type_check_decl(decl: Decl, scope: &Scope) -> Result<Decl, TypeError> {
  match decl {
    Decl::Use(ref u) => {
      scope
        .global()
        .get_module(&u.module_path)
        .ok_or_else(|| TypeError::Scope(ScopeError::PathNotFound(u.module_path.clone())))?;
      Ok(decl)
    }
    Decl::Def(def) => type_check_def(def, scope).map(Decl::Def),
    Decl::Ins(instance) => {
      let class = scope.find_inductive(&instance.class_name)?;
      type_check_instance(instance, class, scope).map(Decl::Ins)
    }
    Decl::Infix(_) => Ok(decl), // TODO
    _ => Ok(decl),
  }
}

pub fn elaborate_type(
  typ: Term,
  type_constraints: &[TypeConstraint],
  known_names: &Set<&ModulePath>,
) -> Term {
  let constraint_vars: Set<Identifier> = type_constraints
    .iter()
    .flat_map(|cons| cons.vars().iter().cloned())
    .collect();
  let free_vars = free_vars(&typ, known_names);
  let free_vars: Set<&Identifier> = free_vars.union(&constraint_vars).collect();
  let default_type = type0();
  let free_vars_map: Map<&Identifier, &Term> =
    free_vars.into_iter().map(|i| (i, &default_type)).collect();

  add_forall_to_type(typ, &free_vars_map)
}
pub fn elaborate_def(mut def: Def, known_names: &Set<&ModulePath>) -> Def {
  let typ = def.typ.clone();
  let typ = elaborate_type(typ, &def.type_constraints, known_names);
  def.typ = typ;
  def
}

pub fn add_forall_to_type(mut typ: Term, vars: &Map<&Identifier, &Term>) -> Term {
  let free_vars = free_vars(&typ, &empty_set());
  for (&name, &param_typ) in vars {
    if free_vars.contains(name) {
      typ = forall(param(name.clone(), param_typ.clone()), typ);
    }
  }
  typ
}

fn type_check_def(mut def_: Def, scope: &Scope) -> Result<Def, TypeError> {
  let (term, typ) = type_check(def_.term, def_.typ, scope)?.to_tuple();
  def_.term = term;
  def_.typ = typ;
  Ok(def_)
}

fn type_check_decls(
  decls: Vec<SourceContext<Decl>>,
  scope: &Scope,
) -> (Vec<SourceContext<Decl>>, Vec<TypeError>) {
  let res = decls
    .into_iter()
    .map(|ctx| {
      let decl = ctx.value();
      type_check_decl(decl.clone(), scope)
        .map(|d| ctx.with(d))
        .map_err(|err| TypeError::Context {
          name: Some(decl.to_ref().clone()),
          loc: ctx.loc.clone(),
          err: Box::new(err),
        })
    })
    .collect();
  join_many_results(res)
}

pub fn pi_to_vec(mut typ: Term) -> (Vec<Term>, Term) {
  let mut res = Vec::new();
  while let Pi {
    arg,
    ret,
    arg_name: _,
    ..
  } = typ
  {
    res.push(*arg);
    typ = *ret;
  }
  (res, typ)
}

pub fn elaborate_inductive(mut ind: Inductive, known_names: &Set<&ModulePath>) -> Inductive {
  let is_class = ind.variant() == &InductiveVariant::Class;
  let default_type = type0();
  let params: Map<Identifier, Term> = ind
    .params()
    .iter()
    .map(|p| {
      (
        p.name.clone(),
        (*p.typ).clone().replace_hole(|| default_type.clone()),
      )
    })
    .collect();
  let param_paths: Set<ModulePath> = params.keys().map(|name| name.clone().to_path()).collect();
  let known_names: Set<&ModulePath> = param_paths
    .iter()
    .chain(known_names.iter().copied())
    .collect();
  for cons in ind.constructors.iter_mut() {
    let typ = cons.typ().clone();
    cons.typ = if is_class {
      let (mut class_defs, ret) = pi_to_vec(typ);
      for (typ, param) in class_defs.iter_mut().zip(cons.params.iter_mut()) {
        let free_vars = free_vars(typ, &known_names);
        let vars = free_vars
          .iter()
          .map(|i| (i, &default_type))
          .chain(params.iter())
          .collect();
        *typ = add_forall_to_type(typ.clone(), &vars);
        *param.typ = typ.clone();
      }
      pi_typs(class_defs, ret)
    } else {
      let free_vars = free_vars(&typ, &known_names);
      let default_type = type0();
      let vars = free_vars
        .iter()
        .map(|i| (i, &default_type))
        .chain(params.iter())
        .collect();
      add_forall_to_type(typ, &vars)
    }
  }
  ind
}
pub fn elaborate_instance(mut ins: Instance, known_names: &Set<&ModulePath>) -> Instance {
  for imp in ins.impls_map.values_mut() {
    let typ = imp.typ.clone();
    let free_vars = free_vars(&typ, known_names);
    let default_type = type0();
    let vars = free_vars.iter().map(|i| (i, &default_type)).collect();
    imp.typ = add_forall_to_type(typ, &vars);
  }
  ins
}

pub fn elaborate_decl(decl: Decl, known_names: &Set<&ModulePath>) -> Decl {
  use Decl::*;

  match decl {
    Def(def) => Def(elaborate_def(def, known_names)),
    Type(ind) => Type(elaborate_inductive(ind, known_names)),
    Ins(ins) => Ins(elaborate_instance(ins, known_names)),
    _ => decl,
  }
}

pub fn elaborate_decls(
  decls: Vec<SourceContext<Decl>>,
  loaded: &LoadedModules,
) -> Vec<SourceContext<Decl>> {
  let path = mpt("_");
  let global = loaded.scope_of_decls(&path, &decls);
  let mut known_names: Set<ModulePath> = global.all_known_names().into_iter().cloned().collect();
  known_names.extend(names_of_decls(&decls));
  let known_names = known_names.iter().collect();
  decls
    .into_iter()
    .map(|ctx| ctx.map(|decl| elaborate_decl(decl, &known_names)))
    .collect()
}

pub fn type_check_module_decls(
  path: &ModulePath,
  decls: Vec<SourceContext<Decl>>,
  loaded: &LoadedModules,
) -> Result<Vec<SourceContext<Decl>>, TypeError> {
  let decls = elaborate_decls(decls, loaded);
  let global = loaded.scope_of_decls(path, &decls);

  let (oks, errs) = type_check_decls(decls.clone(), &global.scope());
  if !errs.is_empty() {
    Err(TypeError::Many(errs))
  } else {
    Ok(oks)
  }
}
