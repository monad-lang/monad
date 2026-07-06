use crate::term::module::GlobalScope;
use crate::term::{
  Identifier, Inductive, Instance, InstanceKey, ModulePath, Param, Term, TypeConstraint, param,
};
use crate::{Map, Set};

/// Error when a constraint cannot be satisfied.
#[derive(Debug, Clone)]
pub enum ConstraintError {
  /// No instance found for the given class and type.
  NoInstance { class: String, arg: String },
  /// Cyclic constraint dependency detected.
  Cycle,
}

impl std::fmt::Display for ConstraintError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ConstraintError::NoInstance { class, arg } => {
        write!(f, "no instance `{class}` found for type `{arg}`")
      }
      ConstraintError::Cycle => write!(f, "cyclic constraint dependency detected"),
    }
  }
}

impl From<&ConstraintError> for crate::diag::Diagnostic {
  fn from(err: &ConstraintError) -> Self {
    crate::diag::Diagnostic {
      severity: crate::diag::Severity::Error,
      message: err.to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    }
  }
}

/// Solver for type class constraints during instance resolution.
///
/// Takes a visiting set as a parameter so that cycle detection works
/// across nested solver instances (since Instance::matches calls
/// check_instance_constraints which creates a new solver).
pub struct ConstraintSolver<'a> {
  global: &'a GlobalScope<'a>,
}

impl<'a> ConstraintSolver<'a> {
  pub fn new(global: &'a GlobalScope<'a>) -> Self {
    Self { global }
  }

  /// Check if all constraints of an instance are satisfiable.
  ///
  /// The key contains the concrete type args (e.g., `{A -> I64}`).
  /// For each constraint like `[Add A]`, we look up `A` in the key's args
  /// to get the concrete type, then check that an instance exists.
  pub fn check_instance(
    &mut self,
    instance: &'a Instance,
    key: &InstanceKey,
    _class: &'a Inductive,
    visiting: &mut Set<String>,
  ) -> bool {
    if instance.constraints.is_empty() {
      return true;
    }

    // Build a map from type variable names to concrete types from the key
    let key_args: Map<Identifier, &Term> = key
      .args
      .iter()
      .map(|p| (p.name.clone(), p.typ.as_ref()))
      .collect();

    for constraint in &instance.constraints {
      if !self.check_constraint(constraint, &key_args, visiting) {
        return false;
      }
    }
    true
  }

  /// Check if a single constraint is satisfiable.
  pub(crate) fn check_constraint(
    &mut self,
    constraint: &TypeConstraint,
    key_args: &Map<Identifier, &Term>,
    visiting: &mut Set<String>,
  ) -> bool {
    // Get (var_name, concrete_type) pairs for each constraint var from the key args
    let concrete_types: Vec<(Identifier, Term)> = constraint
      .vars()
      .iter()
      .filter_map(|v| key_args.get(v).map(|t| (v.clone(), (*t).clone())))
      .collect();

    // If we couldn't resolve all vars, skip (will be caught elsewhere)
    if concrete_types.is_empty() {
      return true;
    }

    let class_name = constraint.class();
    let types_str = concrete_types
      .iter()
      .map(|(_, t)| format!("{t}"))
      .collect::<Vec<_>>()
      .join(",");
    let visit_key = format!("{class_name}({types_str})");

    // Check visiting set for cycle detection.
    if visiting.contains(&visit_key) {
      return true;
    }
    visiting.insert(visit_key.clone());

    let result = self.resolve_constraint(class_name, &concrete_types, visiting);

    visiting.remove(&visit_key);
    result
  }

  /// Try to find an instance for the given class and concrete type args,
  /// then recursively check that instance's constraints.
  fn resolve_constraint(
    &mut self,
    class_name: &ModulePath,
    concrete_types: &[(Identifier, Term)],
    visiting: &mut Set<String>,
  ) -> bool {
    let Some(class) = self.global.find_inductive(class_name) else {
      return false;
    };

    let key = build_constraint_key(class_name.clone(), concrete_types, class);
    let Some(instance) = self.global.find_instance_with_visiting(&key, visiting) else {
      return false;
    };

    self.check_instance(instance, &key, class, visiting)
  }
}

/// Build an InstanceKey for a constraint like `Add I64` or `HAdd I64 I64 I64`.
/// Matches all class params to concrete types by position (the constraint var
/// at position i maps to the class param at position i).
fn build_constraint_key(
  class_name: ModulePath,
  concrete_types: &[(Identifier, Term)],
  class: &Inductive,
) -> InstanceKey {
  let args: Vec<Param> = class
    .params
    .iter()
    .enumerate()
    .map(|(i, p)| {
      let typ = concrete_types
        .get(i)
        .map(|(_, typ)| typ.clone())
        .unwrap_or_else(|| (*p.typ).clone());
      param(p.name.clone(), typ)
    })
    .collect();

  InstanceKey::new(class_name, Vec::new(), args)
}

/// Check instance constraints with a shared visiting set for cycle detection.
/// Internal — called from Instance::matches during instance resolution.
pub fn check_instance_constraints_with_visiting(
  global: &GlobalScope,
  instance: &Instance,
  key: &InstanceKey,
  class: &Inductive,
  visiting: &mut Set<String>,
) -> bool {
  let mut solver = ConstraintSolver::new(global);
  solver.check_instance(instance, key, class, visiting)
}

/// Top-level function: check if an instance's constraints are satisfied.
/// Creates a fresh visiting set (no cycle sharing with callers).
pub fn check_instance_constraints(
  global: &GlobalScope,
  instance: &Instance,
  key: &InstanceKey,
  class: &Inductive,
) -> bool {
  let mut visiting = Set::default();
  check_instance_constraints_with_visiting(global, instance, key, class, &mut visiting)
}

/// Check if per-method constraints are satisfiable using a variable map
/// from Forall instantiation (maps type variable names to concrete types).
/// Returns Err with the first failing constraint description, or Ok(()).
/// Skips constraints where any mapped type is still an unresolved type variable.
/// In Monad's type representation, concrete types use `NameRef::P` (module path)
/// while type variables use `NameRef::Id` (bare identifier).
pub fn check_method_constraints(
  global: &GlobalScope,
  constraints: &Vec<TypeConstraint>,
  var_map: &Map<Identifier, &Term>,
) -> Result<(), String> {
  let mut solver = ConstraintSolver::new(global);
  let mut visiting = Set::default();
  for constraint in constraints {
    // Skip constraint if any of its variables are still unresolved type vars.
    // Unresolved type vars appear as Var{Id(_)} — they resolve to
    // Var{P(_)} or App{...} when concrete types are determined.
    let all_concrete = constraint.vars().iter().all(|v| {
      if let Some(t) = var_map.get(v) {
        match t {
          Term::Var { name } => !name.is_id(),
          _ => true, // App, Pi, etc. are concrete type expressions
        }
      } else {
        false
      }
    });
    if !all_concrete {
      continue;
    }
    if !solver.check_constraint(constraint, var_map, &mut visiting) {
      let concrete_types: Vec<String> = constraint
        .vars()
        .iter()
        .filter_map(|v| var_map.get(v).map(|t| format!("{}", *t)))
        .collect();
      let types_str = concrete_types.join(" ");
      return Err(format!(
        "constraint `{}` not satisfied for type(s): {}",
        constraint.class(),
        types_str
      ));
    }
  }
  Ok(())
}
