use crate::term::module::GlobalScope;
use crate::term::{
  Identifier, Inductive, Instance, InstanceKey, ModulePath, Term, TypeConstraint, param,
};
use crate::{Map, empty_set};

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

/// Solver for type class constraints during instance resolution.
///
/// Uses a visiting set to prevent infinite recursion when checking
/// constraints that themselves have constraints.
pub struct ConstraintSolver<'a> {
  global: &'a GlobalScope<'a>,
  /// Tracks constraint keys currently being resolved to detect cycles.
  visiting: crate::Set<String>,
}

impl<'a> ConstraintSolver<'a> {
  pub fn new(global: &'a GlobalScope<'a>) -> Self {
    Self {
      global,
      visiting: empty_set(),
    }
  }

  /// Check if all constraints of an instance are satisfiable.
  ///
  /// The key contains the concrete type args (e.g., `{A → I64}`).
  /// For each constraint like `[Add A]`, we look up `A` in the key's args
  /// to get the concrete type, then check that an instance exists.
  pub fn check_instance(
    &mut self,
    instance: &'a Instance,
    key: &InstanceKey,
    _class: &'a Inductive,
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
      if !self.check_constraint(constraint, &key_args) {
        return false;
      }
    }
    true
  }

  /// Check if a single constraint is satisfiable.
  fn check_constraint(
    &mut self,
    constraint: &TypeConstraint,
    key_args: &Map<Identifier, &Term>,
  ) -> bool {
    // Get the concrete type for each constraint var from the key args
    let concrete_types: Vec<Term> = constraint
      .vars()
      .iter()
      .filter_map(|v| key_args.get(v).map(|t| (*t).clone()))
      .collect();

    // If we couldn't resolve all vars, skip (will be caught elsewhere)
    if concrete_types.is_empty() {
      return true;
    }

    let class_name = constraint.class();
    let concrete_type = &concrete_types[0];
    let visit_key = format!("{class_name}({concrete_type})");

    if self.visiting.contains(&visit_key) {
      return true;
    }
    self.visiting.insert(visit_key.clone());

    let result = self.resolve_constraint(class_name, concrete_type);

    self.visiting.remove(&visit_key);
    result
  }

  /// Try to find an instance for the given class and concrete type,
  /// then recursively check that instance's constraints.
  fn resolve_constraint(&mut self, class_name: &ModulePath, concrete_type: &Term) -> bool {
    let Some(class) = self.global.find_inductive(class_name) else {
      return false;
    };

    let key = build_constraint_key(class_name.clone(), concrete_type.clone(), class);
    let Some(instance) = self.global.find_instance(&key) else {
      return false;
    };

    self.check_instance(instance, &key, class)
  }
}

/// Build an InstanceKey for a constraint like `Add I64`.
fn build_constraint_key(
  class_name: ModulePath,
  concrete_type: Term,
  class: &Inductive,
) -> InstanceKey {
  let param_name = class
    .params
    .first()
    .map(|p| p.name.clone())
    .unwrap_or_else(|| Identifier::new("A".to_string()));

  InstanceKey::new(
    class_name,
    Vec::new(),
    vec![param(param_name, concrete_type)],
  )
}

/// Top-level function: check if an instance's constraints are satisfied.
pub fn check_instance_constraints(
  global: &GlobalScope,
  instance: &Instance,
  key: &InstanceKey,
  class: &Inductive,
) -> bool {
  let mut solver = ConstraintSolver::new(global);
  solver.check_instance(instance, key, class)
}
