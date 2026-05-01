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
  /// Builds a substitution from the matched key args against class params,
  /// then resolves each constraint recursively.
  pub fn check_instance(
    &mut self,
    instance: &'a Instance,
    key: &InstanceKey,
    class: &'a Inductive,
  ) -> bool {
    if instance.constraints.is_empty() {
      return true;
    }

    let subst = build_substitution(key, class, instance);

    for constraint in &instance.constraints {
      if !self.check_constraint(constraint, &subst) {
        return false;
      }
    }
    true
  }

  /// Check if a single constraint is satisfiable.
  fn check_constraint(
    &mut self,
    constraint: &TypeConstraint,
    subst: &Map<Identifier, Term>,
  ) -> bool {
    let Some(concrete_type) = constraint.resolve_type(subst) else {
      return true;
    };

    let class_name = constraint.class();
    let visit_key = format!("{class_name}({concrete_type})");

    if self.visiting.contains(&visit_key) {
      return true;
    }
    self.visiting.insert(visit_key.clone());

    let result = self.resolve_constraint(class_name, &concrete_type);

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

/// Build a substitution map from InstanceKey args → instance args,
/// using class params as the bridge.
fn build_substitution(
  key: &InstanceKey,
  class: &Inductive,
  instance: &Instance,
) -> Map<Identifier, Term> {
  let mut subst = Map::new();
  for key_arg in &key.args {
    if let Some((idx, class_param)) = class
      .params
      .iter()
      .enumerate()
      .find(|(_, p)| p.name == key_arg.name)
      && let Some(inst_arg) = instance.args.get(idx)
    {
      subst.insert(class_param.name.clone(), inst_arg.clone());
    }
  }
  subst
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
