use std::fmt::Display;
use std::time::Instant;

use crate::{
  Map, Set, empty_set,
  eval::macro_expand,
  eval::termination::{TerminationError, check_termination_all},
  set_of,
  term::{
    Ann, ClassDefRef, Decl, DeclGenDef, Def, Identifier, Inductive, InductiveVariant, Instance,
    InstanceKey, Literal, ModulePath, Multiplicity, NameRef, Named, NumSuffix, SourceContext,
    SourceRange,
    Term::{Forall, Hole, Pi, Quote, Sort},
    TypeConstraint, Typed, TypedTerm, VarRef, app, ctx, forall, lam_par,
    module::{LoadedModules, names_of_decls},
    mpvar, num_suffix, param, pi_typs, pi_with_mult, sort_u, sort1, typed_term, var,
  },
  vec_fmt,
};

use super::*;

use crate::eval::constraint::check_method_constraints;
use crate::term::module::Scope;

fn is_known_type_name(name: &ModulePath, scope: &Scope) -> bool {
  scope.find_inductive(name).is_ok()
    || scope.global().find_ref(name).is_some()
    || scope.global().find_class_def(name).is_some()
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
  MismatchingBranches(Term, Term, SourceRange),
  ConstructorMismatch {
    params: Vec<Param>,
    args: Vec<Identifier>,
    loc: SourceRange,
  },
  InductiveMismatch {
    name: ModulePath,
    params: Vec<Param>,
    args: Vec<Term>,
    loc: SourceRange,
  },
  ConstructorUnknown(Identifier, Vec<Identifier>, SourceRange),
  Scope(ScopeError, SourceRange),
  ExpectedInductive(Term, SourceRange),
  ExpectedPi(Term, SourceRange),
  ExpectedType(Term, SourceRange),
  Context {
    name: Option<ModulePath>,
    loc: SourceRange,
    err: Box<TypeError>,
  },
  InstanceDecl(String, SourceRange),
  Instance(InstanceError, SourceRange),
  MissingField(Identifier, SourceRange),
  Generic(String, SourceRange),
  ArgumentMismatch {
    expected: Term,
    actual: Term,
    loc: SourceRange,
  },
  TypeMismatch {
    expected: Term,
    actual: Term,
    loc: SourceRange,
  },
  FreeVarMismatch {
    name: NameRef,
    expected: Term,
    actual: Term,
    locals: Map<Identifier, Term>,
    loc: SourceRange,
  },
  Overflow {
    value: i64,
    target: &'static str,
    loc: SourceRange,
  },
  Many(Vec<TypeError>),
  // Linear type errors
  LinearUsedMultipleTimes(Identifier, SourceRange),
  LinearUnused(Identifier, SourceRange),
  AffineUsedMultipleTimes(Identifier, SourceRange),
  ErasedUsedAtRuntime(Identifier, SourceRange),
  StructNoConstructors {
    loc: SourceRange,
  },
  ExpectedStructName {
    found: Term,
    loc: SourceRange,
  },
  StructUpdateExpectedInductive {
    found: Term,
    loc: SourceRange,
  },
  StructTooManyFields {
    max: usize,
    found: usize,
    loc: SourceRange,
  },
  MacroExpansion(crate::eval::macro_expand::MacroError),
  Termination(TerminationError),
}

impl From<ScopeError> for TypeError {
  fn from(value: ScopeError) -> Self {
    Self::Scope(value, SourceRange::default())
  }
}

impl Display for TypeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TypeError::MismatchingBranches(t1, t2, loc) => {
        write!(f, "Mismatching branches {t1} != {t2}")?;
        fmt_loc(loc, f)
      }
      TypeError::Scope(scope_error, loc) => {
        write!(f, "{scope_error}")?;
        fmt_loc(loc, f)
      }
      TypeError::ExpectedPi(s, loc) => {
        write!(f, "Expected function type found: {}", s)?;
        fmt_loc(loc, f)
      }
      TypeError::Context { loc, err, name } => {
        write!(f, "{} at {}:{}", err, loc.start.line, loc.start.column)?;
        if let Some(name) = name {
          write!(f, " in {name}")?;
        }
        Ok(())
      }
      TypeError::InstanceDecl(i, loc) => {
        write!(f, "{}", i)?;
        fmt_loc(loc, f)
      }
      TypeError::Generic(s, loc) => {
        write!(f, "{}", s)?;
        fmt_loc(loc, f)
      }
      TypeError::Many(type_errors) => {
        for (i, t) in type_errors.iter().enumerate() {
          writeln!(f, "{}. {}", i + 1, t)?;
        }
        Ok(())
      }
      TypeError::ConstructorMismatch { params, args, loc } => {
        write!(
          f,
          "Constructor mismatch {} != {}",
          vec_fmt(params),
          vec_fmt(args)
        )?;
        fmt_loc(loc, f)
      }
      TypeError::ExpectedType(e, loc) => {
        write!(f, "Expected Type found {e}")?;
        fmt_loc(loc, f)
      }
      TypeError::FreeVarMismatch {
        name,
        expected,
        actual,
        locals,
        loc,
      } => {
        write!(
          f,
          "Variable mismatch, expected {name} to be {expected} found {actual} with local vars [{}]",
          locals
            .iter()
            .map(|(name, typ)| format!("{name} : {typ}"))
            .collect::<Vec<_>>()
            .join(", ")
        )?;
        fmt_loc(loc, f)
      }
      TypeError::TypeMismatch {
        expected,
        actual,
        loc,
      } => {
        write!(f, "Type mismatch, expected {expected} found {actual}")?;
        fmt_loc(loc, f)
      }
      TypeError::MissingField(identifier, loc) => {
        write!(f, "Missing field {identifier}")?;
        fmt_loc(loc, f)
      }
      TypeError::ArgumentMismatch {
        expected,
        actual,
        loc,
      } => {
        write!(f, "Argument mismatch, expected {expected} found {actual}")?;
        fmt_loc(loc, f)
      }
      TypeError::Instance(instance_error, loc) => {
        write!(f, "instance {instance_error}")?;
        fmt_loc(loc, f)
      }
      TypeError::InductiveMismatch {
        name,
        params,
        args,
        loc,
      } => {
        write!(
          f,
          "Inductive {name} params mismatch {} != {}",
          vec_fmt(params),
          vec_fmt(args)
        )?;
        fmt_loc(loc, f)
      }
      TypeError::ConstructorUnknown(identifier, constructors, loc) => {
        write!(f, "Unknown constructor {identifier}")?;
        if let Some(suggestion) = did_you_mean(identifier.as_str(), &names_to_strings(constructors))
        {
          write!(f, "\n  = help: did you mean '{}'?", suggestion)?;
        }
        fmt_loc(loc, f)
      }
      TypeError::ExpectedInductive(term, loc) => {
        write!(f, "Expected inductive found {term}")?;
        fmt_loc(loc, f)
      }
      TypeError::Overflow { value, target, loc } => {
        write!(f, "Integer overflow: {value} does not fit in {target}")?;
        fmt_loc(loc, f)
      }
      TypeError::LinearUsedMultipleTimes(id, loc) => {
        write!(f, "Linear variable '{}' used more than once", id)?;
        fmt_loc(loc, f)
      }
      TypeError::LinearUnused(id, loc) => {
        write!(f, "Linear variable '{}' must be used exactly once", id)?;
        fmt_loc(loc, f)
      }
      TypeError::AffineUsedMultipleTimes(id, loc) => {
        write!(f, "Affine variable '{}' used more than once", id)?;
        fmt_loc(loc, f)
      }
      TypeError::ErasedUsedAtRuntime(id, loc) => {
        write!(
          f,
          "Erased variable '{}' used at runtime (erased vars are compile-time only)",
          id
        )?;
        fmt_loc(loc, f)
      }
      TypeError::StructNoConstructors { loc } => {
        write!(f, "Structs must have at least one constructor")?;
        fmt_loc(loc, f)
      }
      TypeError::ExpectedStructName { found, loc } => {
        write!(f, "Expected struct type, found {found}")?;
        fmt_loc(loc, f)
      }
      TypeError::StructUpdateExpectedInductive { found, loc } => {
        write!(f, "Struct update requires an inductive type, found {found}")?;
        fmt_loc(loc, f)
      }
      TypeError::StructTooManyFields { max, found, loc } => {
        write!(
          f,
          "Too many fields in struct literal (max {max}, found {found})"
        )?;
        fmt_loc(loc, f)
      }
      TypeError::MacroExpansion(err) => {
        write!(f, "macro expansion failed: {err}")
      }
      TypeError::Termination(err) => {
        write!(f, "{err}")
      }
    }
  }
}

fn err_to_diagnostic(err: &TypeError) -> crate::diag::Diagnostic {
  use crate::diag::{Diagnostic, Severity, SubDiagnostic, Suggestion};
  match err {
    TypeError::MismatchingBranches(t1, t2, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Mismatching branches {t1} != {t2}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Scope(scope_error, loc) => Diagnostic {
      severity: Severity::Error,
      message: scope_error.to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ExpectedPi(s, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected function type found: {s}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Context { loc, err, name } => {
      let mut diag = err_to_diagnostic(err);
      if let Some(name) = name {
        diag.context_name = Some(format!("{name}"));
      }
      if diag.location.is_none() {
        diag.location = loc_opt(loc);
      }
      diag
    }
    TypeError::InstanceDecl(i, loc) => Diagnostic {
      severity: Severity::Error,
      message: i.clone(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Generic(s, loc) => Diagnostic {
      severity: Severity::Error,
      message: s.clone(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ConstructorMismatch { params, args, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "Constructor mismatch {} != {}",
        crate::vec_fmt(params),
        crate::vec_fmt(args)
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ExpectedType(e, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected Type found {e}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::FreeVarMismatch {
      name,
      expected,
      actual,
      locals,
      loc,
    } => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "Variable mismatch, expected {name} to be {expected} found {actual} with local vars [{}]",
        locals
          .iter()
          .map(|(n, t)| format!("{n} : {t}"))
          .collect::<Vec<_>>()
          .join(", ")
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::TypeMismatch {
      expected,
      actual,
      loc,
    } => Diagnostic {
      severity: Severity::Error,
      message: "Type mismatch".to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![
        SubDiagnostic {
          severity: Severity::Note,
          message: format!("expected: {expected}"),
        },
        SubDiagnostic {
          severity: Severity::Note,
          message: format!("found:    {actual}"),
        },
      ],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::MissingField(identifier, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Missing field {identifier}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ArgumentMismatch {
      expected,
      actual,
      loc,
    } => Diagnostic {
      severity: Severity::Error,
      message: "Argument mismatch".to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![
        SubDiagnostic {
          severity: Severity::Note,
          message: format!("expected: {expected}"),
        },
        SubDiagnostic {
          severity: Severity::Note,
          message: format!("found:    {actual}"),
        },
      ],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Instance(instance_error, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("instance {instance_error}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::InductiveMismatch {
      name,
      params,
      args,
      loc,
    } => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "Inductive {name} params mismatch {} != {}",
        crate::vec_fmt(params),
        crate::vec_fmt(args)
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ConstructorUnknown(identifier, constructors, loc) => {
      let mut diag = Diagnostic {
        severity: Severity::Error,
        message: format!("Unknown constructor {identifier}"),
        location: loc_opt(loc),
        path: None,
        sub_diagnostics: vec![],
        suggestions: vec![],
        context_name: None,
      };
      if !constructors.is_empty() {
        let names: Vec<String> = constructors.iter().map(|n| n.to_string()).collect();
        diag.sub_diagnostics.push(SubDiagnostic {
          severity: Severity::Note,
          message: format!("available constructors: {}", names.join(", ")),
        });
        if let Some(suggestion) = did_you_mean(identifier.as_str(), &names) {
          diag.suggestions.push(Suggestion {
            message: format!("did you mean '{suggestion}'?"),
          });
        }
      }
      diag
    }
    TypeError::ExpectedInductive(term, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected inductive found {term}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Overflow { value, target, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Integer overflow: {value} does not fit in {target}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::LinearUsedMultipleTimes(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Linear variable '{id}' used more than once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::LinearUnused(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Linear variable '{id}' must be used exactly once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::AffineUsedMultipleTimes(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Affine variable '{id}' used more than once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ErasedUsedAtRuntime(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "Erased variable '{id}' used at runtime (erased vars are compile-time only)"
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Many(_errs) => Diagnostic {
      severity: Severity::Error,
      message: "Multiple type errors".to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::StructNoConstructors { loc } => Diagnostic {
      severity: Severity::Error,
      message: "Structs must have at least one constructor".to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::ExpectedStructName { found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected struct type, found {found}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::StructUpdateExpectedInductive { found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Struct update requires an inductive type, found {found}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::StructTooManyFields { max, found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Too many fields in struct literal (max {max}, found {found})"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::MacroExpansion(err) => Diagnostic {
      severity: Severity::Error,
      message: format!("macro expansion failed: {err}"),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
    TypeError::Termination(err) => Diagnostic {
      severity: Severity::Error,
      message: err.to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    },
  }
}

pub fn type_error_as_diagnostics(
  err: &TypeError,
  path: Option<&std::path::PathBuf>,
) -> Vec<crate::diag::Diagnostic> {
  let diags: Vec<_> = match err {
    TypeError::Many(errs) => errs.iter().map(err_to_diagnostic).collect(),
    single => vec![err_to_diagnostic(single)],
  };
  if let Some(path) = path {
    diags
      .into_iter()
      .map(|mut d| {
        d.path = Some(path.clone());
        if let Some(ref loc) = d.location {
          if loc.path.is_some() {
            d.path = loc.path.clone();
          }
        }
        d
      })
      .collect()
  } else {
    diags
  }
}

pub fn render_type_error_with_source(
  source: &str,
  error: &TypeError,
  use_colors: bool,
  path: Option<&std::path::PathBuf>,
) -> String {
  let diags = type_error_as_diagnostics(error, path);
  crate::diag::render_diagnostics(&diags, Some(source), use_colors)
}

// Keep the old 3-arg version for small compat cases
pub fn render_type_error_with_source_simple(source: &str, error: &TypeError) -> String {
  render_type_error_with_source(source, error, false, None)
}

fn loc_opt(loc: &SourceRange) -> Option<SourceRange> {
  if loc.start.line > 0 {
    Some(loc.clone())
  } else {
    None
  }
}

impl From<&TypeError> for crate::diag::Diagnostic {
  fn from(err: &TypeError) -> Self {
    err_to_diagnostic(err)
  }
}

fn fmt_loc(loc: &SourceRange, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
  if loc.start.line > 0 {
    write!(f, " at {}:{}", loc.start.line, loc.start.column)
  } else {
    Ok(())
  }
}

#[allow(dead_code)]
fn generic_terr(s: String) -> TypeError {
  TypeError::Generic(s, SourceRange::default())
}

fn names_to_strings(names: &[Identifier]) -> Vec<String> {
  names.iter().map(|n| n.to_string()).collect()
}

fn levenshtein_distance(a: &str, b: &str) -> usize {
  let a_chars: Vec<char> = a.chars().collect();
  let b_chars: Vec<char> = b.chars().collect();
  let a_len = a_chars.len();
  let b_len = b_chars.len();
  if a_len == 0 {
    return b_len;
  }
  if b_len == 0 {
    return a_len;
  }
  let mut prev_row: Vec<usize> = (0..=b_len).collect();
  let mut curr_row = vec![0; b_len + 1];
  for i in 1..=a_len {
    curr_row[0] = i;
    for j in 1..=b_len {
      let cost = if a_chars[i - 1] == b_chars[j - 1] {
        0
      } else {
        1
      };
      curr_row[j] = (curr_row[j - 1] + 1)
        .min(prev_row[j] + 1)
        .min(prev_row[j - 1] + cost);
    }
    std::mem::swap(&mut prev_row, &mut curr_row);
  }
  prev_row[b_len]
}

fn did_you_mean(name: &str, candidates: &[String]) -> Option<String> {
  let name_lower = name.to_lowercase();
  candidates
    .iter()
    .filter_map(|c| {
      let d = levenshtein_distance(&name_lower, &c.to_lowercase());
      if d <= 3 { Some((d, c.clone())) } else { None }
    })
    .min_by_key(|(d, _)| *d)
    .map(|(_, c)| c)
}

/// Extract the universe level from a type, resolving through Var aliases.
/// Uses a visiting set to prevent infinite recursion on alias chains.
fn ensure_sort(typ: &Term, scope: &Scope) -> Result<(Term, u64), TypeError> {
  match typ {
    Term::Sort { level } => Ok((typ.clone(), *level)),
    Term::Var { name } if name.is_name() => {
      let mut visited = std::collections::HashSet::new();
      let mut current = typ.clone();
      loop {
        match &current {
          Term::Sort { level } => return Ok((current.clone(), *level)),
          Term::Ctx { term, .. } => {
            current = (**term).clone();
          }
          Term::Var { name } if name.is_name() => {
            let def_path = name.to_path().unwrap();
            if !visited.insert(def_path.clone()) {
              return Err(TypeError::ExpectedType(typ.clone(), SourceRange::default()));
            }
            let def = scope
              .global()
              .find_ref(&def_path)
              .ok_or(TypeError::ExpectedType(typ.clone(), SourceRange::default()))?;
            current = def.typ().clone();
          }
          _ => return Err(TypeError::ExpectedType(typ.clone(), SourceRange::default())),
        }
      }
    }
    Term::Ctx { term, .. } => ensure_sort(term, scope),
    _ => Err(TypeError::ExpectedType(typ.clone(), SourceRange::default())),
  }
}

/// Check that actual is a subtype of expected under cumulativity.
/// Sort u is a subtype of Sort v iff u <= v.
pub fn check_cumulativity(actual: &Term, expected: &Term, scope: &Scope) -> Result<(), TypeError> {
  match (actual, expected) {
    (Term::Sort { level: u }, Term::Sort { level: v }) if u <= v => Ok(()),
    (Term::Sort { .. }, Term::Sort { .. }) => Err(TypeError::ExpectedType(
      actual.clone(),
      SourceRange::default(),
    )),
    _ => {
      let _ = match_resolve_type(actual, expected, scope)?;
      Ok(())
    }
  }
}

fn check_strict_pos(type_name: &ModulePath, typ: &Term, polarity: bool) -> Result<(), TypeError> {
  match typ {
    Term::Var { name } => {
      if name.to_path().as_ref() == Some(type_name) {
        if polarity {
          Ok(())
        } else {
          Err(TypeError::Generic(
            format!("non-strictly positive occurrence of {}", type_name),
            SourceRange::default(),
          ))
        }
      } else {
        Ok(())
      }
    }
    Term::App { fun, arg } => {
      check_strict_pos(type_name, fun, polarity)?;
      check_strict_pos(type_name, arg, polarity)
    }
    Term::Pi { arg, ret, .. } => {
      check_strict_pos(type_name, arg, !polarity)?;
      check_strict_pos(type_name, ret, polarity)
    }
    Term::Forall { typ, body, .. } => {
      check_strict_pos(type_name, typ, !polarity)?;
      check_strict_pos(type_name, body, polarity)
    }
    _ => Ok(()),
  }
}

fn check_strict_positivity(ind: &Inductive) -> Result<(), TypeError> {
  let name = ind.name();
  for cons in ind.constructors() {
    for param in cons.params() {
      check_strict_pos(name, param.typ(), true)?;
    }
  }
  Ok(())
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
    TypeError::Instance(value, SourceRange::default())
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
        Multiplicity::Zero => {
          return Err(TypeError::ErasedUsedAtRuntime(
            name.clone(),
            SourceRange::default(),
          ));
        }
        Multiplicity::Linear => {
          if *count >= 1 {
            return Err(TypeError::LinearUsedMultipleTimes(
              name.clone(),
              SourceRange::default(),
            ));
          }
        }
        Multiplicity::Affine => {
          if *count >= 1 {
            return Err(TypeError::AffineUsedMultipleTimes(
              name.clone(),
              SourceRange::default(),
            ));
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

  /// Remove a variable from tracking (used to clean up after match branches)
  pub fn remove(&mut self, name: &Identifier) {
    self.usages.remove(name);
  }

  /// Verify all linear variables were used exactly once
  pub fn verify_linear_usage(&self) -> Result<(), TypeError> {
    for (name, (mult, count)) in &self.usages {
      if *mult == Multiplicity::Linear && *count != 1 {
        return Err(TypeError::LinearUnused(
          name.clone(),
          SourceRange::default(),
        ));
      }
    }
    Ok(())
  }

  /// Verify a single variable was used according to its multiplicity.
  /// Used in Lam branches to avoid checking inner lambda params (scope leak fix).
  pub fn verify_var(&self, name: &Identifier) -> Result<(), TypeError> {
    if let Some((mult, count)) = self.usages.get(name) {
      if *mult == Multiplicity::Linear && *count != 1 {
        return Err(TypeError::LinearUnused(
          name.clone(),
          SourceRange::default(),
        ));
      }
    }
    Ok(())
  }
}

pub fn derive_instance_key(class_def: &ClassDefRef, typ: &Term) -> Result<InstanceKey, TypeError> {
  use FreeVar::*;
  use InstanceError::*;
  let class_params = &class_def.class.params;
  let free_vars: FreeVars = class_params
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
    // Try to resolve undetermined params using class defaults
    let mut resolved_args = args.clone();
    let mut still_missing = Vec::new();
    for name in errs {
      if let Some(class_param) = class_def.class.params.iter().find(|p| p.name == name) {
        if let Some(ref default) = class_param.default {
          resolved_args.push(param(name, (**default).clone()));
        } else {
          still_missing.push(name);
        }
      } else {
        still_missing.push(name);
      }
    }
    if !still_missing.is_empty() {
      Err(MissingTypeArgs(still_missing))?;
    }
    // Use the resolved args (with defaults filled in)
    let key = InstanceKey::new(
      class_def.class.name().clone(),
      class_def.class.constraints.clone(),
      resolved_args,
    );
    return Ok(key);
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

  // Collect type variables from explicit params (e.g. instance {R : Type} ...)
  // or infer them from instance args and constraints
  let mut type_vars: crate::Map<Identifier, Term> = crate::Map::new();
  let default_type = sort1();

  if !instance.params.is_empty() {
    // Use explicitly declared forall params
    for param in &instance.params {
      type_vars.insert(param.name.clone(), (*param.typ).clone());
    }
  } else {
    // Infer type variables from constraints and instance args
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
  // Add instance constraints FIRST so they propagate through with_forall calls
  if !instance.constraints.is_empty() {
    scope = scope.with_constraints(instance.constraints.clone());
  }
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
      let typ = match_resolve_type(&class_def_type, &impl_def.typ, &scope)?;
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
  // Collect bound names from the type to avoid clashes
  let reserved = collect_bound_names(&typ);
  let mut result = typ;
  for (name, param_typ) in vars {
    let name = if reserved.contains(name) {
      let mut fresh = Identifier::new(format!("{}_i", name.as_str()));
      while reserved.contains(&fresh) {
        fresh = fresh.rename();
      }
      fresh
    } else {
      name.clone()
    };
    result = Forall {
      name,
      typ: Box::new(param_typ.clone()),
      body: Box::new(result),
    };
  }
  result
}

/// Collect all Forall-bound variable names in a term.
fn collect_bound_names(term: &Term) -> crate::Set<Identifier> {
  let mut names = crate::empty_set();
  collect_bound_names_inner(term, &mut names);
  names
}

fn collect_bound_names_inner(term: &Term, names: &mut crate::Set<Identifier>) {
  match term {
    Term::Forall { name, typ, body } => {
      names.insert(name.clone());
      collect_bound_names_inner(typ, names);
      collect_bound_names_inner(body, names);
    }
    Term::Pi { arg, ret, .. } => {
      collect_bound_names_inner(arg, names);
      collect_bound_names_inner(ret, names);
    }
    Term::App { fun, arg } => {
      collect_bound_names_inner(fun, names);
      collect_bound_names_inner(arg, names);
    }
    _ => {}
  }
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
  if !left.is_known() {
    return Ok(right.clone());
  }
  if let Var { name } = right
    && name.is_id()
  {
    return Ok(left.clone());
  }
  let free_vars = FreeVars::from_locals(scope);
  let free_vars = match_determine_type_vars_with_scope(left, right, free_vars, scope)?;
  let typ = apply_free_type_vars(left.clone(), &free_vars);
  Ok(typ)
}

pub fn match_determine_type_vars<'a>(
  left: &'a Term,
  right: &'a Term,
  mut free_vars: FreeVars<'a>,
) -> Result<FreeVars<'a>, TypeError> {
  let similar = match_resolve_type_inner(left, right, &mut free_vars, None, &mut empty_set());
  if similar {
    Ok(free_vars)
  } else {
    Err(TypeError::TypeMismatch {
      expected: left.clone(),
      actual: right.clone(),
      loc: SourceRange::default(),
    })
  }
}

/// Version of `match_determine_type_vars` with scope access for def alias resolution.
pub fn match_determine_type_vars_with_scope<'a>(
  left: &'a Term,
  right: &'a Term,
  mut free_vars: FreeVars<'a>,
  scope: &'a Scope<'a>,
) -> Result<FreeVars<'a>, TypeError> {
  let similar =
    match_resolve_type_inner(left, right, &mut free_vars, Some(scope), &mut empty_set());
  if similar {
    Ok(free_vars)
  } else {
    Err(TypeError::TypeMismatch {
      expected: left.clone(),
      actual: right.clone(),
      loc: SourceRange::default(),
    })
  }
}

fn apply_free_type_vars(typ: Term, free_vars: &FreeVars) -> Term {
  let typ = substitute_forall(typ, free_vars);

  // Filter keep_vars: skip ~-suffixed vars (temporary renamed forall vars
  // created by pi_of_forall_types_with_mult for matching only — they must
  // not leak into stored types seen by the evaluator).
  let keep = free_vars.keep_vars();
  let filtered: Map<Identifier, &Term> = keep
    .iter()
    .filter(|(id, _)| !id.as_str().contains('~'))
    .map(|(k, v)| ((*k).clone(), *v))
    .collect();
  let filtered_refs: Map<&Identifier, &Term> = filtered.iter().map(|(k, v)| (k, *v)).collect();
  add_forall_to_type(typ, &filtered_refs)
}

/// Try to resolve a `NameRef` through def_refs to expand type aliases.
/// Returns `None` if the name can't be resolved, is a function (Lam), or
/// the definition is already being resolved (recursion guard).
/// Returns a cloned Term for comparison (caller must own it).
fn resolve_def_alias(
  name: &NameRef,
  scope: Option<&Scope>,
  visiting: &mut Set<ModulePath>,
) -> Option<Term> {
  let path = name.clone().to_path()?;
  if !visiting.insert(path.clone()) {
    // Already visiting this path — cycle detected, stop
    return None;
  }
  let scope = scope?;
  let def_ref = scope.global().find_ref(&path)?;
  match def_ref.term() {
    // Lam means it's a function definition, not a simple type alias — don't expand
    Term::Lam { .. } => None,
    // Type alias body: clone for comparison
    body => Some(body.clone()),
  }
}

/// Strip implicit (Forall) params from a term, returning the underlying body.
fn strip_implicit_params(term: &Term) -> Term {
  match term {
    Term::Forall { body, .. } => strip_implicit_params(body),
    _ => term.clone(),
  }
}

/// Try to expand a def type alias applied to arguments.
/// e.g., Lens S T A B → (A -> F B) -> S -> F T
fn try_expand_def_alias(typ: &Term, scope: &Scope) -> Option<Term> {
  // Unwrap Ctx wrapper
  let typ = match typ {
    Term::Ctx { term, .. } => term,
    _ => typ,
  };
  // Collect the head Var and args from App chain
  let (head, args) = collect_apps(typ);
  let head_name = match head {
    Term::Var { name } => name.clone(),
    _ => return None,
  };
  let path = head_name.to_path()?;
  let def_ref = scope.global().find_ref(&path)?;

  // Get the body term, stripping Forall and Ctx layers from the term
  let body = strip_implicit_params(def_ref.term());
  let mut body = {
    let mut b = body.clone();
    while let Term::Ctx { term, .. } = &b {
      b = (**term).clone();
    }
    b
  };
  while let Term::Forall { body: b, .. } = body {
    body = *b;
  }

  // Try substitution via Lambdas (for defs with explicit params)
  let lambda_result = substitute_lam_args(&body, &args);

  // If substitution didn't change the body (no Lam params), try
  // substituting args into Forall-bound variables positionally
  let mut result = if lambda_result == body && !args.is_empty() {
    substitute_forall_params(&body, scope, &args)
  } else {
    lambda_result
  };

  // Strip a single Ctx wrapper from the result
  if let Term::Ctx { term, .. } = result {
    result = *term;
  }

  // After type-checking, the def's type loses Forall bindings for phantom
  // type params. Reconstruct them from free vars in the expanded body.
  let binding_vars = expand_forall_bindings(&result, scope);
  if !binding_vars.is_empty() {
    result = wrap_with_foralls(result, &binding_vars);
  }

  Some(result)
}

/// Try substitution via positional args into free Forall variables when
/// the def has no Lam params but has forall-bound vars in the body.
fn substitute_forall_params(body: &Term, scope: &Scope, args: &[Term]) -> Term {
  // Strip Ctx wrapper from body (type-checked terms have Ctx wrappers)
  let body = match body {
    Term::Ctx { term, .. } => term,
    _ => body,
  };
  let binding_vars = expand_forall_bindings(body, scope);
  if binding_vars.is_empty() {
    return body.clone();
  }
  let mut result = body.clone();
  let forall_names: Vec<Identifier> = binding_vars.keys().cloned().collect();
  for (param_name, arg) in forall_names.iter().zip(args.iter()) {
    result = substitute(result, &NameRef::Id(param_name.clone()), arg);
  }
  result
}

/// Given an expanded type, find the free variables that should be
/// Forall-bound (i.e., type variables, not known types).
fn expand_forall_bindings(term: &Term, scope: &Scope) -> crate::Map<Identifier, Term> {
  let known_names: crate::Set<ModulePath> = scope
    .global()
    .all_known_names()
    .into_iter()
    .cloned()
    .collect();
  let free = free_vars(term, &empty_set());
  let mut bindings = crate::Map::new();
  for id in free {
    let path = ModulePath::single(id.clone());
    if !known_names.contains(&path) {
      bindings.insert(id, sort1());
    }
  }
  bindings
}

/// Collect the head and arguments of an App chain: App(App(head, a1), a2) → (head, [a1, a2])
fn collect_apps(term: &Term) -> (&Term, Vec<Term>) {
  match term {
    Term::App { fun, arg } => {
      let (head, mut args) = collect_apps(fun);
      args.push(*arg.clone());
      (head, args)
    }
    Term::Ctx { term, .. } => collect_apps(term),
    _ => (term, vec![]),
  }
}

/// Substitute arguments for Lam params: Lam(x, Lam(y, body)) + [a, b] → body[x:=a, y:=b]
fn substitute_lam_args(body: &Term, args: &[Term]) -> Term {
  let mut current = body.clone();
  for arg in args.iter().rev() {
    // Strip any Ctx wrappers that might have been added by type checking
    while let Term::Ctx { term, .. } = &current {
      current = (**term).clone();
    }
    current = match current {
      Term::Lam {
        param: Par::P(p),
        body,
        ..
      } => substitute((*body).clone(), &NameRef::Id(p.name.clone()), arg),
      _ => break,
    };
  }
  current
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
      // Both are Forall-bound names from the same scope context — unifiable
      if let (NameRef::Id(id1), NameRef::Id(id2)) = (n1, n2) {
        if free_vars.keep_vars().contains_key(id1) && free_vars.keep_vars().contains_key(id2) {
          return true;
        }
      }
      if n1.is_name() {
        n1.clone().to_path() == n2.clone().to_path()
      } else {
        n1 == n2
      }
    }
    (Sort { .. }, Sort { .. }) => true,
    _ => left == right,
  }
}
fn match_resolve_type_inner<'a>(
  left: &'a Term,
  right: &'a Term,
  free_vars: &mut FreeVars<'a>,
  scope: Option<&Scope<'a>>,
  visiting: &mut Set<ModulePath>,
) -> bool {
  use FreeVar::*;
  match (left, right) {
    (Forall { name, typ, body }, _) => {
      // When both sides have Forall, strip them pairwise
      if let Term::Forall {
        name: r_name,
        typ: r_typ,
        body: r_body,
      } = right
      {
        free_vars.insert_free_var(name, Unknown { typ });
        free_vars.add_var_to_keep(r_name, r_typ);
        match_resolve_type_inner(body, r_body, free_vars, scope, visiting)
      } else {
        free_vars.insert_free_var(name, Unknown { typ });
        let result = match_resolve_type_inner(body, right, free_vars, scope, visiting);
        // When left has Forall wrappers (implicit params) and the body is a
        // constructor return type (App) rather than a Pi, the body may need
        // to match the Pi's return type rather than the whole Pi structure.
        // The Forall-absorbed implicit arguments consume the Pi's arg.
        if !result {
          if let Term::Pi { ret, .. } = right {
            return match_resolve_type_inner(body, ret, free_vars, scope, visiting);
          }
        }
        result
      }
    }
    (_, Forall { name, typ, body }) => {
      free_vars.add_var_to_keep(name, typ);
      match_resolve_type_inner(left, body, free_vars, scope, visiting)
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
      let arg = match_resolve_type_inner(a_arg, b_arg, free_vars, scope, visiting);
      let ret = match_resolve_type_inner(a_ret, b_ret, free_vars, scope, visiting);
      let b = arg && ret;
      b
    }
    (App { fun: f1, arg: a1 }, App { fun: f2, arg: a2 }) => {
      let f_res = match_resolve_type_inner(f1, f2, free_vars, scope, visiting);
      let a_res = match_resolve_type_inner(a1, a2, free_vars, scope, visiting);
      f_res && a_res
    }
    (Hole, _) => true,
    (_, Hole) => true,
    (Ctx { loc: _, term }, _) => match_resolve_type_inner(term, right, free_vars, scope, visiting),
    (_, Ctx { loc: _, term }) => match_resolve_type_inner(left, term, free_vars, scope, visiting),
    (Var { name: n1 }, Var { name: n2 }) => {
      let name_eq = if n1.is_name() {
        match n1.as_id() {
          Some(id) if check_free_vars(id, right, free_vars) => true,
          _ => n1.clone().to_path() == n2.clone().to_path(),
        }
      } else {
        n1 == n2
      };
      if name_eq {
        true
      } else {
        // Try resolving left as a type alias using compare_types
        // (compare_types doesn't require `'a` lifetimes)
        match resolve_def_alias(n1, scope, visiting) {
          Some(body) => compare_types(&body, right, free_vars),
          None => false,
        }
      }
    }
    (Sort { level: _ }, Var { name: Id(name) }) => {
      if check_free_vars(name, left, free_vars) {
        true
      } else {
        let s = name.as_str();
        s == "Type" || s == "Prop" || s == "Sort"
      }
    }
    (Var { name: Id(name) }, Sort { level: _ }) => {
      if check_free_vars(name, right, free_vars) {
        true
      } else {
        let s = name.as_str();
        s == "Type" || s == "Prop" || s == "Sort"
      }
    }
    (Var { name: Id(name) }, _) => {
      if check_free_vars(name, right, free_vars) {
        true
      } else {
        match resolve_def_alias(&NameRef::Id(name.clone()), scope, visiting) {
          Some(body) => compare_types(&body, right, free_vars),
          None => false,
        }
      }
    }
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
  let defined = match scope.find_var_ref_of(nref, &expected_type) {
    Ok(var_ref) => var_ref,
    Err(_) if !scope.constraints().is_empty() => scope
      .global()
      .find_any_name_ref_with_constraints(nref, &expected_type, scope.constraints())?,
    Err(e) => return Err(e.into()),
  };
  let mut method_constraints: Option<&Vec<TypeConstraint>> = None;
  match defined {
    VarRef::UpdateRef {
      new_path,
      term: _,
      typ: _,
      method_constraints: mc,
    } => {
      method_constraints = mc;
      term = Var {
        name: new_path.clone().into(),
      };
    }
    VarRef::ClassMethod { .. } => {
      // Constraint guarantees an instance exists, but the
      // concrete type is abstract. Keep the original term.
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
  } else if let Ok(typ) = match_resolve_type(&defined_type, &expected_type, scope) {
    // Check per-method constraints when expected type is known
    if let Some(constraints) = method_constraints
      && !constraints.is_empty()
    {
      let free_vars = FreeVars::from_locals(scope);
      if let Ok(free_vars) =
        match_determine_type_vars_with_scope(&defined_type, &expected_type, free_vars, scope)
      {
        use FreeVar::*;
        let keep_vars = free_vars.keep_vars();
        let var_map: Map<Identifier, &Term> = free_vars
          .free_vars()
          .iter()
          .filter_map(|(name, fv)| match fv {
            Detected { term, .. } => Some(((*name).clone(), *term)),
            _ => None,
          })
          .collect();
        // Skip check if any mapped type is still an unresolved type variable
        // (happens during instance body type-checking where types are generic)
        let all_concrete = var_map.values().all(|t| {
          if let Term::Var { name } = t
            && let Some(id) = name.as_id()
          {
            !keep_vars.contains_key(id)
          } else {
            true
          }
        });
        if all_concrete && !var_map.is_empty() {
          if let Err(msg) = check_method_constraints(scope.global(), constraints, &var_map) {
            return Err(TypeError::Generic(msg, SourceRange::default()));
          }
        }
      }
    }
    Ok(typed_term(term, typ))
  } else if let Some(expanded) = try_expand_def_alias(&defined_type, scope) {
    let typ = match_resolve_type(&expanded, &expected_type, scope)?;
    Ok(typed_term(term, typ))
  } else {
    Err(FreeVarMismatch {
      name: nref.clone(),
      actual: defined_type.clone(),
      expected: expected_type,
      locals: scope.local_bindings(),
      loc: SourceRange::default(),
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
    Ctx { term, .. } => extract_first_name(term),
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
    Var { name } if name.is_name() && !known_names.contains(&name.to_path().unwrap()) => name
      .as_id()
      .map(|id| set_of(vec![id.clone()].into_iter()))
      .unwrap_or(empty_set()),
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
    Term::Quote { term } => free_vars(term, known_names),
    Lit {
      value: Literal::Term(t),
    } => free_vars(t, known_names),
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
      } else if name.as_str().contains('~') {
        // Strip ~-renamed foralls that were not detected — these are
        // temporary renames from pi_of_forall_types_with_mult that must
        // not leak into stored types or result types seen by the evaluator.
        // Also clean up Var references to this variable in the body.
        let original = Identifier::new(name.as_str().trim_end_matches('~').to_string());
        let body = substitute(
          *body,
          &Id(name.clone()),
          &Var {
            name: NameRef::Id(original),
          },
        );
        substitute_forall(body, free_vars)
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
pub fn add_params_to_scope<'a>(
  params: &'a [Param],
  args: &'a [Term],
  mut scope: Scope<'a>,
) -> Scope<'a> {
  for (param, arg) in params.iter().zip(args.iter()) {
    scope = scope.with_local_var(&param.name, arg);
  }
  scope
}

pub fn pi_of_forall_types(arg_type: Term, return_type: Term) -> Term {
  pi_of_forall_types_with_mult(arg_type, return_type, Multiplicity::Many)
}

pub fn pi_of_forall_types_with_mult(arg_type: Term, return_type: Term, mult: Multiplicity) -> Term {
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
  let fun_type = pi_with_mult(arg_type, return_type, mult);
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

fn type_name_from_var(name: &NameRef) -> Option<&str> {
  match name {
    NameRef::Id(id) => Some(id.as_str()),
    NameRef::P(path) if path.len() == 1 => Some(path.last().as_str()),
    _ => None,
  }
}

fn resolve_num_literal_type(
  expected: &Term,
  default: NumSuffix,
  _scope: &Scope,
) -> Result<NumSuffix, TypeError> {
  if default != NumSuffix::I64 {
    return Ok(default);
  }
  if let Term::Var { name } = expected
    && let Some(name_str) = type_name_from_var(name)
  {
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
    && let Some(name_str) = type_name_from_var(name)
  {
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
      loc: SourceRange::default(),
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
  let term = crate::eval::apply_dot_macro_recursive(term);
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
      // First check: infer arg type (counts usage only when tracking is active)
      let (arg, inferred_type) =
        match type_check_with_env(arg.clone(), Hole, &scope, usage, track_usage) {
          Ok(tt) => tt.to_tuple(),
          Err(err) => {
            // Propagate linear type errors; suppress other (type inference) errors
            if matches!(
              err,
              TypeError::LinearUsedMultipleTimes(..)
                | TypeError::LinearUnused(..)
                | TypeError::AffineUsedMultipleTimes(..)
                | TypeError::ErasedUsedAtRuntime(..)
            ) {
              return Err(err);
            }
            (arg, Hole)
          }
        };
      let fun_type = pi_of_forall_types(inferred_type.clone(), expected_type.clone());
      // Check function against expected type with the inferred arg type
      let (fun, fun_type) =
        type_check_with_env(*fun, fun_type, &scope, usage, track_usage)?.to_tuple();
      let (fun_vars, fun_typ_pi) = unwrap_forall(fun_type);
      let mut fun_typ_pi = try_expand_def_alias(&fun_typ_pi, &scope).unwrap_or(fun_typ_pi);
      // Unwrap a single Ctx wrapper from the result
      if let Term::Ctx { term, .. } = &fun_typ_pi {
        fun_typ_pi = (**term).clone();
      }
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
        // Unwrap Ctx wrappers before checking for struct literals
        // (type_check_with_env from step (a) may wrap the literal in a Ctx)
        let is_struct_lit = {
          let mut t = &arg;
          while let Term::Ctx { term, .. } = t {
            t = term;
          }
          matches!(
            t,
            Term::Lit {
              value: Literal::StructLit { .. }
            }
          )
        };
        // Optimization: skip second full term walk when step (a) already
        // inferred the same type the Pi expects.
        let (arg, _) = if is_struct_lit || arg_type.is_known() {
          if arg_type.is_known() && inferred_type == arg_type {
            (arg, arg_type)
          } else {
            type_check_with_env(arg, arg_type, &scope, usage, false)?.to_tuple()
          }
        } else {
          (arg, arg_type)
        };
        let term = app(fun, arg);
        let ret_type = *ret.clone();
        let ret_type = add_forall_to_type(ret_type, &fun_forall_vars);
        Ok(typed_term(term, ret_type))
      } else if fun_vars.is_empty() {
        // Constructor with only Forall-wrapped implicit params (like refl).
        // The Foralls were substituted by match_resolve_type and the
        // explicit argument was absorbed by one of the Foralls.
        // The resulting type is the constructor's return type.
        let term = app(fun, arg);
        Ok(typed_term(term, fun_typ_pi))
      } else {
        Err(ExpectedPi(fun_typ_pi.clone(), SourceRange::default()))
      }
    }
    Lit { value } => match value {
      Literal::StructLit { ref fields } => {
        let struct_type = {
          if let Var { name } = &expected_type
            && let Some(name) = name.to_path()
          {
            Some(name.clone())
          } else {
            None
          }
        };
        if struct_type.is_none() && expected_type.is_known() {
          return Err(TypeError::ExpectedStructName {
            found: expected_type.clone(),
            loc: SourceRange::default(),
          });
        }
        if let Some(ref struct_name) = struct_type {
          let ind = scope.find_inductive(struct_name)?;
          let mk_cons =
            ind
              .constructors
              .first()
              .ok_or_else(|| TypeError::StructNoConstructors {
                loc: SourceRange::default(),
              })?;
          if fields.len() > mk_cons.params.len() {
            return Err(TypeError::StructTooManyFields {
              max: mk_cons.params.len(),
              found: fields.len(),
              loc: SourceRange::default(),
            });
          }
          for Param { name, typ, .. } in mk_cons.params.iter() {
            if let Some(term) = fields.get(name) {
              type_check_with_env(term.clone(), *typ.clone(), &scope, usage, track_usage)?;
            } else if !ind.defaults.contains_key(name) {
              return Err(MissingField(name.clone(), SourceRange::default()));
            }
          }
          let args: Vec<Option<Term>> = mk_cons
            .params
            .iter()
            .map(|p| {
              Ok(Some(
                fields
                  .get(&p.name)
                  .cloned()
                  .or_else(|| ind.defaults.get(&p.name).cloned())
                  .ok_or_else(|| MissingField(p.name.clone(), SourceRange::default()))?,
              ))
            })
            .collect::<Result<Vec<_>, TypeError>>()?;
          let con = Term::Con(Constructor {
            name: id("mk"),
            typ_name: struct_name.clone(),
            args,
            num_args: mk_cons.params.len(),
          });
          Ok(typed_term(con, expected_type.clone()))
        } else {
          Ok(typed_term(Lit { value }, expected_type))
        }
      }
      Literal::StructUpdate { base, fields } => {
        // Desugar { id with field := val, ... } to:
        //   match id { mk orig_fields => mk new_fields }
        let base_term = Term::Var {
          name: NameRef::Id(base),
        };
        let (base, base_type) =
          type_check_with_env(base_term, Hole, &scope, usage, track_usage)?.to_tuple();
        if let Some((ind_name, _ind_args)) = extract_first_name(&base_type) {
          let ind = scope.find_inductive(&ind_name)?;
          let mk_cons =
            ind
              .constructors
              .first()
              .ok_or_else(|| TypeError::StructNoConstructors {
                loc: SourceRange::default(),
              })?;
          // Generate fresh pattern variables
          let fresh_names: Map<Identifier, Identifier> = mk_cons
            .params
            .iter()
            .map(|p| {
              let fresh = p.name.rename();
              (p.name.clone(), fresh)
            })
            .collect();
          let pat_args: Vec<Identifier> = mk_cons
            .params
            .iter()
            .map(|p| fresh_names.get(&p.name).unwrap().clone())
            .collect();
          // Build body with fresh variable references (will be bound by match pattern)
          let mut body_args: Vec<Option<Term>> = Vec::new();
          for param in mk_cons.params.iter() {
            let fresh = fresh_names.get(&param.name).unwrap();
            let val: Term = if let Some(override_term) = fields.get(&param.name) {
              override_term.clone()
            } else {
              Term::Var {
                name: NameRef::Id(fresh.clone()),
              }
            };
            body_args.push(Some(val));
          }
          let body = Term::Con(Constructor {
            name: id("mk"),
            typ_name: ind_name.clone(),
            args: body_args,
            num_args: mk_cons.params.len(),
          });
          let match_case = case(id("mk"), pat_args, body);
          let match_expr = match_term(base, vec![match_case]);
          return type_check_with_env(
            match_expr,
            expected_type.clone(),
            &scope,
            usage,
            track_usage,
          );
        }
        Err(TypeError::StructUpdateExpectedInductive {
          found: base_type,
          loc: SourceRange::default(),
        })
      }
      Literal::Match {
        ref value,
        ref cases,
      } => {
        let con = type_check_with_env(*value.clone(), Hole, &scope, usage, track_usage)?;
        let (_, con_type) = unwrap_forall(con.typ().clone());

        if let Some((ind_name, ind_args)) = extract_first_name(&con_type) {
          let ind = scope.find_inductive(&ind_name)?;
          let ind_params = &ind.params;
          if ind_params.len() != ind_args.len() {
            return Err(InductiveMismatch {
              name: ind_name,
              params: ind_params.clone(),
              args: ind_args,
              loc: SourceRange::default(),
            });
          }
          let mut branch_t = expected_type.clone();
          let mut new_cases = Vec::new();
          for mcase in cases {
            if mcase.name.as_str() == "_" {
              if !mcase.args.is_empty() {
                return Err(Generic(
                  "wildcard pattern cannot bind variables".to_string(),
                  SourceRange::default(),
                ));
              }
              let t = type_check_with_env(
                *mcase.value.clone(),
                branch_t.clone(),
                &scope,
                usage,
                track_usage,
              )?;
              if let Ok(typ) = match_resolve_type(&branch_t, t.typ(), &scope) {
                branch_t = typ;
              } else {
                return Err(MismatchingBranches(
                  branch_t,
                  t.typ().clone(),
                  SourceRange::default(),
                ));
              }
              new_cases.push(case(id("_"), vec![], t.term().clone()));
            } else if let Some(ind_cons) = ind.find_cons(&mcase.name) {
              let mut scope = scope.clone();
              if ind_cons.params.len() != mcase.args.len() {
                return Err(ConstructorMismatch {
                  params: ind_cons.params.clone(),
                  args: mcase.args.clone(),
                  loc: SourceRange::default(),
                });
              }
              for (name, param) in mcase.args.iter().zip(ind_cons.params.iter()) {
                if name.as_str() == "_" {
                  continue;
                }
                let typ = substitute_params(*param.typ.clone(), ind_params, &ind_args);
                scope = add_params_to_scope(ind_params, &ind_args, scope);
                scope = scope.with_type_owned(name, typ);
                // Register pattern variable with its constructor param's multiplicity
                usage.register(name.clone(), param.mult.clone());
              }
              let t = type_check_with_env(
                *mcase.value.clone(),
                branch_t.clone(),
                &scope,
                usage,
                track_usage,
              )?;
              // Remove pattern variables from usage tracking after each branch
              for (name, _) in mcase.args.iter().zip(ind_cons.params.iter()) {
                if name.as_str() != "_" {
                  usage.remove(name);
                }
              }
              if let Ok(typ) = match_resolve_type(&branch_t, t.typ(), &scope) {
                branch_t = typ;
              } else {
                return Err(MismatchingBranches(
                  branch_t,
                  t.typ().clone(),
                  SourceRange::default(),
                ));
              }
              new_cases.push(case(
                mcase.name.clone(),
                mcase.args.clone(),
                t.term().clone(),
              ));
            } else {
              let ctor_names: Vec<Identifier> = ind
                .constructors
                .iter()
                .map(|c| c.name().last().clone())
                .collect();
              return Err(ConstructorUnknown(
                mcase.name.clone(),
                ctor_names,
                SourceRange::default(),
              ));
            }
          }
          Ok(typed_term(
            match_term(con.term().clone(), new_cases),
            branch_t.clone(),
          ))
        } else {
          Err(ExpectedInductive(con.typ().clone(), SourceRange::default()))
        }
      }
      Literal::If { value, then, els } => {
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
            SourceRange::default(),
          ))
        }
      }
      Literal::Str { value: _ } => {
        let typ = match_resolve_type(&var("String"), &expected_type, &scope)?;
        Ok(typed_term(Lit { value }, typ))
      }
      Literal::Char { value: _ } => {
        let typ = match_resolve_type(&var("Char"), &expected_type, &scope)?;
        Ok(typed_term(Lit { value }, typ))
      }
      Literal::Num { value: val, suffix } => {
        if suffix.is_int() {
          let target = resolve_num_literal_type(&expected_type, suffix, &scope)?;
          let converted = convert_int_literal(val, target)?;
          Ok(typed_term(converted, var(target.type_name())))
        } else {
          let typ = match_resolve_type(&var("F64"), &expected_type, &scope)?;
          Ok(typed_term(Lit { value }, typ))
        }
      }
      Literal::Float { value: val, suffix } => {
        if suffix.is_float() {
          let target = resolve_float_literal_type(&expected_type, suffix, &scope)?;
          Ok(typed_term(
            Term::Lit {
              value: Literal::Float {
                value: val,
                suffix: target,
              },
            },
            var(target.type_name()),
          ))
        } else {
          let typ = match_resolve_type(&var("F64"), &expected_type, &scope)?;
          Ok(typed_term(Lit { value }, typ))
        }
      }
      Literal::Term(_) => {
        // Term values are evaluated at expansion time; not type-checked here
        Ok(typed_term(Lit { value }, Hole))
      }
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
        // Unwrap initial Foralls, expand def aliases, unwrap again
        let (initial_vars, inner_typ) = unwrap_forall(expected_type.clone());
        let mut typ = try_expand_def_alias(&inner_typ, &scope).unwrap_or(inner_typ);
        let (extra_vars, unwrapped) = unwrap_forall(typ);
        typ = unwrapped;
        // Merge initial and expansion forall owned bindings
        let mut owned_vars = initial_vars;
        for (k, v) in extra_vars {
          if !owned_vars.contains_key(&k) {
            owned_vars.insert(k, v);
          }
        }
        let vars = owned_vars.iter().collect();
        // Unwrap a single Ctx wrapper from the result
        if let Term::Ctx { term, .. } = &typ {
          typ = (**term).clone();
        }
        if let Pi {
          arg,
          ret,
          arg_name: _,
          ..
        } = typ
        {
          let arg_type = *arg.clone();
          let arg_type = add_forall_to_type(arg_type, &vars);
          let param_type = param.typ().clone();
          let arg_type = match_resolve_type(&arg_type, &param_type, &scope).map_err(|_| {
            TypeError::ArgumentMismatch {
              expected: *arg.clone(),
              actual: param_type.clone(),
              loc: SourceRange::default(),
            }
          })?;
          let arg_type = if !arg_type.is_known() {
            param_type
          } else {
            arg_type
          };
          // Register param in usage env (before body check)
          let registered_name = if let Par::P(ref p) = param {
            usage.register(p.name.clone(), p.mult.clone());
            Some(p.name.clone())
          } else {
            None
          };
          let scope = scope.with_param(&param);
          let return_type = *ret.clone();
          let return_type = add_forall_to_type(return_type, &vars);
          let (body, return_type) =
            type_check_with_env(*body.clone(), return_type, &scope, usage, track_usage)?.to_tuple();
          // Verify only this lambda's param — inner lambdas verify their own
          if let Some(name) = registered_name {
            usage.verify_var(&name)?;
          }
          let lam_type = pi_of_forall_types_with_mult(
            arg_type.clone(),
            return_type,
            param.multiplicity().clone(),
          );
          let term = lam_par(param.with_type(arg_type), body);
          Ok(typed_term(term, lam_type))
        } else {
          Err(TypeError::ExpectedPi(typ.clone(), SourceRange::default()))
        }
      } else {
        let param_type = param.typ();
        // Register param in usage env (before body check)
        let registered_name = if let Par::P(ref p) = param {
          usage.register(p.name.clone(), p.mult.clone());
          Some(p.name.clone())
        } else {
          None
        };
        let scope = scope.with_param(&param);
        let (body, body_type) =
          type_check_with_env(*body.clone(), Hole, &scope, usage, track_usage)?.to_tuple();
        // Verify only this lambda's param — inner lambdas verify their own
        if let Some(name) = registered_name {
          usage.verify_var(&name)?;
        }
        let lam_type = pi_with_mult(param_type.clone(), body_type, param.multiplicity().clone());
        let term = lam_par(param, body);
        Ok(typed_term(term, lam_type))
      }
    }
    Sort { level } => match &expected_type {
      Hole => Ok(typed_term(term, sort_u(level + 1))),
      Sort {
        level: expected_level,
      } if *expected_level > level =>
      // Cumulativity: Sort u can inhabit Sort v whenever v > u
      // Return the expected type to propagate level information
      {
        Ok(typed_term(term, expected_type.clone()))
      }
      _ => Err(TypeError::ExpectedType(term, SourceRange::default())),
    },
    Ntv { native: _ } => Ok(typed_term(term.clone(), expected_type.clone())),
    Con(Constructor {
      ref typ_name,
      ref args,
      ref name,
      num_args: _,
    }) => {
      let inductive = scope.find_inductive(typ_name)?;
      let cons = inductive.find_cons(name).ok_or_else(|| {
        let ctor_names: Vec<Identifier> = inductive
          .constructors
          .iter()
          .map(|c| c.name().last().clone())
          .collect();
        ConstructorUnknown(name.clone(), ctor_names, SourceRange::default())
      })?;
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
      let lam_types: Vec<Term> = arg_res.into_iter().map(|tt| tt.to_tuple().1).collect();
      let num_present = args.iter().filter(|a| a.is_some()).count();
      let ind_type = apps(
        mpvar(inductive.name().clone()),
        inductive.params().iter().map(|_| Hole).collect(),
      );
      // Use the constructor's declared type as the base
      let mut cons_type = cons.typ().clone();
      // Strip forall bindings (implicit type parameters)
      while let Forall { body, .. } = &cons_type {
        cons_type = *body.clone();
      }
      // Peel off Pi layers for each provided arg to get the return type
      for _ in 0..num_present {
        if let Pi { ret, .. } = cons_type {
          cons_type = *ret;
        } else {
          break;
        }
      }
      // For non-dependent constructors (return type = apps(name, param_refs)),
      // use the old ind_type with holes to allow type inference.
      // For dependent constructors (return type has specific values for indices),
      // keep the actual return type.
      let is_dependent = {
        let (actual_name, actual_args) = extract_first_name(&cons_type)
          .map(|(n, a)| (n, a))
          .unwrap_or((ModulePath::single(id("_")), vec![]));
        if actual_name == *inductive.name() && actual_args.len() == inductive.params().len() {
          // Check if any arg differs from a simple param variable reference
          actual_args
            .iter()
            .zip(inductive.params().iter())
            .any(|(arg, param)| match arg {
              Var { name: nref } => match nref.as_id() {
                Some(id) => id != &param.name,
                None => true,
              },
              _ => true,
            })
        } else {
          true
        }
      };
      let cons_type = if is_dependent {
        // Use the actual constructor type for dependent constructors
        if !lam_types.is_empty() && num_present < args.len() {
          pi_typs(lam_types, cons_type)
        } else {
          cons_type
        }
      } else {
        // Use the old behavior for non-dependent constructors
        if lam_types.is_empty() || num_present == args.len() {
          ind_type
        } else {
          pi_typs(lam_types, ind_type)
        }
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
      ref typ,
      ref body,
    } => {
      let typ_result = type_check_with_env(*typ.clone(), Hole, &scope, usage, track_usage)?;
      let body_result = type_check_with_env(*body.clone(), Hole, &scope, usage, track_usage)?;

      // Try .term first (handles Sort literals), fall back to .typ (handles Pi/App/Var types)
      let (_, typ_sort) =
        ensure_sort(&typ_result.term, &scope).or_else(|_| ensure_sort(typ_result.typ(), &scope))?;
      let (_, body_sort) = ensure_sort(&body_result.term, &scope)
        .or_else(|_| ensure_sort(body_result.typ(), &scope))?;

      let max_level = std::cmp::max(typ_sort, body_sort);
      Ok(typed_term(term, sort_u(max_level)))
    }
    Pi {
      ref arg,
      ref ret,
      arg_name: _,
      ..
    } => {
      if expected_type.is_type()
        || matches!(expected_type, Term::Sort { .. })
        || matches!(expected_type, Hole)
      {
        let arg_result = type_check_with_env(*arg.clone(), Hole, &scope, usage, track_usage)?;
        let ret_result = type_check_with_env(*ret.clone(), Hole, &scope, usage, track_usage)?;

        // Try .term first (handles Sort literals), fall back to .typ (handles Pi/App/Var types)
        let (_, arg_sort) = ensure_sort(&arg_result.term, &scope)
          .or_else(|_| ensure_sort(arg_result.typ(), &scope))?;
        let (_, ret_sort) = ensure_sort(&ret_result.term, &scope)
          .or_else(|_| ensure_sort(ret_result.typ(), &scope))?;

        let max_level = std::cmp::max(arg_sort, ret_sort);
        Ok(typed_term(term.clone(), sort_u(max_level)))
      } else {
        Err(TypeError::ExpectedType(
          expected_type.clone(),
          SourceRange::default(),
        ))
      }
    }
    Hole => Ok(typed_term(term, expected_type)),
    Ann { term, typ } => {
      let tt = type_check_with_env(*term, *typ, &scope, usage, track_usage)?;
      let typ = match_resolve_type(tt.typ(), &expected_type, &scope)?;
      Ok(typed_term(tt.term, typ))
    }
    Quote { term } => {
      // Quote terms should be consumed by macro expansion before reaching the type checker
      // Return Hole type as a placeholder
      let _ = type_check_with_env((*term).clone(), Hole, &scope, usage, track_usage)?;
      Ok(typed_term(*term, Hole))
    }
  }
}

pub fn type_check_decl(decl: Decl, scope: &Scope) -> Result<Decl, TypeError> {
  match decl {
    Decl::Use(ref u) => {
      scope.global().get_module(&u.module_path).ok_or_else(|| {
        TypeError::Scope(
          ScopeError::PathNotFound(u.module_path.clone()),
          SourceRange::default(),
        )
      })?;
      Ok(decl)
    }
    Decl::Def(def) => type_check_def(def, scope).map(Decl::Def),
    Decl::Ins(instance) => {
      let class = scope.find_inductive(&instance.class_name)?;
      type_check_instance(instance, class, scope).map(Decl::Ins)
    }
    Decl::Type(ref ind) => {
      check_strict_positivity(ind)?;
      Ok(decl)
    }
    Decl::DefMacro(_) => Ok(decl),
    Decl::DeclGen(_) => Ok(decl),
    Decl::Generated(inner) => {
      let mut checked = Vec::new();
      for d in inner {
        checked.push(type_check_decl(d, scope)?);
      }
      Ok(Decl::Generated(checked))
    }
    Decl::MacroCall { .. } => Ok(decl),
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
  let default_type = sort1();
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

pub fn type_check_decls(
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
  let (checked_decls, type_errors) = join_many_results(res);

  // Only run termination checking if there are no type errors
  if !type_errors.is_empty() {
    return (checked_decls, type_errors);
  }

  // Collect all Def declarations for termination checking
  let defs: Vec<&Def> = checked_decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Def(d) => Some(d),
      _ => None,
    })
    .collect();

  if defs.is_empty() {
    return (checked_decls, vec![]);
  }

  match check_termination_all(&defs) {
    Ok(()) => (checked_decls, vec![]),
    Err(e) => (checked_decls, vec![TypeError::Termination(e)]),
  }
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
  let default_type = sort1();
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
  let ind_params = ind.params().clone();
  for cons in ind.constructors.iter_mut() {
    let typ = cons.typ().clone();
    if is_class {
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
      cons.typ = pi_typs(class_defs, ret);
    } else {
      let all_free = free_vars(&typ, &empty_set());
      let extra_free = free_vars(&typ, &known_names);
      let mut new_typ = typ;
      let mut new_term = cons.term().clone();
      // Determine which inductive params need Forall wrappers on the term:
      // - Sort-typed params (type-level): always Forall-wrapped, stripped by Var resolution
      // - Non-Sort params: only Forall-wrapped when the constructor has no explicit
      //   params (like `refl` with 0 field params), so eval_app absorbs arguments.
      //   For constructors WITH explicit params (like `cons`), the Lams handle args.
      let has_explicit_params = !cons.params().is_empty();
      for p in ind_params.iter().rev() {
        if all_free.contains(&p.name) {
          let p_typ = params
            .get(&p.name)
            .cloned()
            .unwrap_or_else(|| (*p.typ).clone());
          let lam_param = Param {
            name: p.name.clone(),
            typ: Box::new(p_typ.clone()),
            mult: p.mult.clone(),
            default: p.default.clone(),
          };
          new_typ = forall(lam_param.clone(), new_typ);
          if matches!(*p.typ, Term::Sort { .. }) || !has_explicit_params {
            new_term = forall(lam_param, new_term);
          }
        }
      }
      let def_type = sort1();
      for fv in extra_free.iter() {
        if !params.contains_key(fv) && all_free.contains(fv) {
          new_typ = forall(param((*fv).clone(), def_type.clone()), new_typ);
          new_term = forall(param((*fv).clone(), def_type.clone()), new_term);
        }
      }
      cons.typ = new_typ;
      cons.set_term(new_term);
    }
  }
  ind
}
pub fn elaborate_instance(mut ins: Instance, known_names: &Set<&ModulePath>) -> Instance {
  for imp in ins.impls_map.values_mut() {
    let typ = imp.typ.clone();
    let free_vars = free_vars(&typ, known_names);
    let default_type = sort1();
    let vars = free_vars.iter().map(|i| (i, &default_type)).collect();
    imp.typ = add_forall_to_type(typ, &vars);
  }
  ins
}

pub fn elaborate_decl(decl: Decl, known_names: &Set<&ModulePath>) -> Decl {
  use Decl::*;

  match decl {
    Def(def) => Def(elaborate_def(def, known_names)),
    DefMacro(def) => DefMacro(elaborate_def(def, known_names)),
    DeclGen(gd) => DeclGen(DeclGenDef {
      name: gd.name,
      params: gd.params,
      decls: gd
        .decls
        .into_iter()
        .map(|d| elaborate_decl(d, known_names))
        .collect(),
      attributes: gd.attributes,
    }),
    Generated(inner) => Generated(
      inner
        .into_iter()
        .map(|d| elaborate_decl(d, known_names))
        .collect(),
    ),
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
  let benchmark = loaded.config.benchmark;
  let decls: Vec<SourceContext<Decl>> = if loaded.config.test_mode {
    decls
  } else {
    decls
      .into_iter()
      .filter(|ctx| match ctx.value() {
        Decl::Use(u) if u.has_cfg_test_attr() => false,
        Decl::Open(o) if o.has_cfg_test_attr() => false,
        _ => true,
      })
      .collect()
  };
  let elab_start = Instant::now();
  let decls = elaborate_decls(decls, loaded);
  let elab_dur = elab_start.elapsed();
  let macro_start = Instant::now();
  let decls = macro_expand::expand_macros(decls, loaded).map_err(TypeError::MacroExpansion)?;
  let macro_dur = macro_start.elapsed();
  let scope_start = Instant::now();
  let global = loaded.scope_of_decls(path, &decls);
  let scope_dur = scope_start.elapsed();

  let tc_start = Instant::now();
  let (oks, errs) = type_check_decls(decls.clone(), &global.scope());
  let tc_dur = tc_start.elapsed();
  if benchmark {
    eprintln!(
      "  [{}] elab={} macro={} scope={} tc={}",
      path,
      crate::term::module::format_duration(elab_dur),
      crate::term::module::format_duration(macro_dur),
      crate::term::module::format_duration(scope_dur),
      crate::term::module::format_duration(tc_dur),
    );
  }
  if !errs.is_empty() {
    Err(TypeError::Many(errs))
  } else {
    Ok(oks)
  }
}
