use std::fmt::Display;
use std::sync::Arc;

use crate::{
  Map, Set, empty_set,
  eval::termination::TerminationError,
  set_of,
  term::{
    ClassDefRef, Decl, DeclGenDef, Def, Identifier, Inductive, InductiveVariant, Instance,
    InstanceKey, Literal, ModulePath, Multiplicity,
    NameRef::{self, Id},
    Named, Param, SourceContext, SourceRange,
    Term::{self, App, Ctx, Forall, Hole, Lit, Pi, Sort, Var},
    TypeConstraint, Typed, forall,
    module::{LoadedModules, ScopeError, names_of_decls},
    mpt, param, pi_typs, sort1,
  },
  vec_fmt,
};

use crate::parser::ModuleContext;
use crate::term::module::Scope;

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
    module: Arc<ModuleContext>,
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
  QttSubsumption {
    name: Identifier,
    provided: Multiplicity,
    expected: Multiplicity,
    loc: SourceRange,
  },
  StructNoConstructors {
    loc: SourceRange,
  },
  /// `open Module {}` — an explicit but empty name filter. Imports
  /// nothing a plain `use Module {...}` didn't already provide: per
  /// `docs/src/reference.md`, qualified access (`Module.name`) always
  /// works once a module is `use`d, whether or not it's also `open`ed —
  /// see `crate::term::module::validate_open_filters`.
  EmptyOpenFilter {
    module_path: crate::term::ModulePath,
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
      TypeError::Context {
        loc,
        err,
        name,
        module,
      } => {
        write!(f, "{} at {}:{}", err, loc.start.line, loc.start.column)?;
        if let Some(name) = name {
          write!(f, " in {name} in {:?}", module.file)?;
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
      TypeError::QttSubsumption {
        name,
        provided,
        expected,
        loc,
      } => {
        write!(
          f,
          "Cannot pass {} variable '{}' where {} parameter is expected (subsumption failed)",
          match provided {
            Multiplicity::Linear => "linear",
            Multiplicity::Affine => "affine",
            Multiplicity::Zero => "erased",
            Multiplicity::Many => "unrestricted",
          },
          name,
          match expected {
            Multiplicity::Linear => "linear",
            Multiplicity::Affine => "affine",
            Multiplicity::Zero => "erased",
            Multiplicity::Many => "unrestricted",
          },
        )?;
        fmt_loc(loc, f)
      }
      TypeError::StructNoConstructors { loc } => {
        write!(f, "Structs must have at least one constructor")?;
        fmt_loc(loc, f)
      }
      TypeError::EmptyOpenFilter { module_path, loc } => {
        write!(
          f,
          "`open {module_path} {{}}` imports nothing — qualified access already works via `use`, remove this line"
        )?;
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
      module_path: None,
    },
    TypeError::Scope(scope_error, loc) => Diagnostic {
      severity: Severity::Error,
      message: scope_error.to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::ExpectedPi(s, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected function type found: {s}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::Context {
      loc,
      err,
      name,
      module,
    } => {
      let mut diag = err_to_diagnostic(err);
      if let Some(name) = name {
        diag.context_name = Some(format!("{name}"));
      }
      if diag.location.is_none() {
        diag.location = loc_opt(loc);
      }
      if diag.path.is_none() {
        diag.path = module.file.clone();
      }
      if diag.path.is_none() {
        diag.module_path = Some(module.path.clone());
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
      module_path: None,
    },
    TypeError::Generic(s, loc) => Diagnostic {
      severity: Severity::Error,
      message: s.clone(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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
      module_path: None,
    },
    TypeError::ExpectedType(e, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected Type found {e}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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
      module_path: None,
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
      module_path: None,
    },
    TypeError::MissingField(identifier, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Missing field {identifier}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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
      module_path: None,
    },
    TypeError::Instance(instance_error, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("instance {instance_error}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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
      module_path: None,
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
        module_path: None,
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
      module_path: None,
    },
    TypeError::Overflow { value, target, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Integer overflow: {value} does not fit in {target}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::LinearUsedMultipleTimes(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Linear variable '{id}' used more than once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::LinearUnused(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Linear variable '{id}' must be used exactly once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::AffineUsedMultipleTimes(id, loc) => Diagnostic {
      severity: Severity::Error,
      message: format!("Affine variable '{id}' used more than once"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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
      module_path: None,
    },
    TypeError::QttSubsumption {
      name,
      provided,
      expected,
      loc,
    } => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "Cannot pass {} variable '{name}' where {} parameter is expected",
        match provided {
          Multiplicity::Linear => "linear",
          Multiplicity::Affine => "affine",
          Multiplicity::Zero => "erased",
          Multiplicity::Many => "unrestricted",
        },
        match expected {
          Multiplicity::Linear => "linear",
          Multiplicity::Affine => "affine",
          Multiplicity::Zero => "erased",
          Multiplicity::Many => "unrestricted",
        },
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::Many(_errs) => Diagnostic {
      severity: Severity::Error,
      message: "Multiple type errors".to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::StructNoConstructors { loc } => Diagnostic {
      severity: Severity::Error,
      message: "Structs must have at least one constructor".to_string(),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::EmptyOpenFilter { module_path, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!(
        "`open {module_path} {{}}` imports nothing — qualified access already works via `use`, remove this line"
      ),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![Suggestion {
        message: format!("remove `open {module_path} {{}}`"),
      }],
      context_name: None,
      module_path: None,
    },
    TypeError::ExpectedStructName { found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Expected struct type, found {found}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::StructUpdateExpectedInductive { found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Struct update requires an inductive type, found {found}"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::StructTooManyFields { max, found, loc } => Diagnostic {
      severity: Severity::Error,
      message: format!("Too many fields in struct literal (max {max}, found {found})"),
      location: loc_opt(loc),
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::MacroExpansion(err) => Diagnostic {
      severity: Severity::Error,
      message: format!("macro expansion failed: {err}"),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    },
    TypeError::Termination(err) => Diagnostic {
      severity: Severity::Error,
      message: err.to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
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

pub(crate) fn check_strict_positivity(ind: &Inductive) -> Result<(), TypeError> {
  let name = ind.name();
  for cons in ind.constructors() {
    for param in cons.params() {
      check_strict_pos(name, param.typ(), true)?;
    }
  }
  Ok(())
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

  pub fn lookup_mult(&self, name: &Identifier) -> Option<&Multiplicity> {
    self.usages.get(name).map(|(mult, _)| mult)
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
  /// Right-side forall variables that share a name with a left-side forall
  /// variable (name collision). These must not be unified — they represent
  /// the right forall's binder, which is kept (non-unifiable) in keep_vars.
  clash_vars: Set<&'a Identifier>,
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
      clash_vars: Set::default(),
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
      clash_vars: Set::default(),
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
      clash_vars: Set::default(),
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

  fn add_clash_var(&mut self, name: &'a Identifier) {
    self.clash_vars.insert(name);
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
        if name == r_name {
          // Name collision: right forall binds the same name as left.
          // Mark the right name as a clash var so (_, Var) doesn't unify it.
          free_vars.add_clash_var(r_name);
        }
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
      free_vars.insert_free_var(name, Unknown { typ });
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
    (Ctx { term, .. }, _) => match_resolve_type_inner(term, right, free_vars, scope, visiting),
    (_, Ctx { term, .. }) => match_resolve_type_inner(left, term, free_vars, scope, visiting),
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
    (_, Var { name: Id(name) }) => {
      // A right-side Var that collides with a left forall binding
      // (same name used by both foralls) is non-unifiable — skip it.
      if free_vars.clash_vars.contains(name) {
        false
      } else if check_free_vars(name, left, free_vars) {
        true
      } else {
        match resolve_def_alias(&NameRef::Id(name.clone()), scope, visiting) {
          Some(body) => compare_types(left, &body, free_vars),
          None => false,
        }
      }
    }
    _ => compare_types(left, right, free_vars),
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
    // A transparent source-location wrapper — dozens of other `Term`
    // methods (`as_var`, `as_app`, `is_forall`, ...) already see through
    // it. Without this arm, a free var parsed inside a `Ctx`-wrapped
    // sub-term (e.g. a return type's nested application) is invisible to
    // this scan, silently skipping its implicit `Forall` wrapping.
    Term::Ctx { term, .. } => free_vars(term, known_names),
    _ => empty_set(),
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
            attrs: p.attrs.clone(),
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
    ScopedOpen {
      module_path,
      filter,
      attributes,
      decl,
    } => ScopedOpen {
      module_path,
      filter,
      attributes,
      decl: Box::new(elaborate_decl(*decl, known_names)),
    },
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
