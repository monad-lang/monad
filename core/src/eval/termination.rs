use std::fmt::Display;

use crate::term::{Def, Identifier, Literal, ModulePath, Par, SourceRange, Term, Term::*};

/// Tracks which variables are known subterms of which formal parameters.
///
/// Key: formal parameter identifier -> Value: set of variables that are
/// subterms of that parameter (via pattern matching).
type SubtermEnv = crate::Map<Identifier, crate::Set<Identifier>>;

/// Error returned when the termination check fails.
#[derive(Debug, Clone, PartialEq)]
pub enum TerminationError {
  NotStructural {
    def_name: ModulePath,
    call: String,
    suggestion: String,
    loc: SourceRange,
  },
  NoRecursiveParams {
    def_name: ModulePath,
  },
}

impl Display for TerminationError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TerminationError::NotStructural {
        def_name,
        call,
        suggestion,
        ..
      } => {
        write!(
          f,
          "Termination check failed for '{def_name}'\n  Recursive call: {call}\n  {suggestion}"
        )
      }
      TerminationError::NoRecursiveParams { def_name } => {
        write!(f, "No recursive parameters found for '{def_name}'")
      }
    }
  }
}

/// A found recursive call site with collected arguments.
#[derive(Debug, Clone)]
struct RecursiveCall {
  args: Vec<Term>,
  loc: SourceRange,
}

/// Extract the formal parameters from a function body.
///
/// The body of `def f (x: A) (y: B) := body` is stored as
/// `Lam(Par::P(x), Lam(Par::P(y), body))`. Unwraps the Lam chain
/// and returns parameter identifiers (skipping implicit Par::I params).
fn extract_params(body: &Term) -> Vec<Identifier> {
  let mut params = Vec::new();
  let mut current = body;
  loop {
    match current {
      Lam {
        param: Par::P(p),
        body,
        ..
      } => {
        params.push(p.name.clone());
        current = body;
      }
      Lam {
        param: Par::I { .. },
        body,
        ..
      } => {
        current = body;
      }
      _ => break,
    }
  }
  params
}

/// Check if a term is a reference to a specific definition name.
fn is_ref_to(term: &Term, def_name: &ModulePath) -> bool {
  match term {
    Var { name } => name.to_path().as_ref() == Some(def_name),
    _ => false,
  }
}

/// If `term` is a chain of `App` nodes ending in a reference to `def_name`,
/// collect and return the arguments. Returns None otherwise.
fn as_recursive_call(term: &Term, def_name: &ModulePath) -> Option<RecursiveCall> {
  let mut args: Vec<Term> = Vec::new();
  let mut current = term;
  let mut loc = SourceRange::default();

  loop {
    match current {
      App { fun, arg } => {
        args.push((**arg).clone());
        current = fun;
      }
      Ctx { loc: ctx_loc, term } => {
        loc = ctx_loc.clone();
        current = term;
      }
      _ => break,
    }
  }

  if args.is_empty() {
    return None;
  }

  args.reverse();

  if is_ref_to(current, def_name) {
    Some(RecursiveCall { args, loc })
  } else {
    None
  }
}

/// Check if a scrutinee variable is a formal parameter or known subterm,
/// and if so, record the pattern variables from a match case as subterms.
fn extend_env_from_match(
  env: &mut SubtermEnv,
  scrutinee: &Term,
  case_args: &[Identifier],
  params: &[Identifier],
) {
  let scrutinee_id = match scrutinee {
    Var { name } => name.as_id().cloned(),
    _ => None,
  };

  let Some(scrutinee_id) = scrutinee_id else {
    return;
  };

  // Filter out wildcards
  let new_subterms: Vec<Identifier> = case_args
    .iter()
    .filter(|a| a.as_str() != "_")
    .cloned()
    .collect();

  if new_subterms.is_empty() {
    return;
  }

  // If the scrutinee is a param, its case args are direct subterms
  if params.contains(&scrutinee_id) {
    let entry = env.entry(scrutinee_id.clone()).or_default();
    for sub in new_subterms {
      entry.insert(sub);
    }
    return;
  }

  // If the scrutinee is a known subterm of some param, its case args are
  // indirect subterms (transitive)
  for (param, subterms) in env.iter() {
    if subterms.contains(&scrutinee_id) {
      let entry = env.entry(param.clone()).or_default();
      for sub in &new_subterms {
        entry.insert(sub.clone());
      }
      return;
    }
  }
}

/// Check if a variable is a known subterm of a given parameter.
fn is_subterm(env: &SubtermEnv, param: &Identifier, arg: &Term) -> bool {
  match arg {
    Var { name } => {
      if let Some(var_id) = name.as_id() {
        env
          .get(param)
          .map_or(false, |subterms| subterms.contains(var_id))
      } else {
        false
      }
    }
    _ => false,
  }
}

/// Check that at least one argument in a recursive call is a strict subterm
/// of the corresponding formal parameter.
///
/// Uses lexicographic ordering: if a position passes the original parameter
/// unchanged (identity), we look for a decrease at later positions.
fn check_call_args(
  call: &RecursiveCall,
  env: &SubtermEnv,
  params: &[Identifier],
) -> Result<(), String> {
  let n = params.len().min(call.args.len());

  for i in 0..n {
    let param = &params[i];
    let arg = &call.args[i];

    // If arg is the param itself (identity), no decrease — check later positions
    let is_identity = match arg {
      Var { name } => name.as_id().map_or(false, |id| id == param),
      _ => false,
    };

    if is_identity {
      continue;
    }

    if is_subterm(env, param, arg) {
      return Ok(());
    }
  }

  let args_str: Vec<String> = call.args.iter().map(|a| a.to_string()).collect();
  let params_str: Vec<&str> = params.iter().map(|p| p.as_str()).collect();
  Err(format!(
    "Argument(s) ({}) are not structural subterms of parameter(s) ({})",
    args_str.join(", "),
    params_str.join(", ")
  ))
}

/// Recursively walk a term body, checking all recursive calls for termination.
fn check_body_termination(
  body: &Term,
  def_name: &ModulePath,
  params: &[Identifier],
  env: &SubtermEnv,
) -> Result<(), TerminationError> {
  match body {
    Lam { body, .. } => check_body_termination(body, def_name, params, env),

    App { fun, arg } => {
      // Check if the current App chain is a recursive call
      if let Some(call) = as_recursive_call(body, def_name) {
        check_call_args(&call, env, params).map_err(|msg| TerminationError::NotStructural {
          def_name: def_name.clone(),
          call: format!("{}", body),
          suggestion: format!(
            "{} — add @[terminating] if this function is well-founded",
            msg
          ),
          loc: call.loc,
        })?;
      }
      // Recurse into sub-expressions
      check_body_termination(fun, def_name, params, env)?;
      check_body_termination(arg, def_name, params, env)
    }

    Lit {
      value: Literal::Match { value, cases },
    } => {
      for case in cases {
        let mut case_env = env.clone();
        extend_env_from_match(&mut case_env, value, &case.args, params);
        check_body_termination(&case.value, def_name, params, &case_env)?;
      }
      Ok(())
    }

    Lit {
      value: Literal::If { value, then, els },
    } => {
      check_body_termination(value, def_name, params, env)?;
      check_body_termination(then, def_name, params, env)?;
      check_body_termination(els, def_name, params, env)
    }

    Ann { term, .. } => check_body_termination(term, def_name, params, env),

    Ctx { term, .. } => check_body_termination(term, def_name, params, env),

    // Leaf / non-recursive nodes: no further checking needed
    Var { .. } | Lit { .. } | Sort { .. } | Hole | Ntv { .. } | Con(..) | Quote { .. } => Ok(()),

    // These shouldn't appear in def bodies
    Pi { .. } | Forall { .. } => Ok(()),
  }
}

/// Check that a recursive definition terminates by structural recursion.
///
/// Returns Ok if all recursive calls use structural subterms on at least one
/// parameter, or Err describing the first non-structural call found.
pub fn check_termination(def: &Def) -> Result<(), TerminationError> {
  // Skip if the definition has @[terminating] or @[partial] attribute
  if def
    .attributes
    .iter()
    .any(|a| a.name.as_str() == "terminating" || a.name.as_str() == "partial")
  {
    return Ok(());
  }

  let body = &def.term;
  let params = extract_params(body);
  if params.is_empty() {
    return Ok(());
  }

  let env = SubtermEnv::default();
  check_body_termination(body, def.name(), &params, &env)
}

// ──────── Tests ────────

#[cfg(test)]
mod tests {
  use super::*;
  use crate::term::{case, id, lam, lam_par, mpt, num, param, var};

  fn test_def(name: &str) -> ModulePath {
    mpt(name)
  }

  /// Helper: create a multi-segment ModulePath from string segments
  fn mpath(segments: &[&str]) -> ModulePath {
    ModulePath::new(segments.iter().map(|s| id(s)).collect())
  }

  #[test]
  fn test_extract_params_single() {
    let body = lam(param(id("x"), Term::Hole), var("x"));
    let params = extract_params(&body);
    assert_eq!(params, vec![id("x")]);
  }

  #[test]
  fn test_extract_params_multiple() {
    let body = lam(
      param(id("a"), Term::Hole),
      lam(param(id("b"), Term::Hole), var("a")),
    );
    let params = extract_params(&body);
    assert_eq!(params, vec![id("a"), id("b")]);
  }

  #[test]
  fn test_extract_params_skips_implicit() {
    let body = lam_par(
      Par::I {
        typ: Box::new(Term::Sort { level: 1 }),
        mult: crate::term::Multiplicity::Many,
      },
      lam(param(id("x"), Term::Hole), var("x")),
    );
    let params = extract_params(&body);
    assert_eq!(params, vec![id("x")]);
  }

  #[test]
  fn test_is_ref_to_true() {
    let name = mpath(&["List", "append"]);
    let term = crate::term::mpvar(name.clone());
    assert!(is_ref_to(&term, &name));
  }

  #[test]
  fn test_is_ref_to_false() {
    let name = mpath(&["List", "append"]);
    let term = var("other");
    assert!(!is_ref_to(&term, &name));
  }

  #[test]
  fn test_as_recursive_call_basic() {
    let name = mpath(&["List", "append"]);
    let ref_term = crate::term::mpvar(name.clone());
    let call = crate::term::app(crate::term::app(ref_term, var("tail")), var("b"));
    let result = as_recursive_call(&call, &name);
    assert!(result.is_some());
    let rc = result.unwrap();
    assert_eq!(rc.args.len(), 2);
  }

  #[test]
  fn test_as_recursive_call_not_recursive() {
    let name = mpath(&["List", "append"]);
    let ref_term = crate::term::mpvar(mpath(&["List", "map"]));
    let call = crate::term::app(crate::term::app(ref_term, var("tail")), var("b"));
    let result = as_recursive_call(&call, &name);
    assert!(result.is_none());
  }

  #[test]
  fn test_structural_list_append_passes() {
    let name = mpath(&["List", "append"]);
    let ref_name = crate::term::mpvar(name.clone());

    let empty_case = case(id("empty"), vec![], var("b"));
    let cons_case = case(
      id("cons"),
      vec![id("el_a"), id("tail")],
      crate::term::app(
        crate::term::app(crate::term::mpvar(mpath(&["List", "cons"])), var("el_a")),
        crate::term::app(crate::term::app(ref_name, var("tail")), var("b")),
      ),
    );

    let body = lam(
      param(id("a"), Term::Hole),
      lam(
        param(id("b"), Term::Hole),
        crate::term::match_term(var("a"), vec![empty_case, cons_case]),
      ),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "List.append should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_nonstructural_factorial_fails() {
    let name = test_def("factorial");
    let ref_term = var("factorial");

    let body = lam(
      param(id("n"), Term::Hole),
      crate::term::if_term(
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "beq"])), var("n")),
          num(0),
        ),
        num(1),
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "mul"])), var("n")),
          crate::term::app(
            ref_term,
            crate::term::app(
              crate::term::app(crate::term::mpvar(mpath(&["I64", "sub"])), var("n")),
              num(1),
            ),
          ),
        ),
      ),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(result.is_err(), "factorial should fail termination check");
    let err = result.unwrap_err();
    assert!(
      err.to_string().contains("Termination check failed"),
      "got: {err}"
    );
  }

  #[test]
  fn test_terminating_attr_skips_check() {
    let name = test_def("factorial");
    let ref_term = var("factorial");

    let body = lam(
      param(id("n"), Term::Hole),
      crate::term::if_term(
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "beq"])), var("n")),
          num(0),
        ),
        num(1),
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "mul"])), var("n")),
          crate::term::app(
            ref_term,
            crate::term::app(
              crate::term::app(crate::term::mpvar(mpath(&["I64", "sub"])), var("n")),
              num(1),
            ),
          ),
        ),
      ),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![crate::term::Attribute {
        name: id("terminating"),
        args: vec![],
      }],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "@[terminating] should skip check: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_infinite_loop_rejected() {
    // def infinite (x : I64) : I64 := infinite x
    let name = test_def("infinite");
    let body = lam(
      param(id("x"), Term::Hole),
      crate::term::app(var("infinite"), var("x")),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(result.is_err(), "infinite should fail: no subterm decrease");
  }

  #[test]
  fn test_list_flatten_passes() {
    let name = mpath(&["List", "flatten"]);
    let ref_name = crate::term::mpvar(name.clone());

    let empty_case = case(
      id("empty"),
      vec![],
      crate::term::mpvar(mpath(&["List", "empty"])),
    );
    let cons_case = case(
      id("cons"),
      vec![id("list"), id("tail")],
      crate::term::app(
        crate::term::app(crate::term::mpvar(mpath(&["List", "append"])), var("list")),
        crate::term::app(ref_name, var("tail")),
      ),
    );

    let body = lam(
      param(id("self"), Term::Hole),
      crate::term::match_term(var("self"), vec![empty_case, cons_case]),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "List.flatten should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_list_last_passes() {
    // match self { empty => none, cons a tail => ... List.last tail }
    let name = mpath(&["List", "last"]);
    let ref_name = crate::term::mpvar(name.clone());

    let empty_case = case(id("empty"), vec![], crate::term::none());

    let cons_case = case(
      id("cons"),
      vec![id("a"), id("tail")],
      crate::term::if_term(
        crate::term::app(
          crate::term::mpvar(mpath(&["List", "is_empty"])),
          var("tail"),
        ),
        crate::term::some(var("a")),
        crate::term::app(ref_name, var("tail")),
      ),
    );

    let body = lam(
      param(id("self"), Term::Hole),
      crate::term::match_term(var("self"), vec![empty_case, cons_case]),
    );

    let def = Def {
      name,
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "List.last should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_no_params_no_crash() {
    let name = test_def("zero");
    let def = Def {
      name,
      typ: Term::Hole,
      term: num(0),
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(result.is_ok(), "Constant def should pass");
  }

  #[test]
  fn test_non_recursive_def_passes() {
    // def add (a b : I64) : I64 := a + b   (no self-call)
    let name = test_def("add");
    let body = lam(
      param(id("a"), Term::Hole),
      lam(
        param(id("b"), Term::Hole),
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "add"])), var("a")),
          var("b"),
        ),
      ),
    );

    let def = Def {
      name: name.clone(),
      typ: Term::Hole,
      term: body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "Non-recursive def should pass: {}",
      result.unwrap_err()
    );
  }
}
