use std::fmt::Display;

use crate::empty_set;
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

/// A set of mutually recursive function names being checked together.
type RecursiveNames = crate::Set<ModulePath>;

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

/// Check if a term is a reference to any name in the given set.
fn is_ref_to_any(term: &Term, names: &RecursiveNames) -> bool {
  match term {
    Var { name } => name.to_path().map_or(false, |p| names.contains(&p)),
    _ => false,
  }
}

/// If `term` is a chain of `App` nodes ending in a reference to one of the
/// recursive names, collect and return the arguments. Returns None otherwise.
fn as_recursive_call_any(term: &Term, names: &RecursiveNames) -> Option<RecursiveCall> {
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

  if is_ref_to_any(current, names) {
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
  // Unwrap Ctx wrappers added by the type checker
  let mut scrutinee = scrutinee;
  while let Ctx { term, .. } = scrutinee {
    scrutinee = term;
  }

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
    Ctx { term, .. } => is_subterm(env, param, term),
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

/// Recursively walk a term body, checking all calls to any member of
/// `recursive_names` for structural termination.
fn check_body_termination(
  body: &Term,
  def_name: &ModulePath,
  recursive_names: &RecursiveNames,
  params: &[Identifier],
  env: &SubtermEnv,
) -> Result<(), TerminationError> {
  match body {
    Lam { body, .. } => check_body_termination(body, def_name, recursive_names, params, env),

    App { fun, arg } => {
      // Check if the current App chain is a call to any recursive name.
      // If so, verify structural termination and stop — don't recurse into
      // sub-expressions (which would detect partial applications as false positives).
      if let Some(call) = as_recursive_call_any(body, recursive_names) {
        return check_call_args(&call, env, params).map_err(|msg| {
          TerminationError::NotStructural {
            def_name: def_name.clone(),
            call: format!("{}", body),
            suggestion: format!(
              "{} — add @[terminating] if this function is well-founded",
              msg
            ),
            loc: call.loc,
          }
        });
      }
      // Not a recursive call — recurse into sub-expressions
      check_body_termination(fun, def_name, recursive_names, params, env)?;
      check_body_termination(arg, def_name, recursive_names, params, env)
    }

    Lit {
      value: Literal::Match { value, cases },
    } => {
      for case in cases {
        let mut case_env = env.clone();
        extend_env_from_match(&mut case_env, value, &case.args, params);
        check_body_termination(&case.value, def_name, recursive_names, params, &case_env)?;
      }
      Ok(())
    }

    Lit {
      value: Literal::If { value, then, els },
    } => {
      check_body_termination(value, def_name, recursive_names, params, env)?;
      check_body_termination(then, def_name, recursive_names, params, env)?;
      check_body_termination(els, def_name, recursive_names, params, env)
    }

    Ann { term, .. } => check_body_termination(term, def_name, recursive_names, params, env),

    Ctx { term, .. } => check_body_termination(term, def_name, recursive_names, params, env),

    // Leaf / non-recursive nodes: no further checking needed
    Var { .. } | Lit { .. } | Sort { .. } | Hole | Ntv { .. } | Con(..) | Quote { .. } => Ok(()),

    // These shouldn't appear in def bodies
    Pi { .. } | Forall { .. } => Ok(()),
  }
}

/// Build a call graph from definitions: for each def, find which other
/// defs (by ModulePath) it references in its body.
pub fn build_call_graph(defs: &[&Def]) -> crate::Map<ModulePath, crate::Set<ModulePath>> {
  let def_names: crate::Set<&ModulePath> = defs.iter().map(|d| d.name()).collect();
  let mut graph = crate::Map::new();

  for def in defs {
    let callees = find_callees(&def.term, &def_names);
    graph.insert(def.name().clone(), callees);
  }

  graph
}

/// Walk a term to find all Var references that match known def names.
fn find_callees(term: &Term, known_names: &crate::Set<&ModulePath>) -> crate::Set<ModulePath> {
  let mut callees = empty_set();

  fn walk(term: &Term, known: &crate::Set<&ModulePath>, callees: &mut crate::Set<ModulePath>) {
    match term {
      Var { name } => {
        if let Some(path) = name.to_path() {
          if known.contains(&path) {
            callees.insert(path);
          }
        }
      }
      App { fun, arg } => {
        walk(fun, known, callees);
        walk(arg, known, callees);
      }
      Lam { body, .. } => walk(body, known, callees),
      Ann { term, .. } => walk(term, known, callees),
      Ctx { term, .. } => walk(term, known, callees),
      Lit {
        value: Literal::Match { value, cases },
      } => {
        walk(value, known, callees);
        for case in cases {
          walk(&case.value, known, callees);
        }
      }
      Lit {
        value: Literal::If { value, then, els },
      } => {
        walk(value, known, callees);
        walk(then, known, callees);
        walk(els, known, callees);
      }
      Pi { arg, ret, .. } => {
        walk(arg, known, callees);
        walk(ret, known, callees);
      }
      Forall { typ, body, .. } => {
        walk(typ, known, callees);
        walk(body, known, callees);
      }
      _ => {}
    }
  }

  walk(term, known_names, &mut callees);
  callees
}

/// Find strongly connected components in the call graph.
/// Returns groups of mutually recursive definitions (SCCs with size > 1).
pub fn find_mutual_groups(
  graph: &crate::Map<ModulePath, crate::Set<ModulePath>>,
) -> Vec<Vec<ModulePath>> {
  // Use Tarjan's algorithm for SCC detection
  let mut index_counter = 0u64;
  let mut indices: crate::Map<ModulePath, u64> = crate::Map::new();
  let mut lowlink: crate::Map<ModulePath, u64> = crate::Map::new();
  let mut on_stack: crate::Set<ModulePath> = empty_set();
  let mut stack: Vec<ModulePath> = Vec::new();
  let mut sccs: Vec<Vec<ModulePath>> = Vec::new();

  // Collect all nodes (some may have no outgoing edges)
  let mut all_nodes: crate::Set<ModulePath> = empty_set();
  for node in graph.keys() {
    all_nodes.insert(node.clone());
  }
  for callees in graph.values() {
    for callee in callees {
      all_nodes.insert(callee.clone());
    }
  }

  fn strongconnect(
    v: &ModulePath,
    graph: &crate::Map<ModulePath, crate::Set<ModulePath>>,
    index_counter: &mut u64,
    indices: &mut crate::Map<ModulePath, u64>,
    lowlink: &mut crate::Map<ModulePath, u64>,
    on_stack: &mut crate::Set<ModulePath>,
    stack: &mut Vec<ModulePath>,
    sccs: &mut Vec<Vec<ModulePath>>,
  ) {
    indices.insert(v.clone(), *index_counter);
    lowlink.insert(v.clone(), *index_counter);
    *index_counter += 1;
    stack.push(v.clone());
    on_stack.insert(v.clone());

    if let Some(neighbors) = graph.get(v) {
      for w in neighbors {
        if !indices.contains_key(w) {
          strongconnect(
            w,
            graph,
            index_counter,
            indices,
            lowlink,
            on_stack,
            stack,
            sccs,
          );
          let w_low = lowlink[w];
          let v_low = lowlink.get_mut(v).unwrap();
          *v_low = (*v_low).min(w_low);
        } else if on_stack.contains(w) {
          let w_idx = indices[w];
          let v_low = lowlink.get_mut(v).unwrap();
          *v_low = (*v_low).min(w_idx);
        }
      }
    }

    if lowlink[v] == indices[v] {
      let mut scc = Vec::new();
      loop {
        let w = stack.pop().unwrap();
        on_stack.remove(&w);
        scc.push(w.clone());
        if &w == v {
          break;
        }
      }
      if scc.len() > 1 {
        sccs.push(scc);
      }
    }
  }

  for node in &all_nodes {
    if !indices.contains_key(node) {
      strongconnect(
        node,
        graph,
        &mut index_counter,
        &mut indices,
        &mut lowlink,
        &mut on_stack,
        &mut stack,
        &mut sccs,
      );
    }
  }

  sccs
}

/// Check a single definition for termination, treating only self-calls
/// as recursive calls.
///
/// Returns Ok if all self-calls use structural subterms on at least one
/// parameter, or Err describing the first non-structural call found.
pub fn check_termination(def: &Def) -> Result<(), TerminationError> {
  // Skip if the definition has @[terminating] or @[partial] attribute
  if def.has_terminating_attr() || def.has_partial_attr() {
    return Ok(());
  }

  let body = &def.term;
  let params = extract_params(body);
  if params.is_empty() {
    return Ok(());
  }

  let mut names = RecursiveNames::default();
  names.insert(def.name().clone());
  let env = SubtermEnv::default();
  check_body_termination(body, def.name(), &names, &params, &env)
}

/// Check a mutually recursive group of definitions for termination.
///
/// Each definition's body is checked against calls to any member of the group.
/// A call to any group member must use a structural subterm of the caller's
/// parameters.
pub fn check_termination_group(defs: &[&Def]) -> Result<(), TerminationError> {
  let mut recursive_names = RecursiveNames::default();
  for def in defs {
    recursive_names.insert(def.name().clone());
  }

  for def in defs {
    // Skip individual defs with escape attributes
    if def.has_terminating_attr() || def.has_partial_attr() {
      continue;
    }

    let params = extract_params(&def.term);
    if params.is_empty() {
      return Err(TerminationError::NoRecursiveParams {
        def_name: def.name().clone(),
      });
    }

    let env = SubtermEnv::default();
    check_body_termination(&def.term, def.name(), &recursive_names, &params, &env)?;
  }

  Ok(())
}

/// Run termination checking on a collection of definitions.
///
/// Builds the call graph, finds mutual recursion groups (SCCs), and checks
/// each group together. Single-recursive definitions are checked individually.
pub fn check_termination_all(defs: &[&Def]) -> Result<(), TerminationError> {
  let graph = build_call_graph(defs);
  let groups = find_mutual_groups(&graph);

  // Collect defs that are in mutual groups
  let mut in_group: crate::Set<ModulePath> = empty_set();
  for group in &groups {
    for name in group {
      in_group.insert(name.clone());
    }
  }

  // Check each mutual group
  for group in &groups {
    let group_defs: Vec<&Def> = defs
      .iter()
      .filter(|d| group.contains(d.name()))
      .copied()
      .collect();
    check_termination_group(&group_defs)?;
  }

  // Check remaining non-mutual defs individually
  for def in defs {
    if !in_group.contains(def.name()) {
      check_termination(def)?;
    }
  }

  Ok(())
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

  // ── Unit tests for helper functions ──

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

  // ── Single-def termination tests ──

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
  fn test_partial_attr_skips_check() {
    let name = test_def("arbitrary");
    let ref_term = var("arbitrary");

    let body = lam(
      param(id("n"), Term::Hole),
      crate::term::if_term(
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "beq"])), var("n")),
          num(0),
        ),
        num(1),
        crate::term::app(
          ref_term,
          crate::term::app(
            crate::term::app(crate::term::mpvar(mpath(&["I64", "sub"])), var("n")),
            num(1),
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
        name: id("partial"),
        args: vec![],
      }],
    };

    let result = check_termination(&def);
    assert!(
      result.is_ok(),
      "@[partial] should skip check: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_infinite_loop_rejected() {
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

  // ── Call graph tests ──

  #[test]
  fn test_build_call_graph_basic() {
    // f calls g, g calls nothing
    let f_name = test_def("f");
    let g_name = test_def("g");

    let f_def = Def {
      name: f_name.clone(),
      typ: Term::Hole,
      term: lam(
        param(id("x"), Term::Hole),
        crate::term::app(var("g"), var("x")),
      ),
      type_constraints: vec![],
      attributes: vec![],
    };

    let g_def = Def {
      name: g_name.clone(),
      typ: Term::Hole,
      term: lam(param(id("x"), Term::Hole), var("x")),
      type_constraints: vec![],
      attributes: vec![],
    };

    let defs = [&f_def, &g_def];
    let graph = build_call_graph(&defs);
    assert!(graph.get(&f_name).unwrap().contains(&g_name));
    assert!(graph.get(&g_name).unwrap().is_empty());
  }

  #[test]
  fn test_build_call_graph_mutual() {
    // f calls g, g calls f
    let f_name = test_def("f");
    let g_name = test_def("g");

    let f_def = Def {
      name: f_name.clone(),
      typ: Term::Hole,
      term: lam(
        param(id("x"), Term::Hole),
        crate::term::app(var("g"), var("x")),
      ),
      type_constraints: vec![],
      attributes: vec![],
    };

    let g_def = Def {
      name: g_name.clone(),
      typ: Term::Hole,
      term: lam(
        param(id("x"), Term::Hole),
        crate::term::app(var("f"), var("x")),
      ),
      type_constraints: vec![],
      attributes: vec![],
    };

    let defs = [&f_def, &g_def];
    let graph = build_call_graph(&defs);
    assert!(graph.get(&f_name).unwrap().contains(&g_name));
    assert!(graph.get(&g_name).unwrap().contains(&f_name));
  }

  #[test]
  fn test_find_mutual_groups_pair() {
    // f → g, g → f  => one SCC {f, g}
    let f = test_def("f");
    let g = test_def("g");
    let mut graph = crate::Map::new();
    graph.insert(f.clone(), crate::set_of(std::iter::once(g.clone())));
    graph.insert(g.clone(), crate::set_of(std::iter::once(f.clone())));

    let groups = find_mutual_groups(&graph);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].len(), 2);
    // Both f and g should be in the group
    let group_set: crate::Set<&ModulePath> = groups[0].iter().collect();
    assert!(group_set.contains(&f));
    assert!(group_set.contains(&g));
  }

  #[test]
  fn test_find_mutual_groups_no_cycle() {
    // f → g, g → h  (simple chain, no mutual recursion)
    let f = test_def("f");
    let g = test_def("g");
    let h = test_def("h");
    let mut graph = crate::Map::new();
    graph.insert(f.clone(), crate::set_of(std::iter::once(g.clone())));
    graph.insert(g.clone(), crate::set_of(std::iter::once(h.clone())));
    graph.insert(h.clone(), empty_set());

    let groups = find_mutual_groups(&graph);
    assert!(groups.is_empty(), "no mutual groups in a DAG");
  }

  #[test]
  fn test_find_mutual_groups_self_loop_not_mutual() {
    // f → f (self-loop, not mutual with others)
    let f = test_def("f");
    let mut graph = crate::Map::new();
    graph.insert(f.clone(), crate::set_of(std::iter::once(f.clone())));

    let groups = find_mutual_groups(&graph);
    // Self-loop is an SCC of size 1, should not be returned as mutual group
    assert!(groups.is_empty());
  }

  // ── Mutual recursion termination tests ──

  #[test]
  fn test_mutual_structural_passes() {
    // Mutual recursion on List, both decreasing:
    //
    // def is_even (n : Nat) : Bool :=
    //   match n { zero => true, succ m => is_odd m }
    //
    // def is_odd (n : Nat) : Bool :=
    //   match n { zero => false, succ m => is_even m }
    let even_name = test_def("is_even");
    let odd_name = test_def("is_odd");

    let even_term = crate::term::mpvar(even_name.clone());
    let odd_term = crate::term::mpvar(odd_name.clone());

    let even_body = lam(
      param(id("n"), Term::Hole),
      crate::term::match_term(
        var("n"),
        vec![
          case(id("zero"), vec![], crate::term::b_true()),
          case(
            id("succ"),
            vec![id("m")],
            crate::term::app(odd_term, var("m")),
          ),
        ],
      ),
    );

    let odd_body = lam(
      param(id("n"), Term::Hole),
      crate::term::match_term(
        var("n"),
        vec![
          case(id("zero"), vec![], crate::term::b_false()),
          case(
            id("succ"),
            vec![id("m")],
            crate::term::app(even_term, var("m")),
          ),
        ],
      ),
    );

    let even_def = Def {
      name: even_name,
      typ: Term::Hole,
      term: even_body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let odd_def = Def {
      name: odd_name,
      typ: Term::Hole,
      term: odd_body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination_group(&[&even_def, &odd_def]);
    assert!(
      result.is_ok(),
      "is_even/is_odd mutual recursion should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_mutual_nonstructural_fails() {
    // Non-structural mutual recursion:
    // def f (x : I64) : I64 := g (x - 1)
    // def g (x : I64) : I64 := f (x - 1)
    let f_name = test_def("f");
    let g_name = test_def("g");

    let f_term = crate::term::mpvar(f_name.clone());
    let g_term = crate::term::mpvar(g_name.clone());

    let f_body = lam(
      param(id("x"), Term::Hole),
      crate::term::app(
        g_term,
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "sub"])), var("x")),
          num(1),
        ),
      ),
    );

    let g_body = lam(
      param(id("x"), Term::Hole),
      crate::term::app(
        f_term,
        crate::term::app(
          crate::term::app(crate::term::mpvar(mpath(&["I64", "sub"])), var("x")),
          num(1),
        ),
      ),
    );

    let f_def = Def {
      name: f_name,
      typ: Term::Hole,
      term: f_body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let g_def = Def {
      name: g_name,
      typ: Term::Hole,
      term: g_body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination_group(&[&f_def, &g_def]);
    assert!(
      result.is_err(),
      "non-structural mutual recursion should fail"
    );
  }

  #[test]
  fn test_mutual_three_way_structural_passes() {
    // Three-way mutual recursion on Nat (all structural):
    // def a (n : Nat) : Nat := match n { zero => zero, succ m => b m }
    // def b (n : Nat) : Nat := match n { zero => zero, succ m => c m }
    // def c (n : Nat) : Nat := match n { zero => zero, succ m => a m }
    let a_name = test_def("a");
    let b_name = test_def("b");
    let c_name = test_def("c");

    let a_term = crate::term::mpvar(a_name.clone());
    let b_term = crate::term::mpvar(b_name.clone());
    let c_term = crate::term::mpvar(c_name.clone());

    let make_body = |callee: Term| -> Term {
      lam(
        param(id("n"), Term::Hole),
        crate::term::match_term(
          var("n"),
          vec![
            case(id("zero"), vec![], crate::term::num(0)),
            case(
              id("succ"),
              vec![id("m")],
              crate::term::app(callee, var("m")),
            ),
          ],
        ),
      )
    };

    let a_def = Def {
      name: a_name,
      typ: Term::Hole,
      term: make_body(b_term),
      type_constraints: vec![],
      attributes: vec![],
    };
    let b_def = Def {
      name: b_name,
      typ: Term::Hole,
      term: make_body(c_term),
      type_constraints: vec![],
      attributes: vec![],
    };
    let c_def = Def {
      name: c_name,
      typ: Term::Hole,
      term: make_body(a_term),
      type_constraints: vec![],
      attributes: vec![],
    };

    let result = check_termination_group(&[&a_def, &b_def, &c_def]);
    assert!(
      result.is_ok(),
      "Three-way structural mutual recursion should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_check_termination_all_mixed() {
    // Mix of single-recursive (structural), mutual (structural), and non-recursive.
    // Verifies that check_termination_all dispatches correctly.
    let f_name = test_def("f");
    let g_name = test_def("g");
    let h_name = test_def("h");

    // f: structural self-recursion on List
    let f_term = crate::term::mpvar(f_name.clone());
    let f_body = lam(
      param(id("xs"), Term::Hole),
      crate::term::match_term(
        var("xs"),
        vec![
          case(id("empty"), vec![], crate::term::num(0)),
          case(
            id("cons"),
            vec![id("x"), id("tail")],
            crate::term::app(f_term, var("tail")),
          ),
        ],
      ),
    );

    // g ⇄ h: mutual structural on List
    let g_term = crate::term::mpvar(g_name.clone());
    let h_term = crate::term::mpvar(h_name.clone());
    let g_body = lam(
      param(id("xs"), Term::Hole),
      crate::term::match_term(
        var("xs"),
        vec![
          case(id("empty"), vec![], crate::term::num(0)),
          case(
            id("cons"),
            vec![id("x"), id("tail")],
            crate::term::app(h_term, var("tail")),
          ),
        ],
      ),
    );
    let h_body = lam(
      param(id("xs"), Term::Hole),
      crate::term::match_term(
        var("xs"),
        vec![
          case(id("empty"), vec![], crate::term::num(0)),
          case(
            id("cons"),
            vec![id("x"), id("tail")],
            crate::term::app(g_term, var("tail")),
          ),
        ],
      ),
    );

    let f_def = Def {
      name: f_name,
      typ: Term::Hole,
      term: f_body,
      type_constraints: vec![],
      attributes: vec![],
    };
    let g_def = Def {
      name: g_name,
      typ: Term::Hole,
      term: g_body,
      type_constraints: vec![],
      attributes: vec![],
    };
    let h_def = Def {
      name: h_name,
      typ: Term::Hole,
      term: h_body,
      type_constraints: vec![],
      attributes: vec![],
    };

    let defs = [&f_def, &g_def, &h_def];
    let result = check_termination_all(&defs);
    assert!(
      result.is_ok(),
      "Mixed single/mutual structural recursion should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_nat_add_structural_passes() {
    // Mimics: def Nat.add (a b : Nat) : Nat := match a { zero => b, succ n => Nat.succ (Nat.add n b) }
    let name = mpath(&["Nat", "add"]);
    let ref_name = crate::term::mpvar(name.clone());

    let zero_case = crate::term::case(id("zero"), vec![], var("b"));
    let succ_case = crate::term::case(
      id("succ"),
      vec![id("n")],
      crate::term::app(
        crate::term::app(crate::term::mpvar(mpath(&["Nat", "succ"])), var("n")),
        crate::term::app(crate::term::app(ref_name, var("n")), var("b")),
      ),
    );

    let body = lam(
      param(id("a"), Term::Hole),
      lam(
        param(id("b"), Term::Hole),
        crate::term::match_term(var("a"), vec![zero_case, succ_case]),
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
      "Nat.add should pass: {}",
      result.unwrap_err()
    );
  }

  #[test]
  fn test_list_map_structural_passes() {
    // Mimics: def List.map (f : A -> B) (self: List A) : List B :=
    //   match self { empty => List.empty, cons a tail => List.cons (f a) (List.map f tail) }
    let name = mpath(&["List", "map"]);
    let ref_name = crate::term::mpvar(name.clone());

    let empty_case = crate::term::case(
      id("empty"),
      vec![],
      crate::term::mpvar(mpath(&["List", "empty"])),
    );
    let cons_case = crate::term::case(
      id("cons"),
      vec![id("a"), id("tail")],
      crate::term::app(
        crate::term::app(
          crate::term::mpvar(mpath(&["List", "cons"])),
          crate::term::app(var("f"), var("a")),
        ),
        crate::term::app(crate::term::app(ref_name, var("f")), var("tail")),
      ),
    );

    let body = lam(
      param(id("f"), Term::Hole),
      lam(
        param(id("self"), Term::Hole),
        crate::term::match_term(var("self"), vec![empty_case, cons_case]),
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
      "List.map should pass: {}",
      result.unwrap_err()
    );
  }
}
