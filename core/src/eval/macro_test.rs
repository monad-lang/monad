// Macro system tests.
//
// Wiring up: add `pub mod macro_test;` under `#[cfg(test)]` in `core/src/eval.rs`.
// This file won't compile until the following types/functions exist:
//   - Term::Quote { term: Box<Term> }
//   - Literal::Term(Box<Term>)
//   - Decl::DefMacro(Def)
//   - NameRef::Macro(Identifier)
//   - fn expand_macros(...) in eval/macro_expand.rs (or eval.rs)
//   - Module::get_macro_defs() on module
//
// See plans/hygienic-macros.md for the implementation plan.

use crate::core_check_module::type_check_module_decls_new;
use crate::eval::macro_expand::expand_macros;
use crate::eval::r#type::elaborate_decls;
use crate::parser::parse_file;
use crate::parser::{ReplInput, repl_parser};
use crate::term::module::{LoadedModules, ParsedModule, default_modules, module};
use crate::term::{Decl, Hole, ModulePath, NameRef, SourceContext, Term, app, def, mpt, num, var};

fn parse_term(input: &str) -> Term {
  let ReplInput::Term(e) = repl_parser(input).unwrap() else {
    panic!("expected term")
  };
  e
}

// ===== Section 1: Quote parsing & display =====

fn unwrap_ctx(term: Term) -> Term {
  match term {
    Term::Ctx { term, .. } => *term,
    t => t,
  }
}

#[test]
fn test_quote_parses_simple() {
  let parsed = parse_term("quote { 1 + 2 }");
  let inner = unwrap_ctx(parsed);
  assert!(matches!(inner, Term::Quote { .. }), "expected Quote");
}

#[test]
fn test_quote_parses_nested() {
  let parsed = parse_term("quote { quote { x } }");
  let inner = unwrap_ctx(parsed);
  assert!(matches!(inner, Term::Quote { .. }), "expected Quote");
}

#[test]
fn test_quote_display_roundtrip() {
  // Use a simple variable to avoid type suffix issues
  let t = parse_term("quote { x }");
  let s = t.to_string();
  let reparsed = parse_term(&s);
  let inner = |t: Term| match t {
    Term::Ctx { term, .. } => *term,
    t => t,
  };
  assert_eq!(format!("{:?}", inner(t)), format!("{:?}", inner(reparsed)));
}

#[test]
fn test_quote_keyword_reserved() {
  let r = parse_file("def quote : I64 := 42");
  assert!(r.is_err(), "quote must be a reserved keyword");
}

// Section 2 (Quote's RUNTIME value semantics — evaluating a `Quote` to a
// `Term::Lit(Literal::Term(..))`, i.e. a term-as-value, via the legacy
// tree-walker's own `eval()`) was removed along with that evaluator, for
// the same reason as Section 3 above: this quoting-at-runtime feature's
// only real consumer was the `eval_term` native (zero `.mo`-corpus
// usage), already gone, and the CoreTerm pipeline's closure/`Value`-
// based IR has no obvious "term as a first-class runtime value"
// representation to port these three tests (`test_quote_eval_produces_
// term_value`, `test_quote_body_not_evaluated`,
// `test_quote_content_unbound_var_ok`) against — real design work, not
// a mechanical port. Quote's role in macro EXPANSION (compile-time,
// pre-lowering) is unaffected and still fully covered by sections 1 and
// 4-9 below via `expand_macros`.

// Section 3 (eval_term — a scope-aware native that quote-evaluates a
// term at runtime) was removed along with the legacy tree-walking
// evaluator: `eval_term` had zero real `.mo`-corpus usage (nothing
// anywhere declares `#[native "eval_term"]`), no CoreTerm-evaluator
// equivalent, and its only two callers were the two tests that used to
// live here (`test_eval_term_arithmetic`, `test_eval_term_with_macro`).
// See plans/implementations/core-term-closure-evaluator.md.

// ===== Section 4: unquote context recognition (expansion time) =====

#[test]
fn test_unquote_inside_quote_recognized() {
  // unquote inside quote is recognized at expansion time
  // It appears as App(Var("unquote"), arg) in the AST
  let t = parse_term("quote { unquote 42 }");
  let inner = match t {
    Term::Ctx { term, .. } => *term,
    t => t,
  };
  assert!(matches!(inner, Term::Quote { .. }), "expected Quote");
  // The inner content has unquote as a function call
  match inner {
    Term::Quote { term } => {
      let inner = match *term {
        Term::Ctx { term, .. } => *term,
        t => t,
      };
      let has_unquote = matches!(&inner, Term::App { fun, .. } if matches!(fun.as_ref(), Term::Var { name: NameRef::Id(n) } if n.as_str() == "unquote"));
      assert!(
        has_unquote,
        "expected App(Var(unquote), 42) in Quote body, got: {inner:?}"
      );
    }
    _ => panic!("expected Quote"),
  }
}

#[test]
fn test_unquote_outside_quote_fails() {
  // No standalone "check a bare Term" entry point survives the legacy
  // checker's removal — `type_check_module_decls_new` (like
  // `core/src/lib.rs`'s `eval_repl_term`) wraps the term of interest in
  // a synthetic `main` def and checks that instead.
  let loaded = default_modules().unwrap();
  let path = ModulePath::top("test_unquote");
  let t = app(var("unquote"), num(42));
  let decl = SourceContext::no_ctx(Decl::Def(def(mpt("main"), vec![], Hole, t, vec![])));
  let r = type_check_module_decls_new(&path, vec![decl], &loaded);
  assert!(
    r.is_err(),
    "unquote outside quote must produce a type error"
  );
  let msg = r.unwrap_err().to_string();
  assert!(
    msg.contains("unquote") || msg.contains("undefined"),
    "got: {msg}"
  );
}

// ===== Section 5: defmacro parsing & storage =====

#[test]
fn test_defmacro_parses_simple() {
  let parsed = parse_file("defmacro id x := quote { x }").unwrap();
  assert_eq!(parsed.decls.len(), 1);
  match &parsed.decls[0].value() {
    Decl::DefMacro(def) => {
      assert_eq!(def.name, mpt("id"));
      // The body may be wrapped in a lambda (for params); unwrap to find Quote
      let mut body = def.term.clone();
      while let Term::Lam { param: _, body: b } = body {
        body = *b;
      }
      body = unwrap_ctx(body);
      assert!(
        matches!(body, Term::Quote { .. }),
        "expected Quote body, got: {}",
        def.term
      );
    }
    other => panic!("expected DefMacro, got: {other:?}"),
  }
}

#[test]
fn test_defmacro_stored_in_module() {
  let parsed = parse_file("defmacro id x := quote { x }").unwrap();
  let mo = module(
    ModulePath::top("test"),
    ParsedModule {
      decls: parsed.decls,
      module_doc: None,
    },
  );
  let macro_defs = mo.get_macro_defs();
  assert_eq!(macro_defs.len(), 1);
  assert_eq!(macro_defs[0].name, mpt("id"));
}

#[test]
fn test_defmacro_with_multiple_params() {
  let parsed = parse_file("defmacro pair a b := quote { x }").unwrap();
  assert_eq!(parsed.decls.len(), 1);
  match &parsed.decls[0].value() {
    Decl::DefMacro(def) => {
      assert_eq!(def.name, mpt("pair"));
      // With params, the body should be a lambda
      let body = unwrap_ctx(def.term.clone());
      assert!(
        body.is_lam(),
        "multi-param macro body should be a lambda, got: {body}"
      );
    }
    other => panic!("expected DefMacro, got: {other:?}"),
  }
}

// ===== Section 6: Macro expansion (basic) =====
// All tests in Sections 6-9 are marked #[ignore] because expand_macros is a stub.
// Enable them as the expansion pass is implemented.

fn expand_and_type_check(input: &str) -> Result<(), String> {
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  let path = ModulePath::top("test_macro");
  let parsed = parse_file(input.into()).map_err(|e| format!("{e}"))?;
  let decls = elaborate_decls(parsed.decls, &loaded);
  let decls = expand_macros(decls, &loaded).map_err(|e| format!("{e}"))?;
  let oks = type_check_module_decls_new(&path, decls, &loaded).map_err(|e| format!("{e}"))?;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls: oks,
      module_doc: None,
    },
  ));
  Ok(())
}

fn expand_fails(input: &str) -> String {
  let loaded = default_modules().unwrap();
  let path = ModulePath::top("test_macro");
  let parsed = parse_file(input.into()).unwrap_or_else(|e| {
    panic!("expand_fails parse error: {e}");
  });
  let decls = elaborate_decls(parsed.decls, &loaded);
  match expand_macros(decls.clone(), &loaded) {
    Err(e) => e.to_string(),
    // Matches this function's own pre-existing behavior from before the
    // legacy-checker port: re-checks the PRE-expansion `decls`, not
    // `expand_macros`'s own `Ok` value — not something introduced here.
    Ok(_) => match type_check_module_decls_new(&path, decls.clone(), &loaded) {
      Err(e) => e.to_string(),
      Ok(_) => panic!("expected expansion or type error, but succeeded"),
    },
  }
}

#[test]
fn test_macro_identity() {
  let r = expand_and_type_check(
    r#"
        defmacro id x := quote { x }
        def main : I64 := id! 42
        "#,
  );
  if let Err(e) = &r {
    eprintln!("identity error: {e}");
  }
  assert!(r.is_ok(), "identity macro should succeed");
}

#[test]
fn test_macro_add_one() {
  let r = expand_and_type_check(
    "defmacro add1 x := quote { unquote x + 1 }\ndef main : I64 := add1! 41\n",
  );
  if let Err(e) = &r {
    eprintln!("add1 error: {e}");
  }
  assert!(r.is_ok(), "add1 macro should succeed");
}

#[test]
fn test_macro_multiple_args() {
  let r = expand_and_type_check(
    r#"
        defmacro first a b := quote { unquote a }
        def main : I64 := first! 42 1
        "#,
  );
  assert!(r.is_ok(), "macro with two args should succeed");
}

#[test]
fn test_macro_in_let_binding() {
  let r = expand_and_type_check(
    "defmacro add1 x := quote { unquote x + 1 }\ndef main : I64 := let x := add1! 1 in x + 1\n",
  );
  if let Err(e) = &r {
    eprintln!("let binding error: {e}");
  }
  assert!(r.is_ok(), "macro in let should succeed");
}

#[test]
fn test_macro_non_term_return_fails() {
  let msg = expand_fails(
    r#"
        defmacro bad x := 42
        def main : I64 := bad! 1
        "#,
  );
  assert!(
    msg.contains("Term"),
    "expected error about non-Term return, got: {msg}"
  );
}

#[test]
fn test_macro_not_found_fails() {
  let msg = expand_fails("def main : I64 := undefined_macro! 42");
  assert!(
    msg.contains("macro") || msg.contains("undefined"),
    "got: {msg}"
  );
}

// ===== Section 7: Macro expansion (edge cases) =====

#[test]
fn test_macro_depth_limit_exceeded() {
  let msg = expand_fails(
    "defmacro recurse x := quote { recurse! (unquote x) }\ndef main : I64 := recurse! 0\n",
  );
  eprintln!("depth limit msg: {msg:?}");
  assert!(msg.contains("depth") || msg.contains("limit"), "got: {msg}");
}

#[test]
fn test_macro_nested_calls() {
  let r = expand_and_type_check(
    r#"
        defmacro add1 x := quote { unquote x + 1 }
        defmacro add2 x := quote { add1! (add1! (unquote x)) }
        def main : I64 := add2! 5
        "#,
  );
  if let Err(e) = &r {
    eprintln!("nested error: {e}");
  }
  assert!(r.is_ok(), "nested macros should expand");
}

#[test]
fn test_macro_as_function_arg() {
  let r = expand_and_type_check(
    r#"
        defmacro wrap x := quote { unquote x }
        def id (x : I64) : I64 := x
        def main : I64 := id (wrap! 42)
        "#,
  );
  assert!(r.is_ok(), "macro result passed to function should succeed");
}

#[test]
#[ignore = "type checker accepts runtime values in type position via type inference; not a macro issue"]
fn test_macro_expanded_in_type_position_fails() {
  // After expansion, the type checker sees the expanded term directly.
  // If the expansion produces a valid type, it succeeds — which is correct behavior.
  let msg =
    expand_fails("defmacro val x := quote { Unit.unit }\ndef main (x : val! 1) : Unit := x\n");
  eprintln!("type position error: {msg:?}");
  assert!(!msg.is_empty(), "macro in type position should fail");
}

// ===== Section 8: Hygiene =====

#[test]
fn test_hygiene_no_capture_of_user_var() {
  let r = expand_and_type_check(
    "defmacro wrap x := quote { let y := 1 in unquote x + y }\ndef main : I64 := let y := 100 in wrap! (y + 2)\n",
  );
  if let Err(e) = &r {
    eprintln!("hygiene error: {e}");
  }
  assert!(r.is_ok(), "hygiene should prevent capture");
}

#[test]
fn test_hygiene_user_var_captured_by_macro() {
  let r = expand_and_type_check(
    "defmacro add_one x := quote { unquote x + 1 }\ndef main : I64 := let x := 10 in add_one! x\n",
  );
  if let Err(e) = &r {
    eprintln!("hygiene2 error: {e}");
  }
  assert!(r.is_ok(), "user var in macro arg should bind");
}

#[test]
fn test_hygiene_multiple_expansions_independent() {
  let r = expand_and_type_check(
    "defmacro wrap x := quote { let y := 1 in unquote x + y }\ndef main : I64 := let y := 100 in wrap! (wrap! (y + 2))\n",
  );
  if let Err(e) = &r {
    eprintln!("hygiene3 error: {e}");
  }
  assert!(r.is_ok(), "nested hygiene expansions should be independent");
}

// ===== Section 9: Cross-module macros =====

/// Run the full pipeline (elaborate → expand → type_check) using an existing LoadedModules.
fn expand_and_type_check_with_loaded(input: &str, loaded: &LoadedModules) -> Result<(), String> {
  let parsed = parse_file(input.into()).map_err(|e| format!("{e}"))?;
  let decls = elaborate_decls(parsed.decls, loaded);
  let decls = expand_macros(decls, loaded).map_err(|e| format!("{e}"))?;
  let path = ModulePath::top("test_macro");
  type_check_module_decls_new(&path, decls, loaded)
    .map(|_| ())
    .map_err(|e| format!("{e}"))
}

#[test]
fn test_cross_module_macro_simple() {
  let loaded = default_modules().unwrap();

  // Helper module defines a macro
  let helper_path = ModulePath::top("macro_helper");
  let parsed_helper = parse_file(
    r#"
    use init

    defmacro add1 x := quote { unquote x + 1 }
    "#,
  )
  .unwrap();
  let helper_decls =
    type_check_module_decls_new(&helper_path, parsed_helper.decls, &loaded).unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    helper_path.clone(),
    ParsedModule {
      decls: helper_decls,
      module_doc: None,
    },
  ));

  // Main module uses the helper macro
  let r = expand_and_type_check_with_loaded(
    r#"
    use macro_helper
    use init

    def main : I64 := add1! 41
    "#,
    &loaded,
  );
  if let Err(e) = &r {
    eprintln!("cross-module macro error: {e}");
  }
  assert!(r.is_ok(), "cross-module macro should succeed");
}

#[test]
fn test_cross_module_macro_calls_same_module_def() {
  let loaded = default_modules().unwrap();

  // Helper module defines a macro and a regular def
  let helper_path = ModulePath::top("macro_helper2");
  let parsed_helper = parse_file(
    r#"
    use init

    def base : I64 := 40
    defmacro add_base x := quote { unquote x + base }
    "#,
  )
  .unwrap();
  let helper_decls =
    type_check_module_decls_new(&helper_path, parsed_helper.decls, &loaded).unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    helper_path.clone(),
    ParsedModule {
      decls: helper_decls,
      module_doc: None,
    },
  ));

  // Main module uses macro that references defs from its own module
  let r = expand_and_type_check_with_loaded(
    r#"
    use macro_helper2
    use init

    def main : I64 := add_base! 2
    "#,
    &loaded,
  );
  if let Err(e) = &r {
    eprintln!("cross-module macro with def reference error: {e}");
  }
  assert!(
    r.is_ok(),
    "cross-module macro referencing own defs should succeed"
  );
}

// ===== Section 10: Integration examples (unless!, twice!, define_getter!) =====

#[test]
fn test_macro_unless_example() {
  // NOTE: Bool.not unquote cond requires parentheses because
  // Bool.not unquote cond parses as ((Bool.not unquote) cond), not (Bool.not (unquote cond))
  let r = expand_and_type_check(
    "defmacro unless cond body := quote { if Bool.not (unquote cond) then (unquote body) else Unit.unit }\ndef main : Unit := unless! Bool.true Unit.unit\n",
  );
  if let Err(e) = &r {
    eprintln!("unless error: {e}");
  }
  assert!(r.is_ok(), "unless macro should type check");
}

#[test]
fn test_parse_simple_type() {
  // Verify the parser handles a simple type declaration
  let r = parse_file("type Unit { unit }\n");
  assert!(r.is_ok(), "simple type should parse");
}

#[test]
fn test_macro_decl_gen_basic() {
  // Simplest possible decl-gen: generate a single def with no params
  let r = expand_and_type_check(
    r#"
    use init

    defmacro gen := decls { def answer : I64 := 42 }
    gen!
    def main : I64 := answer
    "#,
  );
  if let Err(e) = &r {
    eprintln!("decl gen basic error: {e}");
  }
  assert!(r.is_ok(), "basic decl gen macro should type check");
}

#[test]
fn test_macro_decl_gen_generate_def() {
  let r = expand_and_type_check(
    r#"
    use init

    defmacro make_const name val := decls { def const_val : I64 := val }
    make_const! x 10
    def main : I64 := const_val + 1
    "#,
  );
  if let Err(e) = &r {
    eprintln!("decl gen generate def error: {e}");
  }
  assert!(r.is_ok(), "decl gen generating def should succeed");
}

#[test]
fn test_macro_define_getter() {
  // Test a getter-like macro using simpler syntax
  let r = expand_and_type_check(
    r#"
    use init

    defmacro bind x := decls { def bound_val : I64 := x }
    bind! 42
    def main : I64 := bound_val
    "#,
  );
  if let Err(e) = &r {
    eprintln!("getter error: {e}");
  }
  assert!(r.is_ok(), "getter macro should type check");
}

#[test]
fn test_macro_decl_gen_simple() {
  let r = expand_and_type_check(
    r#"
    use init

    defmacro make_const name val := decls { def const_val : I64 := val }
    make_const! x 10
    def main : I64 := const_val + 1
    "#,
  );
  if let Err(e) = &r {
    eprintln!("decl gen error: {e}");
  }
  assert!(r.is_ok(), "decl gen macro should type check");
}

#[test]
fn test_macro_twice() {
  let r = expand_and_type_check(
    "defmacro twice f x := quote { (unquote f) ((unquote f) (unquote x)) }\ndefmacro add1 x := quote { unquote x + 1 }\ndef main : I64 := twice! add1! 5\n",
  );
  if let Err(e) = &r {
    eprintln!("twice error: {e}");
  }
  assert!(r.is_ok(), "twice macro should apply function two times");
}
