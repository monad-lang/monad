use super::*;

#[test]
fn test_do_parser_simple_return() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { return 1 }"#).unwrap();
  similar!(r, app(pvar(vec!["Monad", "pure"]), num(1)));
}

// -------------------------------------------------------------------
// `return expr` as a standalone term -- shorthand for `do { return
// expr }`, legal at every term position, not just inside an
// already-open `do` block.
// -------------------------------------------------------------------

#[test]
fn test_return_shorthand_matches_do_block_form() {
  // AST equality between the two spellings is what proves this is real
  // sugar (same desugar function, same output), not a parallel/
  // divergent implementation.
  let (_, shorthand) = term::<()>(r#"return 1"#.into()).unwrap();
  let (_, do_block) = term::<()>(r#"do { return 1 }"#.into()).unwrap();
  similar!(shorthand.clone(), do_block);
  similar!(shorthand, app(pvar(vec!["Monad", "pure"]), num(1)));
}

#[test]
fn test_return_shorthand_as_def_body() {
  let (_, res) = def_parser(r#"def f : I64 := return 1"#.into()).unwrap();
  similar!(res.term, app(pvar(vec!["Monad", "pure"]), num(1)));
}

#[test]
fn test_return_shorthand_as_if_branch() {
  let (_, r) = term::<()>(r#"if true then return 1 else return 2"#.into()).unwrap();
  similar!(
    r,
    if_term(
      var("true"),
      app(pvar(vec!["Monad", "pure"]), num(1)),
      app(pvar(vec!["Monad", "pure"]), num(2))
    )
  );
}

#[test]
fn test_return_shorthand_as_match_case_body() {
  let (_, r) =
    match_parser::<()>(r#"match x { some v => return v, none => return 0 }"#.into()).unwrap();
  similar!(
    r,
    match_term(
      var("x"),
      vec![
        case(
          id("some"),
          vec![id("v")],
          app(pvar(vec!["Monad", "pure"]), var("v"))
        ),
        case(id("none"), vec![], app(pvar(vec!["Monad", "pure"]), num(0))),
      ]
    )
  );
}

#[test]
fn test_do_parser_simple_bind() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x <- monadic; return x }"#).unwrap();
  let expected = app(
    app(pvar(vec!["Monad", "bind"]), var("monadic")),
    lam(par("x"), app(pvar(vec!["Monad", "pure"]), var("x"))),
  );
  similar!(r, expected);
}

#[test]
fn test_do_parser_let_and_bind() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x := 1; let y <- monadic; return y }"#).unwrap();
  let expected = lets(
    vec![LetVar {
      name: id("x"),
      typ: Term::Hole,
      value: num(1),
    }],
    app(
      app(pvar(vec!["Monad", "bind"]), var("monadic")),
      lam(par("y"), app(pvar(vec!["Monad", "pure"]), var("y"))),
    ),
  );
  similar!(r, expected);
}
#[test]
fn test_do_parser_typed_let_and_bind() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x : I64 := 1; let y : MState <- monadic; return y }"#).unwrap();
  let expected = lets(
    vec![LetVar {
      name: id("x"),
      typ: var("I64"),
      value: num(1),
    }],
    app(
      app(pvar(vec!["Monad", "bind"]), var("monadic")),
      lam(
        param(id("y"), var("MState")),
        app(pvar(vec!["Monad", "pure"]), var("y")),
      ),
    ),
  );
  similar!(r, expected);
}

#[test]
fn test_do_parser_multiple_binds() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let a <- ma; let b <- mb; return b }"#).unwrap();
  let inner = app(
    app(pvar(vec!["Monad", "bind"]), var("mb")),
    lam(par("b"), app(pvar(vec!["Monad", "pure"]), var("b"))),
  );
  let expected = app(
    app(pvar(vec!["Monad", "bind"]), var("ma")),
    lam(par("a"), inner),
  );
  similar!(r, expected);
}

#[test]
fn test_do_parser_with_spaces() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x <- monadic; return x }"#).unwrap();
  let (_, r2) = do_block(r#"do { let x <- monadic; return x }"#).unwrap();
  similar!(r, r2);
}

#[test]
fn test_do_parser_complex_desugar() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let input = r#"do { let x := 1; let y <- get; return y }"#;
  let (_, r) = do_block(input).unwrap();
  let middle_bind = app(
    app(pvar(vec!["Monad", "bind"]), var("get")),
    lam(par("y"), app(pvar(vec!["Monad", "pure"]), var("y"))),
  );
  let expected = lets(
    vec![LetVar {
      name: id("x"),
      typ: Term::Hole,
      value: num(1),
    }],
    middle_bind,
  );
  similar!(r, expected);
}

#[test]
fn test_def_do_block_simple_expr() {
  let s = r#"def hello : IO Unit {
    println "Hello"
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("hello"),
      vec![],
      app2("IO", "Unit"),
      apps(var("println"), vec![str("Hello")]),
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_return() {
  let s = r#"def get_one : IO I64 {
    return 1
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("get_one"),
      vec![],
      app2("IO", "I64"),
      app(pvar(vec!["Monad", "pure"]), num(1)),
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_with_params() {
  let s = r#"def greet (name : String) : IO Unit {
    println name
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("greet"),
      vec![],
      pi(typ("String"), app2("IO", "Unit")),
      lams(
        vec![dpar("name", typ("String"))],
        apps(var("println"), vec![var("name")])
      ),
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_bind() {
  let s = r#"def read_val : IO I64 {
    let x <- get_value
    return x
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  let expected_body = app(
    app(pvar(vec!["Monad", "bind"]), var("get_value")),
    lam(par("x"), app(pvar(vec!["Monad", "pure"]), var("x"))),
  );
  similar!(
    res,
    def(
      mpt("read_val"),
      vec![],
      app2("IO", "I64"),
      expected_body,
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_let() {
  let s = r#"def with_let : IO I64 {
    let x := 42
    return x
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  let expected_body = lets(
    vec![LetVar {
      name: id("x"),
      typ: Term::Hole,
      value: num(42),
    }],
    app(pvar(vec!["Monad", "pure"]), var("x")),
  );
  similar!(
    res,
    def(
      mpt("with_let"),
      vec![],
      app2("IO", "I64"),
      expected_body,
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_multiple_exprs() {
  let s = r#"def multi : IO Unit {
    println "first";
    println "second"
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  let expected_body = app(
    app(
      pvar(vec!["Monad", "bind"]),
      apps(var("println"), vec![str("first")]),
    ),
    lam(par("_"), apps(var("println"), vec![str("second")])),
  );
  similar!(
    res,
    def(
      mpt("multi"),
      vec![],
      app2("IO", "Unit"),
      expected_body,
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_match() {
  let pure = |a| app(pvar(vec!["Monad", "pure"]), a);
  let bind = |a| app(pvar(vec!["Monad", "bind"]), a);
  let s = r#"def multi : IO Unit {
    println "first";
    match val {
      con1 => mon,
      con2 a => do {
        return b
      }
    }
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  let expected_body = app(
    bind(apps(var("println"), vec![str("first")])),
    lam(
      par("_"),
      match_term(
        var("val"),
        vec![
          case(id("con1"), vec![], var("mon")),
          case(id("con2"), vec![id("a")], pure(var("b"))),
        ],
      ),
    ),
  );
  similar!(
    res,
    def(
      mpt("multi"),
      vec![],
      app2("IO", "Unit"),
      expected_body,
      vec![]
    )
  );
}

#[test]
fn test_def_do_block_with_constraints() {
  let s = r#"def test [Monad M] {M: Type -> Type} (arg : M String) : M Unit {
    arg >>= (fn _ => pure unit)
  }"#
    .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("test"),
      vec![type_constraint(mpt("Monad"), vec![id("M")])],
      forall(
        dpar("M", pi(typ("Type"), typ("Type"))),
        pi(app2("M", "String"), app2("M", "Unit"))
      ),
      lams(
        vec![dpar("arg", app2("M", "String"))],
        oper(
          var("arg"),
          ">>=",
          lams(vec![par("_")], app(var("pure"), var("unit")))
        )
      ),
      vec![]
    )
  );
}
