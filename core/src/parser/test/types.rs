use super::*;

#[test]
fn test_type_expression() {
  let term = |i: Span<'static, ()>| term::<()>(i).finish();
  let (_, a) = term("A -> B".into()).unwrap();
  similar!(a, pi(var("A"), var("B")));
  let (_, a) = term("(a: A) -> B a".into()).unwrap();
  similar!(a, pi_var(id("a"), var("A"), app2("B", "a")));
  let (_, a) = term("String -> _".into()).unwrap();
  similar!(a, pi(var("String"), Hole));
  let (_, a) = term("A -> B".into()).unwrap();
  similar!(a, pi(var("A"), var("B")));
  let (_, a) = type_top_expression::<()>("{A : Type} -> {B : Type} -> A -> B".into()).unwrap();
  similar!(
    a,
    forall(
      param(id("A"), typ("Type")),
      forall(param(id("B"), typ("Type")), pi(typ("A"), typ("B")))
    )
  );
  let (_, a) = application::<()>("F (A -> B)".into()).unwrap();
  similar!(a, app(var("F"), pi(var("A"), var("B"))),);

  let (_, a) = type_top_expression::<()>("F (A -> B) -> F A -> F B".into()).unwrap();
  similar!(
    a,
    pi(
      app(var("F"), pi(var("A"), var("B"))),
      pi(app2("F", "A"), app2("F", "B"))
    )
  );
}

#[test]
fn test_type_annotation() {
  let type_annotation = |s: &'static str| type_annotation::<()>(s.into());
  let (_, t) = type_annotation(": String").unwrap();
  similar!(t, var("String"));
  let (_, t) = type_annotation(": (String)").unwrap();
  similar!(t, var("String"));
  let (_, t) = type_annotation(": IO Unit").unwrap();
  similar!(t, app2("IO", "Unit"));
  let (_, t) = type_annotation(": (Option (Result String (Error E)))").unwrap();
  similar!(
    t,
    app(
      var("Option"),
      app(app(var("Result"), var("String")), app2("Error", "E"))
    )
  );
  let (_, t) = type_annotation(": String -> IO Unit").unwrap();
  similar!(t, pi(var("String"), app2("IO", "Unit")));
  let (_, t) = type_annotation(": IO (Option String) -> String -> IO Unit").unwrap();
  similar!(
    t,
    pi(
      app(var("IO"), app2("Option", "String")),
      pi(var("String"), app2("IO", "Unit"))
    )
  );
  let (_, t) = type_annotation(": IO (Option U8) -> (String -> IO Unit)").unwrap();
  similar!(
    t,
    pi(
      app(var("IO"), app2("Option", "U8")),
      pi(var("String"), app2("IO", "Unit"))
    )
  );
  let (_, t) = type_annotation(": (A -> IO Unit) -> B").unwrap();
  similar!(t, pi(pi(var("A"), app2("IO", "Unit")), var("B")));
  let (_, t) = type_annotation(": ((A -> IO Unit) -> C B) -> B").unwrap();
  similar!(
    t,
    pi(
      pi(pi(var("A"), app2("IO", "Unit")), app2("C", "B")),
      var("B")
    )
  );
  let (_, t) =
    type_annotation(": (Option (Result String (Error E)) -> String) -> IO Unit").unwrap();
  similar!(
    t,
    pi(
      pi(
        app(
          var("Option"),
          app(app(var("Result"), var("String")), app2("Error", "E"))
        ),
        var("String")
      ),
      app2("IO", "Unit")
    )
  );
}

#[test]
fn test_all_type_cons() {
  let all_type_cons_parser = |s: &'static str| all_type_cons_parser::<()>(s.into());
  let s = r#"[Applicative A]"#;
  let (_, res) = all_type_cons_parser(s).unwrap();
  similar!(
    res,
    vec![type_constraint(mpt("Applicative"), vec![id("A")])]
  );
  let s = r#"[MyClass A B, Monad B]"#;
  let (_, res) = all_type_cons_parser(s).unwrap();
  similar!(
    res,
    vec![
      type_constraint(mpt("MyClass"), vec![id("A"), id("B")]),
      type_constraint(mpt("Monad"), vec![id("B")])
    ]
  );
}

#[test]
fn test_cons_param() {
  let (_, r) = cons_param::<()>(r#"E"#.into()).unwrap();
  similar!(r, vec![dpar("", typ("E"))]);
  let (_, r) = cons_param::<()>(r#"(a : String)"#.into()).unwrap();
  similar!(r, vec![dpar("a", typ("String"))]);
  let (_, r) = cons_param::<()>(r#"(a b c: String)"#.into()).unwrap();
  similar!(
    r,
    vec![
      dpar("a", typ("String")),
      dpar("b", typ("String")),
      dpar("c", typ("String"))
    ]
  );
  let (_, r) = cons_param::<()>(r#"(String -> Option Int)"#.into()).unwrap();
  similar!(r, vec![dpar("", pi(typ("String"), app2("Option", "Int")))]);
}
