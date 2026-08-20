use super::*;

#[test]
fn test_lambda() {
  let lambda = |s: &'static str| lambda::<()>(s.into());
  let (_, r) = lambda(r#"\a => a"#.into()).unwrap();
  similar!(r, lams(vec![par("a")], var("a")));

  let (_, r) = lambda("\\a b \n=>\n a".into()).unwrap();
  similar!(r, lams(vec![par("a"), par("b")], var("a")));
}

// -------------------------------------------------------------------
// Phase 4 of `plans/implementations/struct-field-destructuring.md`:
// lambda-literal parameter destructuring (`\({ x, y } : Point) => x +
// y`), mirroring `def`'s own Phase 3 -- only `lambda` itself gets this
// (not `class_parser`/`inductive_parser`'s OWN `lam_param` call sites,
// which parse a declaration's generic TYPE params, not value params).
// -------------------------------------------------------------------

#[test]
fn test_lambda_destructured_param_desugars_to_wrapping_match() {
  let lambda = |s: &'static str| lambda::<()>(s.into());
  let (_, r) = lambda(r#"\({ x, y } : Point) => x + y"#.into()).unwrap();
  let Term::Lam { param, body } = &r else {
    panic!("expected a Lam, got {r:?}");
  };
  let Par::P(p) = param else {
    panic!("expected an explicit Par::P param, got {param:?}");
  };
  assert!(
    p.name.as_str().starts_with("__struct_param"),
    "destructured param must bind a gensym'd name, got `{}`",
    p.name.as_str()
  );
  similar!((*p.typ).clone(), typ("Point"));
  let Term::Lit {
    value: Literal::Match { value, cases },
  } = body.as_ref()
  else {
    panic!("expected the body to be a Lit::Match, got {body:?}");
  };
  match value.as_ref() {
    Term::Var {
      name: NameRef::Id(scrutinee_name),
    } => assert_eq!(scrutinee_name, &p.name),
    other => panic!("expected the scrutinee to be a bare Var, got {other:?}"),
  }
  assert_eq!(cases.len(), 1);
  assert_eq!(cases[0].name, id(""));
  assert_eq!(
    cases[0].field_pattern,
    Some(FieldPattern {
      fields: vec![(id("x"), id("x")), (id("y"), id("y"))],
      rest: false,
    })
  );
  similar!((*cases[0].value).clone(), oper(var("x"), "+", var("y")));
}

#[test]
fn test_lambda_destructured_and_plain_param_mixed() {
  let lambda = |s: &'static str| lambda::<()>(s.into());
  let (_, r) = lambda(r#"\({ x, y } : Point) factor => x * factor"#.into()).unwrap();
  let Term::Lam { param, body } = &r else {
    panic!("expected outer Lam, got {r:?}");
  };
  let Par::P(p0) = param else {
    panic!("expected explicit Par::P");
  };
  assert!(p0.name.as_str().starts_with("__struct_param"));
  let Term::Lam {
    param: factor_param,
    body: inner_body,
  } = body.as_ref()
  else {
    panic!("expected an inner Lam (`factor`), got {body:?}");
  };
  let Par::P(p1) = factor_param else {
    panic!("expected explicit Par::P");
  };
  assert_eq!(p1.name, id("factor"));
  let Term::Lit {
    value: Literal::Match { .. },
  } = inner_body.as_ref()
  else {
    panic!("expected the innermost body to be a wrapping Lit::Match, got {inner_body:?}");
  };
}

#[test]
fn test_application() {
  let application = |s: &'static str| application::<()>(s.into());
  let (_, r) = application("a b").unwrap();
  similar!(r, apps(var("a"), vec![var("b")]));
  let (_, r) = application("a b c").unwrap();
  similar!(r, apps(var("a"), vec![var("b"), var("c")]));
  let (_, r) = application("fun -12 3").unwrap();
  similar!(r, apps(var("fun"), vec![num(-12), num(3)]));
  let (_, r) = application("(fun a abc) -12 3").unwrap();
  similar!(
    r,
    apps(
      apps(var("fun"), vec![var("a"), var("abc")]),
      vec![num(-12), num(3)]
    )
  );
}

#[test]
fn test_match() {
  let match_parser = |s: &'static str| match_parser::<()>(s.into());
  let (_, r) = match_parser(
    "match l {
		empty => none,
		cons a tail => some a
	}
    "
    .into(),
  )
  .unwrap();
  similar!(
    r,
    match_term(
      var("l"),
      vec![
        case(id("empty"), vec![], var("none")),
        case(
          id("cons"),
          vec![id("a"), id("tail")],
          app(var("some"), var("a"))
        )
      ]
    )
  );
}

#[test]
fn test_match_with_dot_paths() {
  let match_parser = |s: &'static str| match_parser::<()>(s.into());
  let (_, r) = match_parser(
    "match Option.none {
      Option.some val => val,
      Option.none => 42
    }"
    .into(),
  )
  .unwrap();
  similar!(
    r,
    match_term(
      pvar(vec!["Option", "none"]),
      vec![
        case(id("some"), vec![id("val")], var("val")),
        case(id("none"), vec![], num(42))
      ]
    )
  );
}

// -------------------------------------------------------------------
// Phase 1 of `plans/implementations/struct-field-destructuring.md`:
// `FieldPattern` + match-case parsing (no elaboration yet -- `field_pattern`
// stays `Some(..)` on the parsed `MatchCase`, unresolved).
// -------------------------------------------------------------------

#[test]
fn test_match_case_bare_field_pattern() {
  let match_case_parser = |s: &'static str| match_case_parser::<()>(s.into());
  let (_, r) = match_case_parser("{ a, b } => a".into()).unwrap();
  assert_eq!(r.name, id(""));
  assert_eq!(r.args, Vec::<Identifier>::new());
  assert_eq!(
    r.field_pattern,
    Some(FieldPattern {
      fields: vec![(id("a"), id("a")), (id("b"), id("b"))],
      rest: false,
    })
  );
  similar!((*r.value).clone(), var("a"));
}

#[test]
fn test_match_case_bare_field_pattern_rename_and_rest() {
  let match_case_parser = |s: &'static str| match_case_parser::<()>(s.into());
  let (_, r) = match_case_parser("{ a := b, .. } => a".into()).unwrap();
  assert_eq!(
    r.field_pattern,
    Some(FieldPattern {
      fields: vec![(id("a"), id("b"))],
      rest: true,
    })
  );
}

#[test]
fn test_match_case_bare_field_pattern_empty() {
  let match_case_parser = |s: &'static str| match_case_parser::<()>(s.into());
  let (_, r) = match_case_parser("{ } => 0".into()).unwrap();
  assert_eq!(
    r.field_pattern,
    Some(FieldPattern {
      fields: vec![],
      rest: false,
    })
  );
}

#[test]
fn test_match_case_named_field_pattern() {
  let match_parser = |s: &'static str| match_parser::<()>(s.into());
  let (_, r) = match_parser(
    "match s {
      circle { radius } => radius,
      rectangle { width, height } => width
    }"
    .into(),
  )
  .unwrap();
  let cases = match r {
    Term::Lit {
      value: Literal::Match { cases, .. },
    } => cases,
    _ => panic!("expected a Lit::Match term"),
  };
  assert_eq!(cases.len(), 2);
  assert_eq!(cases[0].name, id("circle"));
  assert_eq!(
    cases[0].field_pattern,
    Some(FieldPattern {
      fields: vec![(id("radius"), id("radius"))],
      rest: false,
    })
  );
  assert_eq!(cases[1].name, id("rectangle"));
  assert_eq!(
    cases[1].field_pattern,
    Some(FieldPattern {
      fields: vec![(id("width"), id("width")), (id("height"), id("height"))],
      rest: false,
    })
  );
}

#[test]
fn test_match_case_positional_still_parses_unchanged() {
  // Existing positional cases must still parse via the unchanged third
  // alternative -- `field_pattern` stays `None`.
  let match_case_parser = |s: &'static str| match_case_parser::<()>(s.into());
  let (_, r) = match_case_parser("some a => a".into()).unwrap();
  assert_eq!(r.name, id("some"));
  assert_eq!(r.args, vec![id("a")]);
  assert_eq!(r.field_pattern, None);
}

#[test]
fn test_if() {
  let if_parser = |s: &'static str| if_parser::<()>(s.into());
  let (_, r) = if_parser("if var || var2 then a b else c".into()).unwrap();
  similar!(
    r,
    if_term(
      oper(var("var"), "||", var("var2")),
      app(var("a"), var("b")),
      var("c")
    )
  );
}

#[test]
fn test_let() {
  let let_parser = |s: &'static str| let_parser::<()>(s.into());
  let (_, r) = let_parser("let x := 12 in x".into()).unwrap();
  similar!(
    r,
    lets(
      vec![LetVar {
        name: id("x"),
        typ: Hole,
        value: num(12)
      }],
      var("x")
    )
  );
  let (_, r) = let_parser(r#"let x := 12;y:="Hello" in combine x y"#.into()).unwrap();
  similar!(
    r,
    lets(
      vec![
        LetVar {
          name: id("x"),
          typ: Hole,
          value: num(12)
        },
        LetVar {
          name: id("y"),
          typ: Hole,
          value: str("Hello")
        }
      ],
      apps(var("combine"), vec![var("x"), var("y")])
    )
  );
  let (_, r) = let_parser(
    r#"let x := 12
        z : String := "test";
        y := add x 13
        in combine x y"#
      .into(),
  )
  .unwrap();
  similar!(
    r,
    lets(
      vec![
        LetVar {
          name: id("x"),
          typ: Hole,
          value: num(12)
        },
        LetVar {
          name: id("z"),
          typ: typ("String"),
          value: str("test")
        },
        LetVar {
          name: id("y"),
          typ: Hole,
          value: apps(var("add"), vec![var("x"), num(13)])
        }
      ],
      apps(var("combine"), vec![var("x"), var("y")])
    )
  );
}

#[test]
fn test_struct_val() {
  let p = |s: &'static str| struct_or_update_parser::<()>(s.into());
  let (_, r) = p(r#"{}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::new(),
        type_name: None
      }
    }
  );
  let (_, r) = p(r#"{a := b}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::from([(id("a"), var("b"))]),
        type_name: None
      }
    }
  );
  let (_, r) = p(r#"{a := b, b:={c:=0},}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::from([
          (id("a"), var("b")),
          (
            id("b"),
            Term::Lit {
              value: Literal::StructLit {
                fields: Map::from([(id("c"), num(0))]),
                type_name: None
              }
            }
          )
        ]),
        type_name: None
      }
    }
  );
  let (_, r) = p(r#"{a := b : Point}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::from([(id("a"), var("b"))]),
        type_name: Some(Box::new(var("Point")))
      }
    }
  );
}

#[test]
fn test_term() {
  let term = |s: &'static str| term::<()>(s.into());
  let (_, r) = term(r#"a <| b"#).unwrap();
  similar!(r, opr(var("a"), NameRef::Op("<|".into()), var("b")));
  let (_, r) = term("(a c)\n\t>>= b").unwrap();
  similar!(r, oper(app(var("a"), var("c")), ">>=", var("b")));
  let (_, r) = term(r#"f |> a.b"#).unwrap();
  similar!(r, oper(var("f"), "|>", pvar(vec!["a", "b"])));
  let (_, r) = term(r#"(f |> a).b"#).unwrap();
  similar!(r, oper(oper(var("f"), "|>", var("a")), ".", var("b")));
  let (_, r) = term(r#"\a => (a)"#).unwrap();
  similar!(r, lams(vec![par("a")], var("a")));
  let (_, r) = term(r#"(c ++ a) <| b c"#).unwrap();
  similar!(
    r,
    opr(
      opr(var("c"), NameRef::Op("++".into()), var("a")),
      NameRef::Op("<|".into()),
      app(var("b"), var("c"))
    )
  );
  let (_, r) = term(r#"(\a => (a b) c) 5"#).unwrap();
  similar!(
    r,
    app(
      lams(vec![par("a")], app(app(var("a"), var("b")), var("c"))),
      num(5)
    )
  );
  let (_, r) = term(r#"\b => {a := b, c:="Hello", map := {}}"#).unwrap();
  similar!(
    r,
    lams(
      vec![par("b")],
      Term::Lit {
        value: Literal::StructLit {
          fields: Map::from([
            (id("a"), var("b")),
            (id("c"), str("Hello")),
            (
              id("map"),
              Term::Lit {
                value: Literal::StructLit {
                  fields: Map::new(),
                  type_name: None
                }
              }
            )
          ]),
          type_name: None
        }
      }
    )
  );
}

#[test]
fn test_ann_term() {
  let term = |s: &'static str| term::<()>(s.into());
  let result = term(r#"(x : String)"#);
  assert!(result.is_ok(), "parse failed: {:?}", result);
  let result = term(r#"(1 : I64)"#);
  assert!(result.is_ok(), "parse failed: {:?}", result);
}
