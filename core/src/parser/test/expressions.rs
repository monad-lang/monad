use super::*;

#[test]
fn test_lambda() {
  let lambda = |s: &'static str| lambda::<()>(s.into());
  let (_, r) = lambda(r#"\a => a"#.into()).unwrap();
  similar!(r, lams(vec![par("a")], var("a")));

  let (_, r) = lambda("\\a b \n=>\n a".into()).unwrap();
  similar!(r, lams(vec![par("a"), par("b")], var("a")));
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
      value: Literal::StructLit { fields: Map::new() }
    }
  );
  let (_, r) = p(r#"{a := b}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::from([(id("a"), var("b"))])
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
                fields: Map::from([(id("c"), num(0))])
              }
            }
          )
        ])
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
                value: Literal::StructLit { fields: Map::new() }
              }
            )
          ])
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
