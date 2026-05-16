use super::*;

#[test]
fn test_attr_arg_named() {
  let s = r#"@[deprecated {since := "1.0", reason := "use new"}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("deprecated"),
    args: vec![
      AttrArg::Named {
        name: id("since"),
        value: Box::new(AttrArg::Str("1.0".to_string())),
      },
      AttrArg::Named {
        name: id("reason"),
        value: Box::new(AttrArg::Str("use new".to_string())),
      },
    ],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_nested() {
  let s = r#"@[custom {outer := {inner := value}}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Named {
      name: id("outer"),
      value: Box::new(AttrArg::Named {
        name: id("inner"),
        value: Box::new(AttrArg::Ident(id("value"))),
      }),
    }],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_mixed() {
  let s = r#"@[custom "arg1" {key := 42} another_arg]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![
      AttrArg::Str("arg1".to_string()),
      AttrArg::Named {
        name: id("key"),
        value: Box::new(AttrArg::Num(42)),
      },
      AttrArg::Ident(id("another_arg")),
    ],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_native_with_named_arg() {
  let s = r#"@[native {name := num_add}]
    def add (a b : I64) : I64
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let native_term = Term::Ntv {
    native: Native {
      native_name: id("num_add"),
      num_args: 2,
      args: vec![None, None],
    },
  };
  let expected_term = Term::Lam {
    param: Par::I {
      typ: Box::new(typ("I64")),
      mult: Multiplicity::Many,
    },
    body: Box::new(Term::Lam {
      param: Par::I {
        typ: Box::new(typ("I64")),
        mult: Multiplicity::Many,
      },
      body: Box::new(native_term),
    }),
  };

  similar!(
    res.value(),
    &Decl::Def(def(
      mpt("add"),
      vec![],
      pi(typ("I64"), pi(typ("I64"), typ("I64"))),
      expected_term,
      vec![Attribute {
        name: id("native"),
        args: vec![AttrArg::Named {
          name: id("name"),
          value: Box::new(AttrArg::Ident(id("num_add")))
        }]
      }]
    ))
  );
}

#[test]
fn test_attr_arg_group() {
  let s = r#"@[custom [1, "hello", ident]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Group(vec![
      AttrArg::Num(1),
      AttrArg::Str("hello".to_string()),
      AttrArg::Ident(id("ident")),
    ])],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_group_trailing_comma() {
  let s = r#"@[custom [1, 2,]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Group(vec![AttrArg::Num(1), AttrArg::Num(2)])],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_nested_group() {
  let s = r#"@[custom {outer := {a := 1, b := 2}}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Named {
      name: id("outer"),
      value: Box::new(AttrArg::Group(vec![
        AttrArg::Named {
          name: id("a"),
          value: Box::new(AttrArg::Num(1)),
        },
        AttrArg::Named {
          name: id("b"),
          value: Box::new(AttrArg::Num(2)),
        },
      ])),
    }],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_named_with_group() {
  let s = r#"@[custom {outer := [1, 2, 3]}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Named {
      name: id("outer"),
      value: Box::new(AttrArg::Group(vec![
        AttrArg::Num(1),
        AttrArg::Num(2),
        AttrArg::Num(3),
      ])),
    }],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_arg_nested_groups() {
  let s = r#"@[custom [[1, 2], [3, 4]]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("custom"),
    args: vec![AttrArg::Group(vec![
      AttrArg::Group(vec![AttrArg::Num(1), AttrArg::Num(2)]),
      AttrArg::Group(vec![AttrArg::Num(3), AttrArg::Num(4)]),
    ])],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_test() {
  let s = r#"@[test]
    def test_addition : Bool :=
        1 + 1 == 2
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("test"),
    args: vec![],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_native_string() {
  let s = r#"@[native "eq_rec"]
    def eq_rec {A : Sort 1} {a : A} {b : A} (P : (b : A) -> Eq A a b -> Sort 1) (h : P a (Eq.refl a)) (e : Eq A a b) : P b e
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("native"),
    args: vec![AttrArg::Str("eq_rec".to_string())],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_terminating() {
  let s = r#"@[terminating]
    def factorial (n : I64) : I64 :=
        if n == 0
        then 1
        else n * factorial (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("terminating"),
    args: vec![],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_partial() {
  let s = r#"@[partial]
    def arbitrary (n : I64) : I64 :=
        if n == 0
        then 1
        else arbitrary (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    name: id("partial"),
    args: vec![],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}
