use super::*;

#[test]
fn test_attr_arg_named() {
  let s = r#"@[deprecated {since := "1.0", reason := "use new"}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
        source_location: Default::default(),
        legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
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
    source_location: Default::default(),
    legacy_syntax: false,
    name: id("partial"),
    args: vec![],
  }];

  match res.value() {
    Decl::Def(def) => assert_eq!(def.attributes, expected_attrs),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_cfg_test_on_use() {
  let s = r#"@[cfg test]
    use std.test
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
    legacy_syntax: false,
    name: id("cfg"),
    args: vec![AttrArg::Ident(id("test"))],
  }];

  match res.value() {
    Decl::Use(u) => assert_eq!(u.attributes, expected_attrs),
    _ => panic!("expected Use, got {:?}", res.value()),
  }
}

#[test]
fn test_attr_cfg_test_on_open() {
  let s = r#"@[cfg test]
    open IO
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
    legacy_syntax: false,
    name: id("cfg"),
    args: vec![AttrArg::Ident(id("test"))],
  }];

  match res.value() {
    Decl::Open(o) => assert_eq!(o.attributes, expected_attrs),
    _ => panic!("expected Open, got {:?}", res.value()),
  }
}

// --- #[...] (current syntax) vs @[...] (deprecated syntax) ---

#[test]
fn test_attr_hash_test() {
  // `#[test]` parses identically to `@[test]`, just via the new delimiter.
  let s = r#"#[test]
    def test_addition : Bool :=
        1 + 1 == 2
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  match res.value() {
    Decl::Def(def) => {
      assert_eq!(def.attributes.len(), 1);
      assert_eq!(def.attributes[0].name, id("test"));
      assert!(def.attributes[0].args.is_empty());
      assert!(!def.attributes[0].legacy_syntax);
    }
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_hash_native_string() {
  let s = r#"#[native "eq_rec"]
    def eq_rec {A : Sort 1} {a : A} {b : A} (P : (b : A) -> Eq A a b -> Sort 1) (h : P a (Eq.refl a)) (e : Eq A a b) : P b e
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  match res.value() {
    Decl::Def(def) => {
      assert_eq!(def.attributes.len(), 1);
      assert_eq!(def.attributes[0].name, id("native"));
      assert_eq!(
        def.attributes[0].args,
        vec![AttrArg::Str("eq_rec".to_string())]
      );
      assert!(!def.attributes[0].legacy_syntax);
    }
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_hash_partial() {
  let s = r#"#[partial]
    def arbitrary (n : I64) : I64 :=
        if n == 0
        then 1
        else arbitrary (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Def(def) => assert!(def.has_partial_attr()),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_attr_on_type_struct_class_instance() {
  // Regression: `type`/`struct`/`class`/`instance` parsers each called
  // `opt_attributes` but never consumed the whitespace/newline between the
  // attribute and their own keyword (unlike `def_parser`, which does) — so
  // `#[foo]\ntype X { ... }` (the conventional one-attribute-per-line style
  // used everywhere for `#[test]\ndef ...`) silently failed to parse for
  // every non-`def` declaration kind. Fixed by adding the missing `ws0`.
  let s = r#"#[test]
    type Foo { mk }
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Type(induct) => assert!(induct.has_attr("test")),
    other => panic!("expected Decl::Type, got {other:?}"),
  }

  let s = r#"#[test]
    struct Bar { x : I64 }
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Type(induct) => assert!(induct.has_attr("test")),
    other => panic!("expected Decl::Type, got {other:?}"),
  }

  let s = r#"#[test]
    class MyClass A { def m : A }
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  assert!(
    matches!(res.value(), Decl::Type(_)),
    "expected Decl::Type (class)"
  );

  let s = r#"#[test]
    instance MyClass I64 { def m : I64 := 0 }
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  assert!(matches!(res.value(), Decl::Ins(_)), "expected Decl::Ins");
}

#[test]
fn test_attr_hash_terminating() {
  let (_, res) = attribute_parser::<()>(r#"#[terminating]"#.into()).unwrap();
  assert_eq!(res.name, id("terminating"));
  assert!(res.args.is_empty());
  assert!(!res.legacy_syntax);
}

#[test]
fn test_attr_hash_cfg_test_on_use() {
  let s = r#"#[cfg test]
    use std.test
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Use(u) => {
      assert_eq!(u.attributes.len(), 1);
      assert_eq!(u.attributes[0].name, id("cfg"));
      assert!(!u.attributes[0].legacy_syntax);
    }
    _ => panic!("expected Use, got {:?}", res.value()),
  }
}

#[test]
fn test_legacy_syntax_flag() {
  // `@[...]` sets legacy_syntax: true; `#[...]` sets it false; both parse
  // to the exact same name/args content.
  let (_, at) = attribute_parser::<()>(r#"@[native num_add]"#.into()).unwrap();
  let (_, hash) = attribute_parser::<()>(r#"#[native num_add]"#.into()).unwrap();
  assert!(at.legacy_syntax);
  assert!(!hash.legacy_syntax);
  assert_eq!(at, hash); // PartialEq ignores legacy_syntax/source_location
}

#[test]
fn test_multiple_attributes_mixed_syntax() {
  // Both delimiters can be mixed on the same declaration.
  let s = r#"@[partial] #[test]
    def f (n : I64) : I64 :=
        if n == 0
        then 1
        else f (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Def(def) => {
      assert_eq!(def.attributes.len(), 2);
      assert!(def.attributes[0].legacy_syntax);
      assert!(!def.attributes[1].legacy_syntax);
    }
    _ => panic!("expected Def"),
  }
}
