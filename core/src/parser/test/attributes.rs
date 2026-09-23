use super::*;

#[test]
fn test_attr_arg_named() {
  let s = r#"#[deprecated {since := "1.0", reason := "use new"}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom {outer := {inner := value}}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom "arg1" {key := 42} another_arg]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[native {name := num_add}]
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
      npt("add"),
      vec![],
      pi(typ("I64"), pi(typ("I64"), typ("I64"))),
      expected_term,
      vec![Attribute {
        source_location: Default::default(),
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
  let s = r#"#[custom [1, "hello", ident]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom [1, 2,]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom {outer := {a := 1, b := 2}}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom {outer := [1, 2, 3]}]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[custom [[1, 2], [3, 4]]]
    def foo : IO Unit := println "hi"
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[test]
    def test_addition : Bool :=
        1 + 1 == 2
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[native "eq_rec"]
    def eq_rec {A : Sort 1} {a : A} {b : A} (P : (b : A) -> Eq A a b -> Sort 1) (h : P a (Eq.refl a)) (e : Eq A a b) : P b e
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[terminating]
    def factorial (n : I64) : I64 :=
        if n == 0
        then 1
        else n * factorial (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[partial]
    def arbitrary (n : I64) : I64 :=
        if n == 0
        then 1
        else arbitrary (n - 1)
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[cfg test]
    use std::test
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
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
  let s = r#"#[cfg test]
    open IO
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
    name: id("cfg"),
    args: vec![AttrArg::Ident(id("test"))],
  }];

  match res.value() {
    Decl::Open(o) => assert_eq!(o.attributes, expected_attrs),
    _ => panic!("expected Open, got {:?}", res.value()),
  }
}

#[test]
fn test_attr_hash_test() {
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
}

#[test]
fn test_attr_hash_cfg_test_on_use() {
  let s = r#"#[cfg test]
    use std::test
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Use(u) => {
      assert_eq!(u.attributes.len(), 1);
      assert_eq!(u.attributes[0].name, id("cfg"));
    }
    _ => panic!("expected Use, got {:?}", res.value()),
  }
}

#[test]
fn test_multiple_attributes_stacked() {
  // Several `#[...]` attributes can stack on the same declaration.
  let s = r#"#[partial] #[test]
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
      assert_eq!(def.attributes[0].name, id("partial"));
      assert_eq!(def.attributes[1].name, id("test"));
    }
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_extern_c_basic() {
  // FFI is a self-hosted-compiler-only feature: the Rust host keeps no C
  // bridge, so `#[extern "c"]` parses to an ordinary `Term::Ntv` under
  // the def's OWN name, exactly like `#[export "c"]`. The attribute stays
  // on the def — that is what `module_warnings`' `extern_attr_warnings`
  // scans for — and evaluating the def fails with `unknown native: puts`.
  let s = r#"#[extern "c"]
    def puts (s : String) : I64
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  let native = unwrap_ntv_body(res.value());
  assert_eq!(native.native_name, id("puts"));
  assert_eq!(native.num_args, 1);
  match res.value() {
    Decl::Def(d) => assert_eq!(d.attributes[0].name, id("extern")),
    _ => panic!("expected Def"),
  }
}

#[test]
fn test_extern_c_with_lib_and_link_name() {
  // `link_name`/`lib`/`nullable` are interpreted only by the self-hosted
  // codegen (lang/codegen/emit.mo). The Rust host parses the attribute
  // args without acting on them, so the native keeps the def's own name
  // — `link_name := "puts"` does NOT rename it to `puts`.
  let s = r#"#[extern "c" {lib := "m", link_name := "puts", nullable := true}]
    def puts_ (s : String) : I64
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  let native = unwrap_ntv_body(res.value());
  assert_eq!(native.native_name, id("puts_"));
  assert_eq!(native.num_args, 1);
}

/// Peel `Lam`s off the def body to reach the inner `Term::Ntv`.
fn unwrap_ntv_body(decl: &Decl) -> &Native {
  let mut term = match decl {
    Decl::Def(d) => &d.term,
    _ => panic!("expected Def"),
  };
  loop {
    match term {
      Term::Lam { body, .. } => term = body,
      Term::Ntv { native } => return native,
      _ => panic!("expected Ntv at body core, got {:?}", term),
    }
  }
}

#[test]
fn test_extern_c_plus_plus_parses() {
  // ABI validation now belongs to the self-hosted compiler, which is the
  // only thing that lowers externs. The Rust host no longer inspects the
  // ABI string at all, so `#[extern "c++"]` parses like any other
  // codegen-only attribute instead of being a parse error.
  //
  // (The pre-removal version of this test wrote the def as `def f () : I64`
  // and asserted only `is_err()`. That passed for the wrong reason: empty
  // parens are a syntax error in any def, extern or not, so the assertion
  // never actually exercised the ABI check it named.)
  let s = r#"#[extern "c++"]
    def f (x : I64) : I64
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();
  let native = unwrap_ntv_body(res.value());
  assert_eq!(native.native_name, id("f"));
}

#[test]
fn test_mote_inner_attr_parses_as_a_decl() {
  // `#![mote { ... }]` is a DECLARATION in the AST, not a prefix on the
  // next one -- that is what lets a misplaced one reach
  // `validate_mote_attr_position` (`lang/src/module.mo`, the self-hosted
  // compiler) as a real diagnostic instead of stopping the parse. The host
  // only parses it; what this test pins is the AST shape both compilers
  // must agree on.
  let s = r#"#![mote { name := "structs", deps := [init, std] }]
    def foo : I64 := 1
    "#
  .into();
  let (_, res) = decl_parser(s).unwrap();

  let expected_attrs = vec![Attribute {
    source_location: Default::default(),
    name: id("mote"),
    // The FLATTENED shape: `attr_arg_parser` returns a `Vec` per call,
    // so the `{ ... }` block's `Named` entries land directly on
    // `attr.args`. The self-hosted parser wraps them in one
    // `AttrArg::Group` instead -- see `mote_attr_parser`'s doc comment.
    // Both readers must accept this shape.
    args: vec![
      AttrArg::Named {
        name: id("name"),
        value: Box::new(AttrArg::Str("structs".to_string())),
      },
      AttrArg::Named {
        name: id("deps"),
        value: Box::new(AttrArg::Group(vec![
          AttrArg::Ident(id("init")),
          AttrArg::Ident(id("std")),
        ])),
      },
    ],
  }];

  match res.value() {
    Decl::MoteAttr { attr } => assert_eq!(*attr, expected_attrs[0]),
    _ => panic!("expected MoteAttr, got {:?}", res.value()),
  }
}

#[test]
fn test_mote_inner_attr_does_not_consume_the_next_decl() {
  // The failure mode this guards: if the attribute were parsed as a
  // prefix, `decl_parser` would return the DEF and the attribute would
  // be silently lost.
  let s = r#"#![mote { name := "solo" }]
    def foo : I64 := 1
    "#
  .into();
  let (rem, res) = decl_parser(s).unwrap();
  assert!(matches!(res.value(), Decl::MoteAttr { .. }));
  let (_, next) = decl_parser(rem).unwrap();
  assert!(matches!(next.value(), Decl::Def(_)));
}

#[test]
fn test_mote_inner_attr_parses_in_a_whole_file() {
  use crate::parser::parse_file;
  let s = r#"#![mote { name := "x" }]
    def foo : I64 := 1
    "#
  .into();
  let parsed = parse_file(s).unwrap();
  let kinds: Vec<&Decl> = parsed.decls.iter().map(|d| d.value()).collect();
  assert!(
    matches!(kinds.first(), Some(Decl::MoteAttr { .. })),
    "first decl should be the mote attribute, got {:?}",
    kinds.first()
  );
  assert!(
    matches!(kinds.get(1), Some(Decl::Def(_))),
    "second decl should be the def, got {:?}",
    kinds.get(1)
  );
}
