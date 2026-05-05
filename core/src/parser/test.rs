use super::*;
use crate::{
  Map, similar,
  term::{
    AttrArg, Attribute, Decl, LetVar, Literal, Named, Native, Par, Term, app, app2, dpar, forall,
    induct_constructor, mp, mpt, mpv, num, oper, par, pi, pi_var, pvar, str, stru_field,
    test::{decl_def, decl_inductive, decl_infix, decl_open, decl_use, defs_class},
    typ, var,
  },
};

#[test]
fn test_string_litteral() {
  let p = |i: Span<'static, ()>| string_literal::<()>(i);
  let (_, r) = p(r#""It's a test \"Hello, World\"""#.into()).unwrap();
  similar!(r, str(r#"It's a test "Hello, World""#.into()));
  assert!(p("abc".into()).is_err());
  assert!(p(r#""abc"#.into()).is_err());
}

#[test]
fn test_blank() {
  use nom::combinator::all_consuming;
  all_consuming(ws0::<()>).parse("".into()).unwrap();
  all_consuming(ws0::<()>)
    .parse(
      r#"

      
    "#
      .into(),
    )
    .unwrap();
  all_consuming(ws0::<()>)
    .parse(
      r#"
      // test
      // 1
      /* test */
    "#
      .into(),
    )
    .unwrap();
  all_consuming(ws1::<()>)
    .parse(
      r#"
      // test
      // 1
      /* test */
    "#
      .into(),
    )
    .unwrap();
  assert!(ws1::<()>("".into()).is_err());
}

#[test]
fn test_decl_space() {
  use nom::combinator::all_consuming;
  assert!(
    all_consuming(line_comment_not_doc::<()>)
      .parse("// test".into())
      .is_ok()
  );
  assert!(
    all_consuming(line_comment_not_doc::<()>)
      .parse("/// test".into())
      .is_err()
  );
  // Test: doc comment followed by // comments consumed, returns Some(doc)
  let (_, r) = all_consuming(decls_space_parser::<()>)
    .parse(
      r#"/// test
    //
    //

  "#
      .into(),
    )
    .unwrap();
  assert!(r.is_some());
  assert_eq!(r.unwrap().value, "test");
}

#[test]
fn test_identifier() {
  let (_, r) = identifier::<()>("abc_".into()).unwrap();
  similar!(r, id("abc_"));
  assert!(identifier::<()>("let".into()).is_err());
  assert!(identifier::<()>("def".into()).is_err());
  assert!(identifier::<()>("in".into()).is_err());
}

pub fn parse_type(input: &str) -> Term {
  let t = type_top_expression::<()>(input.into()).finish().unwrap().1;
  t
}

#[test]
fn test_infix() {
  let s = r#"infix (+) := add"#.into();
  let (_, res) = infix_parser(s).unwrap();

  similar!(res, infix("+".into(), mpt("add")));
}

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

#[test]
fn test_class() {
  let s = r#"class Functor (F: Type -> Type) {
    	def map (f: A -> B) : (F A) -> F B
    }
    "#
  .into();
  let (_, res) = class_parser(s).unwrap();

  similar!(
    res,
    class(
      mpt("Functor"),
      vec![],
      vec![dpar("F", pi(typ("Type"), typ("Type")))],
      vec![class_def(
        id("map"),
        pi(pi(typ("A"), typ("B")), pi(app2("F", "A"), app2("F", "B"))),
        None,
        vec![],
        None
      )],
      vec![]
    )
  );
  let s = r#"class [Functor F] Applicative F {
        def pure : A -> F A
        def apply : F (A -> B) -> F A -> F B
    }
    "#
  .into();
  let (_, res) = class_parser(s).unwrap();

  similar!(
    res,
    class(
      mpt("Applicative"),
      vec![type_constraint(mpt("Functor"), vec![id("F")])],
      vec![par("F")],
      vec![
        class_def(id("pure"), pi(typ("A"), app2("F", "A")), None, vec![], None),
        class_def(
          id("apply"),
          pi(
            app(typ("F"), pi(typ("A"), typ("B"))),
            pi(app2("F", "A"), app2("F", "B"))
          ),
          None,
          vec![],
          None
        )
      ],
      vec![]
    )
  );
  let s = r#"class [Applicative M] Monad (M: Type -> Type) {
        def pure (a: A) : M A
        def bind (a : M A) (f : A -> M B) : M B
    }
    "#
  .into();
  let (_, res) = class_parser(s).unwrap();

  similar!(
    res,
    class(
      mpt("Monad"),
      vec![type_constraint(mpt("Applicative"), vec![id("M")])],
      vec![dpar("M", pi(typ("Type"), typ("Type")))],
      vec![
        class_def(id("pure"), pi(typ("A"), app2("M", "A")), None, vec![], None),
        class_def(
          id("bind"),
          pi(
            app2("M", "A"),
            pi(pi(typ("A"), app2("M", "B")), app2("M", "B"))
          ),
          None,
          vec![],
          None
        )
      ],
      vec![]
    )
  );
}

#[test]
fn test_def_param() {
  let def_param = |s: &'static str| def_param::<()>(s.into());
  let (_, r) = def_param(r#"(a : String)"#.into()).unwrap();
  similar!(r, vec![dpar("a", typ("String"))]);
  let (_, r) = def_param(r#"(a b : String)"#.into()).unwrap();
  similar!(r, vec![dpar("a", typ("String")), dpar("b", typ("String"))]);
  let (_, r) = def_param(r#"(a : String -> Option Int)"#.into()).unwrap();
  similar!(r, vec![dpar("a", pi(typ("String"), app2("Option", "Int")))]);
}

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
  let struct_val_parser = |s: &'static str| struct_val_parser::<()>(s.into());
  let (_, r) = struct_val_parser(r#"{}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit { fields: Map::new() }
    }
  );
  let (_, r) = struct_val_parser(r#"{a := b}"#.into()).unwrap();
  similar!(
    r,
    Term::Lit {
      value: Literal::StructLit {
        fields: Map::from([(id("a"), var("b"))])
      }
    }
  );
  let (_, r) = struct_val_parser(r#"{a := b, b:={c:=0},}"#.into()).unwrap();
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
#[test]
fn test_inductive() {
  let s = r#"type Solo {
        solo
    }
    "#
  .into();
  let (_, res) = inductive_parser(s).unwrap();

  similar!(
    res,
    inductive(
      mpt("Solo"),
      vec![],
      vec![],
      Hole,
      vec![induct_constructor(
        mpt("Solo"),
        id("solo"),
        mpv("Solo"),
        vec![]
      )],
      vec![]
    )
  );
  let s = r#"type Result E A  {
         ok (a:A), err E
     }
     "#
  .into();
  let (_, res) = inductive_parser(s).unwrap();

  let res_t = app(app(mpv("Result"), var("E")), var("A"));
  similar!(
    res,
    inductive(
      mpt("Result"),
      vec![],
      vec![par("E"), par("A")],
      Hole,
      vec![
        induct_constructor(
          mpt("Result"),
          id("ok"),
          pi(typ("A"), res_t.clone()),
          vec![dpar("a", typ("A"))]
        ),
        induct_constructor(
          mpt("Result"),
          id("err"),
          pi(typ("E"), res_t),
          vec![dpar("", typ("E"))]
        )
      ],
      vec![]
    )
  );
}

#[test]
fn test_instance() {
  let s = r#"instance Functor F {
    	def map (f: A -> B) (v: F A) : F B := 
    	    f |> v
    }
    "#
  .into();
  let (_, res) = instance_parser(s).unwrap();

  similar!(
    res,
    instance(
      None,
      mpt("Functor"),
      vec![],
      vec![var("F")],
      vec![def(
        mpt("map"),
        vec![],
        pi(pi(typ("A"), typ("B")), pi(app2("F", "A"), app2("F", "B"))),
        lams(
          vec![dpar("f", pi(typ("A"), typ("B"))), dpar("v", app2("F", "A"))],
          oper(var("f"), "|>", var("v"))
        ),
        vec![]
      )],
      vec![]
    )
  );
}

#[test]
fn test_struct() {
  let struct_parser = |s: &'static str| struct_parser::<()>(s.into());
  let s = r#"struct MyData {
        data : MyData,
        field_type : Type,
        text : String := "default",
    }
    "#
  .into();
  let (_, res) = struct_parser(s).unwrap();

  similar!(
    res,
    stru(
      mpt("MyData"),
      vec![],
      vec![],
      vec![
        stru_field(id("data"), typ("MyData"), None),
        stru_field(id("field_type"), typ("Type"), None),
        stru_field(id("text"), typ("String"), Some(str("default")))
      ],
      vec![]
    )
  );
  let s = r#"struct [Serialize M] MyData (M: Type) {
         data : M,
         text : String := "default",
     }
     "#
  .into();
  let (_, res) = struct_parser(s).unwrap();

  similar!(
    res,
    stru(
      mpt("MyData"),
      vec![type_constraint(mpt("Serialize"), vec![id("M")])],
      vec![dpar("M", typ("Type"))],
      vec![
        stru_field(id("data"), typ("M"), None),
        stru_field(id("text"), typ("String"), Some(str("default")))
      ],
      vec![]
    )
  );
}

#[test]
fn test_native() {
  let s = r#"@[native num_add]
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
        args: vec![AttrArg::Ident(id("num_add"))]
      }]
    ))
  );
}

#[test]
fn test_def() {
  let s = r#"def test [Monad M] {M: Type -> Type} (arg : M String) : M Unit :=
        arg >>= (fn _ => pure unit)
    "#
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
  let s = r#"def main (args : List String) : IO Unit :=
         println "Hello, world!"
     "#
  .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("main"),
      vec![],
      pi(app2("List", "String"), app2("IO", "Unit")),
      lams(
        vec![dpar("args", app2("List", "String"))],
        apps(var("println"), vec![str("Hello, world!")])
      ),
      vec![]
    )
  );
  let s = r#"def IO.say.hello : IO Unit :=
         println "Hello, world!"
     "#
  .into();
  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mp(vec!["IO", "say", "hello"]),
      vec![],
      app2("IO", "Unit"),
      apps(var("println"), vec![str("Hello, world!")]),
      vec![]
    )
  );
  let s = r#"def Lens [Functor F] (S: Type) (T: Type) (A: Type) (B : Type) : Type :=
 	(A -> F B) -> S -> F T
 	"#
  .into();

  let (_, res) = def_parser(s).unwrap();

  similar!(
    res,
    def(
      mpt("Lens"),
      vec![type_constraint(mpt("Functor"), vec![id("F")])],
      pi_typs(
        vec![typ("Type"), typ("Type"), typ("Type"), typ("Type")],
        typ("Type")
      ),
      lams(
        vec![
          dpar("S", typ("Type")),
          dpar("T", typ("Type")),
          dpar("A", typ("Type")),
          dpar("B", typ("Type")),
        ],
        pi(pi(typ("A"), app2("F", "B")), pi(typ("S"), app2("F", "T")))
      ),
      vec![]
    )
  );
}

#[test]
fn module_test() {
  let s = r#"
    use std.string.trim
    type Bool {
      true,
      false,
    }
    open Bool
    // This is a test
    def test : IO Unit/* test*/ :=
        println "Hello, world!"
    def fun2 : String := "test"
    def append (a b : List A) : List A := todo
    infix (++) := append

    class Functor (F: Type -> Type) {
    	def map (f: A -> B) : (F A) -> F B
    }
    "#;
  let m: Vec<Decl> = parse_file(s.into())
    .unwrap()
    .decls
    .into_iter()
    .map(|f| f.value().clone())
    .collect();
  similar!(
    m,
    vec![
      decl_use(vec!["std", "string", "trim"]),
      decl_inductive(
        mpt("Bool"),
        vec![],
        vec![],
        mpv("Bool"),
        vec![
          induct_constructor(mpt("Bool"), id("true"), mpv("Bool"), vec![]),
          induct_constructor(mpt("Bool"), id("false"), mpv("Bool"), vec![])
        ]
      ),
      decl_open(vec!["Bool"]),
      decl_def(
        mpt("test"),
        vec![],
        app2("IO", "Unit"),
        apps(var("println"), vec![str("Hello, world!")])
      ),
      decl_def(mpt("fun2"), vec![], typ("String"), str("test")),
      decl_def(
        mpt("append"),
        vec![],
        pi(app2("List", "A"), pi(app2("List", "A"), app2("List", "A"))),
        lams(
          vec![dpar("a", app2("List", "A")), dpar("b", app2("List", "A"))],
          var("todo"),
        )
      ),
      decl_infix("++".into(), mpt("append")),
      defs_class(
        mpt("Functor"),
        vec![],
        vec![dpar("F", pi(typ("Type"), typ("Type")))],
        vec![class_def(
          id("map"),
          pi(pi(typ("A"), typ("B")), pi(app2("F", "A"), app2("F", "B"))),
          None,
          vec![],
          None
        )]
      )
    ]
  );
}

#[test]
fn test_do_parser_simple_return() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { return 1 }"#).unwrap();
  similar!(r, num(1));
}

#[test]
fn test_do_parser_simple_bind() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x <- monadic; return x }"#).unwrap();
  let expected = app(
    pvar(vec!["Monad", "bind"]),
    app(var("monadic"), lam(par("x"), var("x"))),
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
      pvar(vec!["Monad", "bind"]),
      app(var("monadic"), lam(par("y"), var("y"))),
    ),
  );
  similar!(r, expected);
}

#[test]
fn test_do_parser_multiple_binds() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let a <- ma; let b <- mb; return b }"#).unwrap();
  let inner = app(
    pvar(vec!["Monad", "bind"]),
    app(var("mb"), lam(par("b"), var("b"))),
  );
  let expected = app(
    pvar(vec!["Monad", "bind"]),
    app(var("ma"), lam(par("a"), inner)),
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
    pvar(vec!["Monad", "bind"]),
    app(var("get"), lam(par("y"), var("y"))),
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
fn test_list_literal_empty() {
  let list = |s: &'static str| list_literal::<()>(s.into());
  let (_, r) = list("[]").unwrap();
  let expected = pvar(vec!["FromListLiteral", "empty"]);
  similar!(r, expected);
}

#[test]
fn test_list_literal_single() {
  let list = |s: &'static str| list_literal::<()>(s.into());
  let (_, r) = list("[x]").unwrap();
  let expected = app(
    app(pvar(vec!["FromListLiteral", "cons"]), var("x")),
    pvar(vec!["FromListLiteral", "empty"]),
  );
  similar!(r, expected);
}

#[test]
fn test_list_literal_multiple() {
  let list = |s: &'static str| list_literal::<()>(s.into());
  let (_, r) = list("[a, b, c]").unwrap();
  let inner = app(
    app(pvar(vec!["FromListLiteral", "cons"]), var("c")),
    pvar(vec!["FromListLiteral", "empty"]),
  );
  let middle = app(app(pvar(vec!["FromListLiteral", "cons"]), var("b")), inner);
  let expected = app(app(pvar(vec!["FromListLiteral", "cons"]), var("a")), middle);
  similar!(r, expected);
}

#[test]
fn test_list_literal_spaces() {
  let list = |s: &'static str| list_literal::<()>(s.into());
  let (_, r) = list("[ a , b ]").unwrap();
  let inner = app(
    app(pvar(vec!["FromListLiteral", "cons"]), var("b")),
    pvar(vec!["FromListLiteral", "empty"]),
  );
  let expected = app(app(pvar(vec!["FromListLiteral", "cons"]), var("a")), inner);
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
    def(mpt("get_one"), vec![], app2("IO", "I64"), num(1), vec![])
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
    pvar(vec!["Monad", "bind"]),
    app(var("get_value"), lam(par("x"), var("x"))),
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
    var("x"),
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
    pvar(vec!["Monad", "bind"]),
    app(
      apps(var("println"), vec![str("first")]),
      lam(par("_"), apps(var("println"), vec![str("second")])),
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
fn test_docstring_def() {
  let s: Span<'static, ()> = r#"/// Adds two integers
def add (a b: I64) : I64 := a + b
"#
  .into();
  let (_, res) = def_parser(s).unwrap();
  let expected_body = oper(var("a"), "+", var("b"));
  similar!(
    res,
    def(
      mpt("add"),
      vec![],
      pi(typ("I64"), pi(typ("I64"), typ("I64"))),
      lams(
        vec![dpar("a", typ("I64")), dpar("b", typ("I64"))],
        expected_body
      ),
      vec![]
    )
  );
}

#[test]
fn test_docstring_class() {
  let s: Span<'static, ()> = r#"/// The Functor class
class Functor (F: Type -> Type) {
    def map (f: A -> B) : F A -> F B
}
"#
  .into();
  let (_, ctx) = decl_parser(s).unwrap();
  similar!(
    ctx.value(),
    &Decl::Type(class(
      mpt("Functor"),
      vec![],
      vec![dpar("F", pi(typ("Type"), typ("Type")))],
      vec![class_def(
        id("map"),
        pi(pi(typ("A"), typ("B")), pi(app2("F", "A"), app2("F", "B"))),
        None,
        vec![],
        None
      )],
      vec![]
    ))
  );
  assert!(ctx.doc.is_some());
}

#[test]
fn test_docstring_struct() {
  let s: Span<'static, ()> = r#"/// A point in 2D space
struct Point {
    x: I64,
    y: I64,
}
"#
  .into();
  let (_, ctx) = decl_parser(s).unwrap();
  similar!(
    ctx.value(),
    &Decl::Type(stru(
      mpt("Point"),
      vec![],
      vec![],
      vec![
        stru_field(id("x"), typ("I64"), None),
        stru_field(id("y"), typ("I64"), None),
      ],
      vec![]
    ))
  );
  assert!(ctx.doc.is_some());
}

#[test]
fn test_docstring_inductive() {
  let s: Span<'static, ()> = r#"/// Optional values
type Option A {
    some (a: A),
    none
}
"#
  .into();
  let (_, ctx) = decl_parser(s).unwrap();
  let option_typ = app(mpv("Option"), var("A"));
  similar!(
    ctx.value(),
    &Decl::Type(inductive(
      mpt("Option"),
      vec![],
      vec![par("A")],
      Hole,
      vec![
        induct_constructor(
          mpt("Option"),
          id("some"),
          pi(typ("A"), option_typ.clone()),
          vec![dpar("a", typ("A"))]
        ),
        induct_constructor(mpt("Option"), id("none"), option_typ, vec![])
      ],
      vec![]
    ))
  );
  assert!(ctx.doc.is_some());
}

#[test]
fn test_docstring_instance() {
  let s: Span<'static, ()> = r#"/// Instance for lists
instance Functor List {
    def map (f: A -> B) (v: List A) : List B := v |> map f
}
"#
  .into();
  let (_, ctx) = decl_parser(s).unwrap();
  similar!(
    ctx.value(),
    &Decl::Ins(instance(
      None,
      mpt("Functor"),
      vec![],
      vec![var("List")],
      vec![def(
        mpt("map"),
        vec![],
        pi(
          pi(typ("A"), typ("B")),
          pi(app2("List", "A"), app2("List", "B"))
        ),
        lams(
          vec![
            dpar("f", pi(typ("A"), typ("B"))),
            dpar("v", app2("List", "A"))
          ],
          oper(var("v"), "|>", app(var("map"), var("f")))
        ),
        vec![]
      )],
      vec![]
    ))
  );
  assert!(ctx.doc.is_some());
}

#[test]
fn test_module_with_docstrings() {
  let s: Span<'static, ()> = r#"/// The Option type represents an optional value
type Option A {
    some (a: A),
    none
}

/// The Functor class for mapping over wrapped values
class Functor (F: Type -> Type) {
    /// Map a function over a functor
    def map (f: A -> B) : F A -> F B
}

/// Functor instance for Option
instance Functor (Option A) {
    def map (f: A -> B) (v: Option A) : Option B :=
        match v {
            some a => some (f a),
            none => none
        }
}
"#
  .into();

  let (_, parsed) = decls_parser(s).unwrap();
  let decls = &parsed.decls;
  assert_eq!(decls.len(), 3);

  // Check first decl - Option type
  let opt_decl = &decls[0];
  match opt_decl.value() {
    Decl::Type(ind) => {
      assert_eq!(ind.name().as_str(), Some("Option"));
    }
    _ => panic!("Expected Type decl"),
  }

  // Check second decl - Functor class
  let functor_decl = &decls[1];
  match functor_decl.value() {
    Decl::Type(ind) => {
      assert_eq!(ind.name().as_str(), Some("Functor"));
      // Check class method doc
      // Note: class methods are stored in a special way, need to verify doc parsing
    }
    _ => panic!("Expected Type decl for class"),
  }

  // Check third decl - Functor instance
  let instance_decl = &decls[2];
  match instance_decl.value() {
    Decl::Ins(inst) => {
      assert_eq!(inst.class_name.as_str(), Some("Functor"));
    }
    _ => panic!("Expected Ins decl"),
  }
}
