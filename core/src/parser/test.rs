use super::*;
use crate::{
  Map, similar,
  term::{
    LetVar, Term, app, app2, dpar, forall, induct_constructor, mp, mpt, mpv, oper, par, pi, pi_var,
    pvar, str,
    test::{decl_def, decl_inductive, decl_infix, decl_open, decl_use, defs_class},
    typ, var,
  },
};

#[test]
fn test_string_litteral() {
  let p = |i: Span<'static, ()>| string_litteral::<()>(i);
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
  let s = r#"infix:123 (+) := add"#.into();
  let (_, res) = infix_parser(s).unwrap();

  similar!(res, infix("+".into(), mpt("add"), 123));
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
        None
      )]
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
        class_def(id("pure"), pi(typ("A"), app2("F", "A")), None),
        class_def(
          id("apply"),
          pi(
            app(typ("F"), pi(typ("A"), typ("B"))),
            pi(app2("F", "A"), app2("F", "B"))
          ),
          None
        )
      ]
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
        class_def(id("pure"), pi(typ("A"), app2("M", "A")), None),
        class_def(
          id("bind"),
          pi(
            app2("M", "A"),
            pi(pi(typ("A"), app2("M", "B")), app2("M", "B"))
          ),
          None
        )
      ]
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
  similar!(r, map_term(Map::new()));
  let (_, r) = struct_val_parser(r#"{a := b}"#.into()).unwrap();
  similar!(r, map_term(Map::from([(id("a"), var("b"))])));
  let (_, r) = struct_val_parser(r#"{a := b, b:={c:=0},}"#.into()).unwrap();
  similar!(
    r,
    map_term(Map::from([
      (id("a"), var("b")),
      (id("b"), map_term(Map::from([(id("c"), num(0))])))
    ]))
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
      map_term(Map::from([
        (id("a"), var("b")),
        (id("c"), str("Hello")),
        (id("map"), map_term(Map::new()))
      ]))
    )
  );
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
      )]
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
      ]
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
        )
      )]
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
      ]
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
      ]
    )
  );
}

#[test]
fn test_native() {
  let s = r#"@[native num_add]
    def add (a b : I64) : I64
    "#
  .into();
  let (_, res) = native_parser(s).unwrap();

  similar!(
    res,
    def_native(
      id("num_add"),
      mpt("add"),
      vec![dpar("a", typ("I64")), dpar("b", typ("I64"))],
      typ("I64"),
    )
    .unwrap()
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
      )
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
      )
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
      apps(var("println"), vec![str("Hello, world!")])
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
      )
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
    infix:90 (++) := append

    class Functor (F: Type -> Type) {
    	def map (f: A -> B) : (F A) -> F B
    }
    "#;
  let m: Vec<Decl> = parse_file(s.into())
    .unwrap()
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
      decl_infix("++".into(), 90, mpt("append")),
      defs_class(
        mpt("Functor"),
        vec![],
        vec![dpar("F", pi(typ("Type"), typ("Type")))],
        vec![class_def(
          id("map"),
          pi(pi(typ("A"), typ("B")), pi(app2("F", "A"), app2("F", "B"))),
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
  let (_, r) = do_block(r#"do { x <- monadic; return x }"#).unwrap();
  let expected = app(
    pvar(vec!["Monad", "bind"]),
    app(var("monadic"), lam(par("x"), var("x"))),
  );
  similar!(r, expected);
}

#[test]
fn test_do_parser_let_and_bind() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let (_, r) = do_block(r#"do { let x := 1; y <- monadic; return y }"#).unwrap();
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
  let (_, r) = do_block(r#"do { a <- ma; b <- mb; return b }"#).unwrap();
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
  let (_, r) = do_block(r#"do { x <- monadic; return x }"#).unwrap();
  let (_, r2) = do_block(r#"do { x <- monadic; return x }"#).unwrap();
  similar!(r, r2);
}

#[test]
fn test_do_parser_complex_desugar() {
  let do_block = |s: &'static str| do_parser::<()>(s.into());
  let input = r#"do { let x := 1; y <- get; return y }"#;
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
