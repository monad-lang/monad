use super::*;

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
        class_def(
          id("pure"),
          pi(typ("A"), app2("F", "A")),
          None,
          vec![],
          vec![],
          None
        ),
        class_def(
          id("apply"),
          pi(
            app(typ("F"), pi(typ("A"), typ("B"))),
            pi(app2("F", "A"), app2("F", "B"))
          ),
          None,
          vec![],
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
        class_def(
          id("pure"),
          pi(typ("A"), app2("M", "A")),
          None,
          vec![],
          vec![],
          None
        ),
        class_def(
          id("bind"),
          pi(
            app2("M", "A"),
            pi(pi(typ("A"), app2("M", "B")), app2("M", "B"))
          ),
          None,
          vec![],
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
  let s = r#"#[native num_add]
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
          vec![],
          None
        )]
      )
    ]
  );
}

#[test]
fn test_selective_use_only() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {println, print}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![
      UseItem::Name(id("println")),
      UseItem::Name(id("print"))
    ])
  );
}

#[test]
fn test_selective_use_rename() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {println as show}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![UseItem::Rename(id("println"), id("show"))])
  );
}

#[test]
fn test_use_bare_still_parses() {
  use crate::term::UseFilter;
  let s = "use IO".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(res.filter, UseFilter::Bare);
}

#[test]
fn test_use_bare_source_location_excludes_trailing_whitespace() {
  // Regression test: `use_opt_filter` used to consume-and-keep trailing
  // whitespace/blank-lines (looking for a `{` that isn't there) even on
  // the bare-use fallback path, so `Use.source_location.end` would land
  // well past the module path — e.g. right before the next declaration.
  // That's harmless for warning display but corrupts any byte-precise
  // splice (`organize_imports`'s `TextEdit`s) built from it: the edit
  // would eat the blank-line separator before the next declaration too.
  let s = "use std.show\n\n\ndef x : I64 := 1".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.source_location.end.line, 1);
  assert_eq!(res.source_location.end.column, 13); // just past "use std.show"
}

#[test]
fn test_use_glob() {
  use crate::term::{UseFilter, UseItem};
  let s = "use IO {*}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(res.filter, UseFilter::Items(vec![UseItem::Glob]));
}

#[test]
fn test_use_empty_braces() {
  use crate::term::UseFilter;
  let s = "use IO {}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(res.filter, UseFilter::Items(vec![]));
}

#[test]
fn test_use_nested_simple() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {file {read}}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(res.module_path, mpt("IO"));
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![UseItem::SubModule {
      name: id("file"),
      items: vec![UseItem::Name(id("read"))],
    }])
  );
}

#[test]
fn test_use_nested_glob() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {file {*}}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![UseItem::SubModule {
      name: id("file"),
      items: vec![UseItem::Glob],
    }])
  );
}

#[test]
fn test_use_nested_deep() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {a {b {c}}}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![UseItem::SubModule {
      name: id("a"),
      items: vec![UseItem::SubModule {
        name: id("b"),
        items: vec![UseItem::Name(id("c"))],
      }],
    }])
  );
}

#[test]
fn test_use_nested_rename() {
  use crate::term::{UseFilter, UseItem, id};
  let s = "use IO {file as myfile {read}}".into();
  let (_, res) = use_parser(s).unwrap();
  assert_eq!(
    res.filter,
    UseFilter::Items(vec![UseItem::SubModuleRename {
      name: id("file"),
      alias: id("myfile"),
      items: vec![UseItem::Name(id("read"))],
    }])
  );
}

#[test]
fn test_open_brace_filter() {
  use crate::term::{Decl, OpenFilter, id};
  let s = "open IO {println, print}".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => {
      assert_eq!(open.module_path, mpt("IO"));
      assert_eq!(
        open.filter,
        OpenFilter::Only(vec![id("println"), id("print")])
      );
    }
    other => panic!("expected Decl::Open, got {other:?}"),
  }
}

#[test]
fn test_open_no_braces_still_all() {
  use crate::term::{Decl, OpenFilter};
  let s = "open IO".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => {
      assert_eq!(open.module_path, mpt("IO"));
      assert_eq!(open.filter, OpenFilter::All);
    }
    other => panic!("expected Decl::Open, got {other:?}"),
  }
}

#[test]
fn test_open_glob() {
  use crate::term::{Decl, OpenFilter};
  let s = "open IO {*}".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => {
      assert_eq!(open.module_path, mpt("IO"));
      assert_eq!(open.filter, OpenFilter::Glob);
    }
    other => panic!("expected Decl::Open, got {other:?}"),
  }
}

#[test]
fn test_open_empty_brace_filter_still_parses() {
  // `open X {}` (zero names) still parses fine at the grammar level — it's
  // rejected later, by the checker (`TypeError::EmptyOpenFilter`, see
  // `core_check_module::test::test_empty_open_filter_is_rejected`), not
  // here.
  use crate::term::{Decl, OpenFilter};
  let s = "open IO {}".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => {
      assert_eq!(open.module_path, mpt("IO"));
      assert_eq!(open.filter, OpenFilter::Only(vec![]));
    }
    other => panic!("expected Decl::Open, got {other:?}"),
  }
}

#[test]
fn test_open_multiline_brace_filter() {
  // Regression test: `open`'s brace-filter grammar used to be missing the
  // leading whitespace-skip right after `{` that `use`'s already had
  // (`use_brace_items`'s opening delimiter is `(char('{'), ws0)`; `open`'s
  // was just `char('{')`) — a newline immediately after `{` (as any
  // multi-line-wrapped `open X {\n  a, b,\n}` produces, e.g. via
  // `monad-rs organize-imports`) made `identifier` fail on the very first
  // attempt, so `many0` silently matched zero names and the parser choked
  // looking for `}` right where the first name actually was.
  use crate::term::{Decl, OpenFilter, id};
  let s = "open IO {\n  println,\n  get_env,\n}".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => {
      assert_eq!(open.module_path, mpt("IO"));
      assert_eq!(
        open.filter,
        OpenFilter::Only(vec![id("println"), id("get_env")])
      );
    }
    other => panic!("expected Decl::Open, got {other:?}"),
  }

  // Multi-line glob too.
  let s = "open IO {\n  *\n}".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::Open(open) => assert_eq!(open.filter, OpenFilter::Glob),
    other => panic!("expected Decl::Open, got {other:?}"),
  }
}

#[test]
fn test_scoped_open_def() {
  use crate::term::{Decl, OpenFilter};
  let s = "open IO in def main : IO Unit := println \"hi\"".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::ScopedOpen {
      module_path,
      filter,
      decl,
      ..
    } => {
      assert_eq!(module_path, mpt("IO"));
      assert_eq!(filter, OpenFilter::All);
      assert!(matches!(*decl, Decl::Def(_)));
    }
    other => panic!("expected Decl::ScopedOpen, got {other:?}"),
  }
}

#[test]
fn test_scoped_open_filtered() {
  use crate::term::{Decl, OpenFilter, id};
  let s = "open IO {println} in def main : IO Unit := println \"hi\"".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::ScopedOpen {
      module_path,
      filter,
      decl,
      ..
    } => {
      assert_eq!(module_path, mpt("IO"));
      assert_eq!(filter, OpenFilter::Only(vec![id("println")]));
      assert!(matches!(*decl, Decl::Def(_)));
    }
    other => panic!("expected Decl::ScopedOpen, got {other:?}"),
  }
}

#[test]
fn test_scoped_open_type() {
  use crate::term::Decl;
  let s = "open Nat in struct Foo { x : Nat }".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::ScopedOpen { decl, .. } => assert!(matches!(*decl, Decl::Type(_))),
    other => panic!("expected Decl::ScopedOpen, got {other:?}"),
  }
}

#[test]
fn test_scoped_open_instance() {
  use crate::term::Decl;
  let s = "open Nat in instance Show Nat { def show (n: Nat) : String := \"\" }".into();
  let (_, res) = open_parser(s).unwrap();
  match res {
    Decl::ScopedOpen { decl, .. } => assert!(matches!(*decl, Decl::Ins(_))),
    other => panic!("expected Decl::ScopedOpen, got {other:?}"),
  }
}

#[test]
fn test_parse_erased_param() {
  // %x : I64 — erased prefix parses as Zero
  let s: Span<()> = "(%x : I64)".into();
  let (_, res) = lam_param(s).unwrap();
  assert_eq!(res.name, id("x"));
  assert_eq!(*res.typ, typ("I64"));
  assert_eq!(res.mult, Multiplicity::Zero);
}

#[test]
fn test_parse_erased_def_param() {
  // def f (%x : I64) : I64 — erased in def
  let s = r#"def f (%x : I64) : I64 := 42"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Def(def) => {
      // The lam param should be erased
      if let Term::Lam { param, .. } = &def.term {
        assert_eq!(param.multiplicity(), &Multiplicity::Zero);
      }
    }
    _ => panic!("Expected Def"),
  }
}

#[test]
fn test_parse_instance_with_forall_params() {
  // instance {R : Type} Functor (Const R) — with explicit forall params
  let s = r#"instance {R : Type} Functor (Const R) { def map (f : A -> B) (a : Const R A) : Const R B := a }"#.into();
  let (_, res) = instance_parser(s).unwrap();
  assert_eq!(res.params.len(), 1);
  assert_eq!(res.params[0].name, id("R"));
  assert_eq!(*res.params[0].typ, var("Type"));
  assert_eq!(res.class_name, mpt("Functor"));
}

#[test]
fn test_parse_instance_with_multiple_forall_params() {
  // instance {R : Type} {E : Type} Functor (Const R) — multiple foralls
  let s = r#"instance {R : Type} {E : Type} Functor (Const R) { def map (f : A -> B) (a : Const R A) : Const R B := a }"#.into();
  let (_, res) = instance_parser(s).unwrap();
  assert_eq!(res.params.len(), 2);
  assert_eq!(res.params[0].name, id("R"));
  assert_eq!(res.params[1].name, id("E"));
}

#[test]
fn test_parse_mixed_multiplicity_params() {
  let s = r#"def f (!x : I64) (?y : I64) (%z : I64) (w : I64) : I64 := x"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Def(_) => {} // Just verify it parses
    _ => panic!("Expected Def"),
  }
}

#[test]
fn test_visibility_def() {
  let (_, res) = def_parser(r#"pub def f : I64 := 1"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let (_, res) = def_parser(r#"priv def f : I64 := 1"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let (_, res) = def_parser(r#"def f : I64 := 1"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_after_attribute() {
  // visibility comes after attributes: `#[attr] pub def`, not `pub #[attr] def`.
  let (_, res) = def_parser(r#"#[partial] pub def f : I64 := 1"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Pub);
  assert!(res.has_partial_attr());
}

#[test]
fn test_visibility_type() {
  let (_, res) = inductive_parser(r#"pub type Foo { mk }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let (_, res) = inductive_parser(r#"priv type Foo { mk }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let (_, res) = inductive_parser(r#"type Foo { mk }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_class() {
  let (_, res) = class_parser(r#"pub class Show A { def show (a: A) : String }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let (_, res) = class_parser(r#"priv class Show A { def show (a: A) : String }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let (_, res) = class_parser(r#"class Show A { def show (a: A) : String }"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_struct() {
  let struct_parser = |s: &'static str| struct_parser::<()>(s.into());
  let (_, res) = struct_parser(r#"pub struct Foo { x : I64 }"#).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let (_, res) = struct_parser(r#"priv struct Foo { x : I64 }"#).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let (_, res) = struct_parser(r#"struct Foo { x : I64 }"#).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_instance() {
  let s = r#"pub instance Show I64 { def show (x: I64) : String := "int" }"#.into();
  let (_, res) = instance_parser(s).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let s = r#"priv instance Show I64 { def show (x: I64) : String := "int" }"#.into();
  let (_, res) = instance_parser(s).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let s = r#"instance Show I64 { def show (x: I64) : String := "int" }"#.into();
  let (_, res) = instance_parser(s).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_infix() {
  let (_, res) = infix_parser(r#"pub infix (++) := myConcat"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Pub);

  let (_, res) = infix_parser(r#"priv infix (++) := myConcat"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::Priv);

  let (_, res) = infix_parser(r#"infix (++) := myConcat"#.into()).unwrap();
  assert_eq!(res.vis, Visibility::PackagePrivate);
}

#[test]
fn test_visibility_pub_priv_is_parse_error() {
  // Only one visibility keyword is allowed.
  assert!(
    decl_parser(r#"pub priv def f : I64 := 1"#.into())
      .finish()
      .is_err()
  );
}

#[test]
fn test_visibility_use_unaffected() {
  // `use` keeps its own binary `pub use`/bare `use` handling; `priv use` is
  // not a thing (priv does not apply to use/open).
  let s = r#"pub use io {*}"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Use(u) => assert!(u.public),
    _ => panic!("Expected Use"),
  }
}
