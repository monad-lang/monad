use super::*;

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

  let opt_decl = &decls[0];
  match opt_decl.value() {
    Decl::Type(ind) => {
      assert_eq!(ind.name().as_str(), Some("Option"));
    }
    _ => panic!("Expected Type decl"),
  }

  let functor_decl = &decls[1];
  match functor_decl.value() {
    Decl::Type(ind) => {
      assert_eq!(ind.name().as_str(), Some("Functor"));
    }
    _ => panic!("Expected Type decl for class"),
  }

  let instance_decl = &decls[2];
  match instance_decl.value() {
    Decl::Ins(inst) => {
      assert_eq!(inst.class_name.as_str(), Some("Functor"));
    }
    _ => panic!("Expected Ins decl"),
  }
}
