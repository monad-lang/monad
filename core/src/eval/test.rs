use super::*;
use crate::eval::r#type::{
  FreeVars, elaborate_type, match_determine_type_vars, match_resolve_type, pi_of_forall_types,
  type_check, type_check_module_decls,
};
use crate::parser::parse_file;
use crate::parser::{ReplInput, repl_parser, term, test::parse_type};
use crate::term::module::{LoadedModules, default_modules, module};
use crate::term::test::{Similar, decl_def};
use crate::term::{
  Hole, Identifier, ModulePath, SourceContext, Term, Typed, app, app2, b_false, b_true,
  constructor, forall, id, io_term, lams, mp, mpt, mpvar, num, par, param, pi, some, str,
  strings_to_list_term, to_list_term, typ, type0, unit, var,
};
use crate::{set_of, similar};
use nom::Finish;
#[cfg(test)]
fn parse_term(input: &str) -> Term {
  let ReplInput::Term(e) = repl_parser(input).unwrap() else {
    panic!("expected term")
  };

  e
}

fn to_free_vars(vars: &[(Identifier, (Term, Option<Term>))]) -> FreeVars<'_> {
  let free_vars: FreeVars = vars.iter().map(|(n, ot)| (n, ot.into())).collect();
  free_vars
}

#[test]
fn test_pi_of_forall_types() {
  let arg_type = parse_type("{A : Type} -> List A");
  let return_type = parse_type("{A : Type} -> A");
  let res = pi_of_forall_types(arg_type, return_type);
  similar!(
    res,
    forall(
      param(id("A~"), var("Type")),
      forall(
        param(id("A"), var("Type")),
        pi(app2("List", "A"), var("A~"))
      )
    )
  );
  let arg_type = parse_type("{A : Type} -> List A -> Bool");
  let return_type = parse_type("{A : Type} -> {B : Type} -> A -> B");
  let res = pi_of_forall_types(arg_type, return_type);
  similar!(
    res,
    forall(
      param(id("B"), var("Type")),
      forall(
        param(id("A~"), var("Type")),
        forall(
          param(id("A"), var("Type")),
          pi(pi(app2("List", "A"), var("Bool")), pi(var("A~"), var("B")))
        )
      )
    )
  );
}

#[test]
fn test_compare_determine_type_vars() {
  let defined = var("A");
  let computed = app2("List", "A");
  let vars = [
    (id("A"), (type0(), Some(app2("List", "A")))),
    (id("B"), (type0(), Some(var("Bool")))),
  ];
  let free_vars: FreeVars = to_free_vars(&vars);
  let res = match_determine_type_vars(&defined, &computed, free_vars.clone());
  similar!(res, Ok(free_vars));

  let defined = pi(var("A"), var("B"));
  let computed = pi(app2("List", "A"), var("Bool"));
  let vars = [
    (id("A"), (type0(), Some(app2("List", "A")))),
    (id("B"), (type0(), Some(var("Bool")))),
  ];
  let free_vars: FreeVars = to_free_vars(&vars);
  let res = match_determine_type_vars(&defined, &computed, free_vars.clone());
  similar!(res, Ok(free_vars));

  let vars = [];
  let free_vars: FreeVars = to_free_vars(&vars);
  let left = parse_type("{A : Type} -> {L : Type -> Type} -> A -> L A -> L A");
  let right = parse_type("_ -> _ -> List I64");
  let res = match_determine_type_vars(&left, &right, free_vars.clone());
  let vars = [
    (id("L"), (pi(type0(), type0()), Some(var("List")))),
    (id("A"), (type0(), Some(var("I64")))),
  ];
  let free_vars: FreeVars = to_free_vars(&vars);
  similar!(res, Ok(free_vars));
}

#[test]
fn test_compare_types() {
  let un = |r: Result<_, TypeError>| r.inspect_err(|e| eprintln!("error: {e}")).unwrap();
  let mut loaded = LoadedModules::empty();
  let path = ModulePath::top("_");
  let mo = module(
    path.clone(),
    parse_file(
      r#"
    type List A {
      empty,
      cons A (tail : List A)
    }
    
    type Option A {
      none,
      some A
    }

    type Bool {
      true,
      false
    }
    "#
      .into(),
    )
    .unwrap(),
  );
  loaded.add_module(mo);
  let global = loaded.global(&path).unwrap();
  let scope = Scope::new(&global);
  let a = parse_type("(List A -> B) -> List B");
  let b = pi(Hole, app(typ("List"), typ("B")));
  similar!(match_resolve_type(&a, &b, &scope).unwrap(), a);
  let a = parse_type("{A : Type} -> {B : Type} -> A -> B");
  let b = pi(Hole, app(typ("List"), typ("B")));
  similar!(
    un(match_resolve_type(&a, &b, &scope)),
    forall(
      param(id("A"), var("Type")),
      pi(var("A"), app(typ("List"), typ("B")))
    )
  );
  let a = parse_type("{A : Type} -> Option A");
  let b = app(typ("Option"), Hole);
  similar!(match_resolve_type(&a, &b, &scope).unwrap(), a);
  let a = parse_type("{A : Type} -> List (List A) -> List A");
  let b = pi(app(typ("List"), app2("List", "A")), Hole);
  similar!(
    match_resolve_type(&a, &b, &scope).unwrap(),
    pi(app(var("List"), app2("List", "A")), app2("List", "A"))
  );
  let a = parse_type("{B : Type} -> {A : Type} -> A -> (A -> B) -> B");
  let b = parse_type("List A -> (List A -> Bool) -> Bool");
  similar!(
    match_resolve_type(&a, &b, &scope).unwrap(),
    pi(
      app2("List", "A"),
      pi(pi(app2("List", "A"), var("Bool")), var("Bool"))
    )
  );
  let a = parse_type("{A : Type} -> A");
  let b = parse_type("{A : Type} -> {B : Type} -> A");
  similar!(
    match_resolve_type(&a, &b, &scope).unwrap(),
    forall(param(id("A"), type0()), var("A"))
  );
  let left = parse_type("{A : Type} -> A");
  let right = parse_type("{A : Type} -> List A");
  similar!(
    match_resolve_type(&left, &right, &scope).unwrap(),
    forall(param(id("A"), type0()), app2("List", "A"))
  );
  let a = parse_type("{A : Type} -> List A");
  let b = parse_type("{A : Type} -> A");
  assert!(match_resolve_type(&a, &b, &scope).is_err(),);
  let a = parse_type("{A : Type} -> {B : Type} -> A -> (A -> B) -> B");
  let b = parse_type("{A : Type} -> List A -> (List A -> Bool) -> _");
  similar!(
    match_resolve_type(&a, &b, &scope).unwrap(),
    forall(
      param(id("A"), type0()),
      pi(
        app2("List", "A"),
        pi(pi(app2("List", "A"), var("Bool")), var("Bool"))
      )
    )
  );
  let left = parse_type("{A : Type} -> {B : Type} -> A -> B");
  let right = parse_type("{A : Type} -> List A -> Bool");
  similar!(
    match_resolve_type(&left, &right, &scope).unwrap(),
    forall(param(id("A"), type0()), pi(app2("List", "A"), var("Bool")))
  );
  let left = parse_type("{A : Type} -> A -> List A -> List A");
  let right = parse_type("{B : Type} -> {A : Type} -> _ -> List A -> List B");
  let res = match_resolve_type(&left, &right, &scope).unwrap();
  similar!(
    res,
    forall(
      param(id("A"), var("Type")),
      pi(var("A"), pi(app2("List", "A"), app2("List", "A")))
    )
  );
}

#[test]
fn test_elaborate_type() {
  let string = mpt("String");
  let v = vec![&string];
  let known = set_of(v.into_iter());
  let t_ano = elaborate_type(parse_type(r#"A -> B -> String"#), &vec![], &known);
  similar!(
    t_ano,
    forall(
      param(id("B"), type0()),
      forall(
        param(id("A"), type0()),
        pi(var("A"), pi(var("B"), var("String")))
      )
    )
  );
}

#[test]
fn test_type_check() {
  let loaded = default_modules().unwrap();
  let global = loaded.global(&loaded.builtins().prelude_path).unwrap();
  let scope = Scope::new(&global);
  let t = parse_term(r#"\a b => "hello""#);
  let t_ano = elaborate_type(
    parse_type(r#"A -> B -> String"#),
    &vec![],
    &scope.global().all_known_names(),
  );
  let r = type_check(t, t_ano, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok());

  let t = parse_term(r#"Option.none"#);
  let t_ano = parse_type(r#"{A : Type} -> Option A"#);
  let r = type_check(t, t_ano, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok());
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    def apply_fun (a : A) (f : A -> B) : B := f a
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);
  let apply_fun = global.find_ref(&mpt("apply_fun")).unwrap();
  let expected_type = parse_type("{B : Type} -> {A : Type} -> A -> (A -> B) -> B");
  // TODO similar!(apply_fun.typ(), &expected_type);
  eprintln!(
    "{} =? {expected_type} result {}",
    apply_fun.typ(),
    apply_fun.typ().similar(&expected_type)
  );
}

#[test]
fn test_type_check_app_polymorphic() {
  let loaded = default_modules().unwrap();
  let global = loaded.global(&loaded.builtins().prelude_path).unwrap();
  let scope = Scope::new(&global);

  let t = parse_term(r#"Option.some 42"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "Option.some 42 should type check");

  let t = parse_term(r#"Option.get_or_default "default" (Option.some 42)"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "Option.get_or_default should type check");
}

#[test]
fn test_type_check_app_pipe_operator() {
  let mut loaded = LoadedModules::empty();
  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    def apply_fun (a : A) (f : A -> B) : B := f a
    infix (|>) := apply_fun
    type I64 {}
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);
  let scope = global.scope();

  let t = parse_term(r#"1 |> fn x => x"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "1 |> fn x => x should type check");
}

#[test]
fn test_type_check_app_polymorphic_chain() {
  let loaded = default_modules().unwrap();
  let global = loaded.global(&loaded.builtins().prelude_path).unwrap();
  let scope = Scope::new(&global);

  // Test: Option.get_or_default "default" (Option.some 42)
  // This tests that type variables are resolved from arguments
  let t = parse_term(r#"Option.get_or_default "default" (Option.some 42)"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(
    r.is_ok(),
    "Option.get_or_default with some should type check"
  );

  // Test: Option.get_or_default "default" Option.none
  // This tests that type variables are resolved even when Option.none doesn't provide type info
  let t = parse_term(r#"Option.get_or_default "default" Option.none"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(
    r.is_ok(),
    "Option.get_or_default with none should type check"
  );
}

#[test]
fn test_type_check_hello_style_pipe() {
  let loaded = default_modules().unwrap();
  let global = loaded.global(&loaded.builtins().prelude_path).unwrap();
  let scope = Scope::new(&global);

  // Simulate hello.mo pattern:
  // args |> List.last |> (Option.get_or_default "nothing") |> say_hello
  // where say_hello : String -> IO Unit

  // First test: List.last on a list
  let t = parse_term(r#"List.last (List.cons "hello" List.empty)"#);
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "List.last should type check");

  // Second test: pipe chain with Option.get_or_default
  let t = parse_term(
    r#"(List.cons "hello" List.empty) |> List.last |> (Option.get_or_default "nothing")"#,
  );
  let r = type_check(t, Hole, &scope).map_err(|e| eprintln!("error: {e}"));
  assert!(
    r.is_ok(),
    "pipe chain with Option.get_or_default should type check"
  );
}

#[test]
fn test_type_check_hello_full() {
  let mut loaded = default_modules().unwrap();
  let path = ModulePath::top("test_hello");
  let decls = parse_file(
    r#"
    use io
    open IO

    def say_hello (s : String) : IO Unit := println s

    def main (args: List String) : IO Unit :=
      args
        |> List.last
        |> (Option.get_or_default "nothing")
        |> say_hello
    "#
    .into(),
  )
  .unwrap();
  let r = type_check_module_decls(&path, decls, &mut loaded).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "hello.mo style code should type check");
}

#[test]
fn test_type_check_hello_with_args() {
  let mut loaded = default_modules().unwrap();
  let path = ModulePath::top("test_hello");
  let decls = parse_file(
    r#"
    use io
    open IO

    def say_hello (s : String) : IO Unit := println s

    def main (args: List String) : IO Unit :=
      args
        |> List.last
        |> (Option.get_or_default "nothing")
        |> say_hello
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(path.clone(), decls));
  let module = loaded.get_module(&path).unwrap();
  let global = loaded.global(&path).unwrap();

  let def = module.get_def(&mpt("main")).unwrap().value();
  let arg = to_list_term(vec![str("arg1"), str("arg2"), str("arg3")]);
  let input_term = app(def.term.clone(), arg);

  let r = type_check(input_term, Hole, &global.scope()).map_err(|e| eprintln!("error: {e}"));
  assert!(r.is_ok(), "hello.mo with args should type check");
}

#[test]
fn test_type_check_hello_with_strings_to_list() {
  let mut loaded = default_modules().unwrap();
  let path = ModulePath::top("test_hello");
  let decls = parse_file(
    r#"
    use io
    open IO

    def say_hello (s : String) : IO Unit := println s

    def main (args: List String) : IO Unit :=
      args
        |> List.last
        |> (Option.get_or_default "nothing")
        |> say_hello
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(path.clone(), decls));
  let module = loaded.get_module(&path).unwrap();
  let global = loaded.global(&path).unwrap();

  let def = module.get_def(&mpt("main")).unwrap().value();
  let arg = strings_to_list_term(vec!["hello".to_string()]);
  let input_term = app(def.term.clone(), arg);

  let r = type_check(input_term, Hole, &global.scope()).map_err(|e| eprintln!("error: {e}"));
  assert!(
    r.is_ok(),
    "hello.mo with strings_to_list_term should type check"
  );
}

fn con_list_cons(head: Term, tail: Term) -> Term {
  Term::Con(constructor(
    id("cons"),
    mpt("List"),
    vec![Some(head), Some(tail)],
  ))
}

fn con_list_empty() -> Term {
  Term::Con(constructor(id("empty"), mpt("List"), vec![]))
}

fn eval_test(main_term: Term, scope: &Scope) -> Result<Term, String> {
  let tt = type_check(main_term, Hole, &scope).map_err(|e| format!("type check failed: {e}"))?;
  eval(tt.term, scope, &EvalOptions { debug: true }).map_err(|e| format!("eval error: {e}"))
}

fn un<T, E>(r: Result<T, E>) -> T
where
  E: std::fmt::Debug + Display,
{
  r.inspect_err(|e| eprintln!("{e}")).unwrap()
}
fn parse(s: &str) -> Term {
  let ReplInput::Term(e) = repl_parser(s).unwrap() else {
    panic!("expected term")
  };
  e
}
#[test]
fn simple_eval() {
  let path = ModulePath::top("_");
  let empty_module = module(
    path.clone(),
    vec![SourceContext::no_ctx(decl_def(
      mpt("y"),
      vec![],
      typ("String"),
      str("y"),
    ))],
  );
  let loaded = LoadedModules::from(vec![empty_module]);
  let global = loaded.global(&path).unwrap();
  let empty_scope = global.scope();
  let e = apps(lam(par("x"), var("x")), vec![var("y")]);
  assert_eq!(eval_test(e, &empty_scope).unwrap(), str("y"));
  let e = apps(lam(par("x"), var("y")), vec![var("y")]);
  assert_eq!(eval_test(e, &empty_scope).unwrap(), str("y"));
}

#[test]
fn term_eval() {
  let loaded = default_modules().unwrap();
  let path = mpt("init");
  let global = loaded.global(&path).unwrap();
  let scope = Scope::new(&global);
  let e = parse(
    r#"
        1 + 2 + 3 + 4 + 5
    "#,
  );
  similar!(eval_test(e, &scope).unwrap(), num(15));
  let e = parse(
    r#"
      Bool.true
    "#,
  );
  similar!(un(eval_test(e, &scope)), b_true());
  let e = parse(
    r#"List.cons "a" List.empty
    "#,
  );
  similar!(
    un(eval_test(e, &scope)),
    con_list_cons(str("a"), con_list_empty())
  );
  let e = parse(
    r#"List.first (List.cons 1 List.empty)
    "#,
  );
  similar!(un(eval_test(e, &scope)), some(num(1)));
  let e = parse(
    r#"if true then 1 else 3
    "#,
  );
  similar!(eval_test(e, &scope).unwrap(), num(1));

  let e = parse(
    r#"not true
    "#,
  );
  similar!(eval_test(e, &scope).unwrap(), b_false());
  let e = parse(
    r#"List.empty |> List.is_empty
    "#,
  );
  similar!(eval_test(e, &scope).unwrap(), b_true());
}

#[test]
fn test_list_literal_eval() {
  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    type List X {
        empty,
        cons (a : X) (List X) : List X
    }
    def test1 : List I64 := [1]
    def test2 : List String := ["a" , "test"]
    def test3 : List (List I64) := [[1], [2]]
    "#
    .into(),
  )
  .unwrap();
  let mut loaded = default_modules().unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);

  let (_, e) = term::<()>("test1".into()).finish().unwrap();
  similar!(
    eval_test(e, &global.scope()).unwrap(),
    con_list_cons(num(1), con_list_empty())
  );
  let (_, e) = term::<()>("test2".into()).finish().unwrap();
  similar!(
    eval_test(e, &global.scope()).unwrap(),
    con_list_cons(str("a"), con_list_cons(str("test"), con_list_empty()))
  );
}

#[test]
fn test_simple_instance() {
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    class HAdd A B C {
      def add (a: A) (b : B) : C
    }
    infix (+) := HAdd.add
    type I64 {}

    @[native num_add]
    def I64.add (a b : I64) : I64

    instance HAdd I64 I64 I64 {
      def add (a b: I64) : I64 := I64.add a b
    }
    def main : I64 := 1 + 2
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);
  let (_, e) = term::<()>("main".into()).finish().unwrap();
  let res = eval_test(e, &global.scope());
  assert_eq!(res.unwrap(), num(3));
}

#[test]
fn complex_monad_eval() {
  let res = io_term(unit()); // IO Unit
  let mut loaded = default_modules().unwrap();
  let init_path = mpt("init");
  let global = loaded.global(&init_path).unwrap();
  let e = apps(
    lams(
      vec![par("x")],
      apps(mpvar(mp(vec!["IO", "println"])), vec![var("x")]),
    ),
    vec![str("Hello")],
  );
  assert_eq!(eval_test(e, &global.scope()).unwrap(), res);

  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    use io
    class Monad (M: Type -> Type) {
        def pure : A -> M A
        def bind (a : M A) (f : A -> M B) : M B
    }
    open Monad
    open IO
    infix (>>=) := Monad.bind

    type IO A {
      io (a : A)
    }
    instance Monad IO {
      def pure (a: A) : IO A :=
        io a
      def bind (a : IO A) (f : A -> IO B) : IO B :=
        match a {
          io a => f a
        }
    }
    def main : IO Unit :=
        println "Hello"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let m = module(path.clone(), decls);
  loaded.add_module(m);
  let global = loaded.global(&path).unwrap();
  let scope = Scope::new(&global);
  let (_, e) = term::<()>("main".into()).finish().unwrap();
  assert_eq!(eval_test(e, &scope).unwrap(), res);
}

#[test]
fn test_i64_eq_comparison() {
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    type Bool {
      true,
      false
    }

    class BEq A {
      def beq : A -> B -> Bool
    }

    infix (==) := BEq.beq

    type I64 {}

    @[native i64_eq]
    def I64.beq (a b : I64) : Bool

    instance BEq I64 {
      def beq (a b : I64) : Bool := I64.beq a b
    }

    def eq_true : Bool := 5 == 5
    def eq_false : Bool := 5 == 3
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);

  let (_, e) = term::<()>("eq_true".into()).finish().unwrap();
  similar!(eval_test(e, &global.scope()).unwrap(), b_true());

  let (_, e) = term::<()>("eq_false".into()).finish().unwrap();
  similar!(eval_test(e, &global.scope()).unwrap(), b_false());
}

#[test]
fn test_i64_eq_with_default_modules() {
  // Test == operator using the actual prelude + init modules
  let mut loaded = default_modules().unwrap();
  let path = ModulePath::top("_");
  let decls = parse_file(
    r#"
    use init
    use math
    open IO

    def eq_true : Bool := 42 == 42
    def eq_false : Bool := 42 == 13
    def neq_test : Bool := 1 == 2
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let global = loaded.scope_of_decls(&path, &decls);

  let (_, e) = term::<()>("eq_true".into()).finish().unwrap();
  similar!(eval_test(e, &global.scope()).unwrap(), b_true());

  let (_, e) = term::<()>("eq_false".into()).finish().unwrap();
  similar!(eval_test(e, &global.scope()).unwrap(), b_false());

  let (_, e) = term::<()>("neq_test".into()).finish().unwrap();
  similar!(eval_test(e, &global.scope()).unwrap(), b_false());
}
