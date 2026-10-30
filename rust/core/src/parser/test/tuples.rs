use super::*;

#[test]
fn test_tuple_pair() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(x, y)").unwrap();
  let expected = app(app(pvar(vec!["Pair", "pair"]), var("x")), var("y"));
  similar!(r, expected);
}

#[test]
fn test_tuple_triple() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(x, y, z)").unwrap();
  let inner = app(app(pvar(vec!["Pair", "pair"]), var("y")), var("z"));
  let expected = app(app(pvar(vec!["Pair", "pair"]), var("x")), inner);
  similar!(r, expected);
}

#[test]
fn test_tuple_pair_with_space() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("( x , y )").unwrap();
  let expected = app(app(pvar(vec!["Pair", "pair"]), var("x")), var("y"));
  similar!(r, expected);
}

#[test]
fn test_tuple_trailing_comma() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(a, b,)").unwrap();
  let expected = app(app(pvar(vec!["Pair", "pair"]), var("a")), var("b"));
  similar!(r, expected);
}

#[test]
fn test_parens_not_tuple() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(x)").unwrap();
  similar!(r, var("x"));
}

#[test]
fn test_parens_expr() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(x + y)").unwrap();
  let expected = oper(var("x"), "+", var("y"));
  similar!(r, expected);
}

#[test]
fn test_tuple_nested_expr() {
  let p = |s: &'static str| term::<()>(s.into());
  let (_, r) = p("(1 + 2, true)").unwrap();
  let left = oper(num(1), "+", num(2));
  let expected = app(app(pvar(vec!["Pair", "pair"]), left), var("true"));
  similar!(r, expected);
}
