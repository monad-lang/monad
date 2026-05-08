use super::*;

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
