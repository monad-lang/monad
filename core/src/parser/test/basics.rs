use super::*;

#[test]
fn test_string_litteral() {
  let p = |i: Span<'static, ()>| string_literal::<()>(i);
  let (_, r) = p(r#""It's a test \"Hello, World\"""#.into()).unwrap();
  similar!(r, str(r#"It's a test "Hello, World""#.into()));
  assert!(p("abc".into()).is_err());
  assert!(p(r#""abc"#.into()).is_err());
}

#[test]
fn test_raw_string_literal_term() {
  // `r"..."` parses as a string literal at the term level (the raw-string
  // parser runs ahead of `variable` in `term_inner`).
  let p = |i: Span<'static, ()>| term::<()>(i);
  // n = 0
  let (rest, r) = p(r#"r"hello""#.into()).unwrap();
  assert_eq!(rest.fragment().to_string(), "");
  similar!(r, str("hello".into()));
  // n = 1: the user's example.
  let (rest, r) = p(r##"r#" blab""" "#"##.into()).unwrap();
  assert_eq!(rest.fragment().to_string(), "");
  similar!(r, str(" blab\"\"\" ".into()));
}

#[test]
fn test_raw_string_disambiguation_from_variable() {
  // `r` is a valid identifier — confirm the raw-string parser backtracks so a
  // bare `r` / `regex` still parse as a `Var`, not a string.
  let p = |i: Span<'static, ()>| term::<()>(i);
  // `r` alone (not followed by `"` or `#") is the identifier `r`.
  let (_, r) = p("r".into()).unwrap();
  similar!(r, var("r"));
  // `regex` is the identifier `regex` (raw parser backtracks on `r` + `e`).
  let (_, r) = p("regex".into()).unwrap();
  similar!(r, var("regex"));
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

#[test]
fn test_infix() {
  let s = r#"infix (+) := add"#.into();
  let (_, res) = infix_parser(s).unwrap();
  similar!(res, infix("+".into(), mpt("add")));
}

#[test]
fn test_infix_at_operator() {
  // `@` carries no built-in meaning — it's a plain operator token, exactly
  // like `+`/`++`, that library code binds via `infix (@) := ...`.
  let s = r#"infix (@) := my_append"#.into();
  let (_, res) = infix_parser(s).unwrap();
  similar!(res, infix("@".into(), mpt("my_append")));
}

#[test]
fn test_at_operator_expr_parses_at_expected_precedence() {
  // `@` sits at `++`'s tier (50, right-associative) — `a @ b @ c` should
  // parse as `a @ (b @ c)`, the same shape `"a" ++ "b" ++ "c"` parses as.
  let (_, res) = term::<()>(r#"a @ b @ c"#.into()).unwrap();
  similar!(
    res,
    oper(
      var_id(id("a")),
      "@",
      oper(var_id(id("b")), "@", var_id(id("c")))
    )
  );
}
