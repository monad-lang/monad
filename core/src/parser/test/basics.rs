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
