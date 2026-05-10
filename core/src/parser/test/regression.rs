use super::*;

#[test]
fn test_match_with_app_scrutinee() {
  let input = "type Unit { unit }\ndef main : Unit := match id unit { unit => unit }\n";
  let r = parse_file(input);
  assert!(
    r.is_ok(),
    "should parse match with app scrutinee: {:?}",
    r.err()
  );
}

#[test]
fn test_match_with_two_var_scrutinee() {
  let input = "type T { a b }\ndef main : T := match id a { a => a, b => b }\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse match with two vars: {:?}", r.err());
}

#[test]
fn test_parse_macro_expr_no_overflow() {
  let input = "defmacro add_one x := quote { unquote x + 1 }\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse defmacro: {:?}", r.err());
}

#[test]
fn test_parse_def_with_let_no_macro() {
  let input = "def main : I64 := let x := 10 in x + 1\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse def with let: {:?}", r.err());
}

#[test]
fn test_parse_def_with_let_simple() {
  let input = "def main : I64 := let x := 10 in x\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse def with simple let: {:?}", r.err());
}

#[test]
fn test_parse_empty() {
  let input = "";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse empty: {:?}", r.err());
}

#[test]
fn test_parse_use() {
  let input = "use init\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse use: {:?}", r.err());
}

#[test]
fn test_parse_type_unit() {
  let input = "type Unit { unit }\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse type: {:?}", r.err());
}

#[test]
fn test_decl_parser_class() {
  let input: Span<'static, ()> = r#"class [Functor F] Applicative (F: Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}
"#
  .into();
  let r = decl_parser(input);
  assert!(r.is_ok(), "should parse class: {:?}", r.err());
}

#[test]
fn test_parse_simple_def_with_parser() {
  let input: Span<'static, ()> = "def main : I64 := 42\n".into();
  let r = def_parser(input);
  assert!(r.is_ok(), "should parse def with parser: {:?}", r.err());
}

#[test]
fn test_parse_def_with_use_and_empty_line() {
  let input = "use prelude\nuse std.test\n\n@[test]\ndef test_x : Bool := True\n";
  let r = parse_file(input);
  assert!(
    r.is_ok(),
    "should parse def with use and empty line: {:?}",
    r.err()
  );
}

#[test]
fn test_parse_simple_def_file() {
  let input = "def main : I64 := 42\n";
  let r = parse_file(input);
  assert!(r.is_ok(), "should parse simple def file: {:?}", r.err());
}
