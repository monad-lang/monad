use super::*;

/// Mirrors the self-hosted `#Named.Instance` battery: the host only needs
/// PARSE-level parity for `f #Inst args` (the dict-pass half is
/// self-hosted), so the marker is consumed and DISCARDED — the resulting
/// term is the plain application.
fn parse_term_app(s: &str) -> Term {
  let t = application::<()>(s.into()).finish().unwrap().1;
  t
}

#[test]
fn test_dict_hint_discarded_from_application() {
  let r = parse_term_app(r#"sort #My.Ord xs"#);
  // `sort #My.Ord xs` is `(sort xs)` on the host — the hint never
  // survives the parse.
  similar!(r, app(var("sort"), var("xs")));
}

#[test]
fn test_dict_hint_bare_name() {
  let r = parse_term_app(r#"compare #MyOrd a b"#);
  similar!(r, apps(var("compare"), vec![var("a"), var("b")]));
}

/// `f #Ins` with no further args still parses (the hint counts as the
/// application's one "argument" for grammar purposes) and yields the
/// callee alone.
#[test]
fn test_dict_hint_without_args_yields_callee() {
  let r = parse_term_app(r#"sort #OrdInst"#);
  similar!(r, var("sort"));
}

/// A `#` not followed by a name is NOT a hint: the hint parser fails,
/// no other argument atom accepts a `#`, and the whole application
/// fails to parse rather than silently dropping or misreading it
/// (matching the self-hosted parser's own rejection).
#[test]
fn test_hash_without_name_is_not_a_hint() {
  let r = application::<()>(r#"f # 5"#.into()).finish();
  assert!(r.is_err(), "`f # 5` must not parse");
}

/// Ordinary applications are untouched by the hint probe.
#[test]
fn test_plain_application_unchanged() {
  let r = parse_term_app(r#"f x y"#);
  similar!(r, apps(var("f"), vec![var("x"), var("y")]));
}
