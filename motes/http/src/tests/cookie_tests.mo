/// Cookie parsing/serialization and constant-time comparison.

use http::cookie {
  Cookie.parse, Cookie.lookup, Cookie.render, Cookie.set_cookie, Cookie.clear,
  CookieAttrs, CookieAttrs.default, SameSite,
}
use http::strings {Strings.ct_eq}

def lookup_ok (name : String) (want : String) (cookies : List (Pair String String)) : Bool :=
  match Cookie.lookup name cookies {
    Option.some v => String.beq v want,
    Option.none => false
  }

#[test]
def test_parse_two_cookies : Bool :=
  let cookies := Cookie.parse (Option.some "a=1; b=2") in
  Bool.and (lookup_ok "a" "1" cookies) (lookup_ok "b" "2" cookies)

#[test]
def test_parse_absent_is_empty : Bool :=
  List.is_empty (Cookie.parse Option.none)

#[test]
def test_parse_empty_is_empty : Bool :=
  List.is_empty (Cookie.parse (Option.some "   "))

#[test]
def test_value_not_percent_decoded : Bool :=
  let cookies := Cookie.parse (Option.some "a=%3D") in
  lookup_ok "a" "%3D" cookies

#[test]
def test_render_drops_invalid_octets : Bool :=
  String.beq (Cookie.render "n" "a;b c") "n=abc"

#[test]
def test_set_cookie_attrs : Bool :=
  let base := CookieAttrs.default in
  let attrs : CookieAttrs :=
    { base with max_age := Option.some 60i64, secure := true, same_site := SameSite.strict } in
  match Cookie.set_cookie "sid" "v" attrs {
    Pair.pair key value =>
      Bool.and (String.beq key "Set-Cookie")
        (String.beq value "sid=v; Path=/; Max-Age=60; HttpOnly; Secure; SameSite=Strict")
  }

#[test]
def test_clear_expires : Bool :=
  match Cookie.clear "sid" CookieAttrs.default {
    Pair.pair key value =>
      Bool.and (String.beq key "Set-Cookie")
        (String.beq value "sid=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax")
  }

#[test]
def test_ct_eq : Bool :=
  Bool.and (Strings.ct_eq "abc" "abc")
    (Bool.and (Bool.not (Strings.ct_eq "abc" "abd"))
      (Bool.not (Strings.ct_eq "abc" "ab")))
