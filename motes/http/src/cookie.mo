/// Cookie parsing and serialization (RFC 6265).
///
/// Pure: a request's `Cookie` header is a `;`-separated list of opaque
/// `name=value` pairs, and a response's `Set-Cookie` is one pair plus
/// attributes. Values are NOT percent-decoded: a cookie's bytes are opaque,
/// and decoding `%3D` here would turn one cookie into another.
///
/// `Cookie.parse_headers` folds every `Cookie` header on the request;
/// `Cookie.set_cookie` returns the `("Set-Cookie", value)` pair to add with
/// `Headers.add` (a response may carry several).

use lib::types {Headers}
use lib::strings {Strings.split_at_byte, Strings.split_on}

pub type SameSite {
  lax,
  strict,
  none
}

pub struct CookieAttrs {
  path : String,
  max_age : Option I64,
  http_only : Bool,
  secure : Bool,
  same_site : SameSite
}

/// The safe default: `/` path, `HttpOnly`, `SameSite=Lax`, no Max-Age.
pub def CookieAttrs.default : CookieAttrs :=
  let a : CookieAttrs :=
    { path := "/", max_age := Option.none, http_only := true, secure := false, same_site := SameSite.lax } in
  a

// ── parsing ─────────────────────────────────────────────────────────────

/// Parse one `Cookie` header value. Order and duplicates are preserved.
pub def Cookie.parse (header : Option String) : List (Pair String String) :=
  match header {
    Option.none => List.empty,
    Option.some h => Cookie.parse_header h
  }

/// Parse every `Cookie` header on a request.
pub def Cookie.parse_headers (headers : Headers) : List (Pair String String) :=
  Cookie.parse_header_list (Headers.get_all "cookie" headers)

def Cookie.parse_header (h : String) : List (Pair String String) :=
  Cookie.parse_entries (Strings.split_on ";" h)

#[terminating]
def Cookie.parse_entries (entries : List String) : List (Pair String String) :=
  match entries {
    List.empty => List.empty,
    List.cons e rest =>
      let trimmed := String.trim e in
      if String.is_empty trimmed
      then Cookie.parse_entries rest
      else
        match Cookie.parse_one trimmed {
          Option.none => Cookie.parse_entries rest,
          Option.some pair => List.cons pair (Cookie.parse_entries rest)
        }
  }

def Cookie.parse_one (e : String) : Option (Pair String String) :=
  match Strings.split_at_byte 61u8 (String.to_list e) {
    Pair.pair name_b value_b =>
      let name := String.trim (String.from_list name_b) in
      if String.is_empty name
      then Option.none
      else Option.some (Pair.pair name (String.trim (String.from_list value_b)))
  }

#[terminating]
def Cookie.parse_header_list (headers : List String) : List (Pair String String) :=
  match headers {
    List.empty => List.empty,
    List.cons h rest => List.append (Cookie.parse_header h) (Cookie.parse_header_list rest)
  }

/// First value for `name`, or `none`.
pub def Cookie.lookup (name : String) (cookies : List (Pair String String)) : Option String :=
  Cookie.lookup_go name cookies

#[terminating]
def Cookie.lookup_go (name : String) (cookies : List (Pair String String)) : Option String :=
  match cookies {
    List.empty => Option.none,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq k name then Option.some v else Cookie.lookup_go name rest
      }
  }

// ── serialization ───────────────────────────────────────────────────────

/// `name=value`, with bytes outside the RFC 6265 cookie-octet set dropped
/// rather than escaped.
pub def Cookie.render (name : String) (value : String) : String :=
  String.concat name (String.concat "=" (Cookie.sanitize value))

#[terminating]
def Cookie.sanitize (value : String) : String :=
  String.from_list (Cookie.sanitize_go (String.to_list value))

#[terminating]
def Cookie.sanitize_go (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons b rest =>
      if Cookie.cookie_octet b
      then List.cons b (Cookie.sanitize_go rest)
      else Cookie.sanitize_go rest
  }

def Cookie.cookie_octet (b : U8) : Bool :=
  if U8.lt b 33u8 then false
  else if U8.lt 126u8 b then false
  else if U8.beq b 34u8 then false
  else if U8.beq b 44u8 then false
  else if U8.beq b 59u8 then false
  else if U8.beq b 92u8 then false
  else true

/// A `("Set-Cookie", rendered)` pair.
pub def Cookie.set_cookie (name : String) (value : String) (attrs : CookieAttrs) : Pair String String :=
  Pair.pair "Set-Cookie" (Cookie.render_with_attrs name value attrs)

/// An expiring cookie (`Max-Age=0`) that removes `name` from the client.
pub def Cookie.clear (name : String) (attrs : CookieAttrs) : Pair String String :=
  let cleared : CookieAttrs := { attrs with max_age := Option.some 0 } in
  Cookie.set_cookie name "" cleared

def Cookie.render_with_attrs (name : String) (value : String) (attrs : CookieAttrs) : String :=
  let base := Cookie.render name value in
  let with_path :=
    if String.is_empty attrs.path
    then base
    else String.concat base (String.concat "; Path=" attrs.path) in
  let with_age :=
    match attrs.max_age {
      Option.none => with_path,
      Option.some n => String.concat with_path (String.concat "; Max-Age=" (I64.to_string n))
    } in
  let with_http :=
    if attrs.http_only then String.concat with_age "; HttpOnly" else with_age in
  let with_secure :=
    if attrs.secure then String.concat with_http "; Secure" else with_http in
  String.concat with_secure (String.concat "; SameSite=" (Cookie.same_site_str attrs.same_site))

def Cookie.same_site_str (s : SameSite) : String :=
  match s {
    SameSite.lax => "Lax",
    SameSite.strict => "Strict",
    SameSite.none => "None"
  }
