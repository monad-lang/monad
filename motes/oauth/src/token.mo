/// Token-endpoint response parsing.
///
/// The rules are deliberately narrow. A response must be HTTP 200, a JSON
/// object, and carry a non-empty `access_token` and a `bearer`
/// `token_type`; `expires_in` must be a non-negative integer (the JSON
/// parser produces integers only, so a JSON float arrives as an integer
/// and cannot be told apart — a string or a negative value is rejected);
/// `refresh_token`/`id_token` are non-empty when present; `scope` is split
/// on spaces with empty entries dropped.
///
/// `summary` is what may be logged: it never contains a token value.

use std::map {BTreeMap, BTreeMap.to_list}
use std::list {List.filter}
use json::json {
  Json, Json.get_num, Json.get_num_i64, Json.get_object, Json.get_str, Json.parse,
}
use http::types {Body, Status.ok}
use http::body {Body.to_bytes_pure}
use http::strings {Strings.split_on}
use lib::errors {OauthError}

pub struct OauthTokenSet {
  access_token : String,
  token_type : String,
  expires_in : Option I64,
  refresh_token : Option String,
  id_token : Option String,
  scope : List String
}

/// Accumulator for the one-pass walk over the JSON object. All values are
/// still unvalidated; `invalid` names the FIRST field that failed its
/// type/shape rule (empty string means none).
struct TokenParts {
  access_token : Option String,
  token_type : Option String,
  expires_in : Option I64,
  refresh_token : Option String,
  id_token : Option String,
  scope : Option String,
  invalid : String
}

def Token.empty_parts : TokenParts :=
  let p : TokenParts := {
    access_token := Option.none,
    token_type := Option.none,
    expires_in := Option.none,
    refresh_token := Option.none,
    id_token := Option.none,
    scope := Option.none,
    invalid := ""
  } in
  p

def Token.field_name (which : I64) : String :=
  if I64.beq which 0i64 then "access_token"
  else if I64.beq which 1i64 then "token_type"
  else if I64.beq which 2i64 then "expires_in"
  else if I64.beq which 3i64 then "refresh_token"
  else if I64.beq which 4i64 then "id_token"
  else "scope"

def Token.mark_invalid (which : I64) (parts : TokenParts) : TokenParts :=
  match parts {
    { access_token, token_type, expires_in, refresh_token, id_token, scope, invalid } =>
      let first : String :=
        if String.is_empty invalid then Token.field_name which else invalid
      in
      let out : TokenParts := {
        access_token := access_token,
        token_type := token_type,
        expires_in := expires_in,
        refresh_token := refresh_token,
        id_token := id_token,
        scope := scope,
        invalid := first
      } in
      out
  }

def Token.set_text (which : I64) (s : String) (parts : TokenParts) : TokenParts :=
  match parts {
    { access_token, token_type, expires_in, refresh_token, id_token, scope, invalid } =>
      let access := if I64.beq which 0i64 then Option.some s else access_token in
      let typ := if I64.beq which 1i64 then Option.some s else token_type in
      let refresh := if I64.beq which 3i64 then Option.some s else refresh_token in
      let idtok := if I64.beq which 4i64 then Option.some s else id_token in
      let sc := if I64.beq which 5i64 then Option.some s else scope in
      let out : TokenParts := {
        access_token := access,
        token_type := typ,
        expires_in := expires_in,
        refresh_token := refresh,
        id_token := idtok,
        scope := sc,
        invalid := invalid
      } in
      out
  }

def Token.set_expires (n : I64) (parts : TokenParts) : TokenParts :=
  match parts {
    { access_token, token_type, refresh_token, id_token, scope, invalid, .. } =>
      let out : TokenParts := {
        access_token := access_token,
        token_type := token_type,
        expires_in := Option.some n,
        refresh_token := refresh_token,
        id_token := id_token,
        scope := scope,
        invalid := invalid
      } in
      out
  }

def Token.text_field (which : I64) (v : Json) (parts : TokenParts) : TokenParts :=
  match Json.get_str v {
    Result.err _ => Token.mark_invalid which parts,
    Result.ok sraw =>
      let s : String := sraw in
      if String.is_empty s
      then Token.mark_invalid which parts
      else Token.set_text which s parts
  }

def Token.num_field (v : Json) (parts : TokenParts) : TokenParts :=
  match Json.get_num_i64 (Json.get_num v) {
    Result.err _ => Token.mark_invalid 2i64 parts,
    Result.ok nraw =>
      let n : I64 := nraw in
      if I64.lt n 0i64
      then Token.mark_invalid 2i64 parts
      else Token.set_expires n parts
  }

def Token.drop_value (v : Json) (parts : TokenParts) : TokenParts :=
  match v {
    _ => parts
  }

def Token.collect_one (k : String) (v : Json) (parts : TokenParts) : TokenParts :=
  if k == "access_token" then Token.text_field 0i64 v parts
  else if k == "token_type" then Token.text_field 1i64 v parts
  else if k == "expires_in" then Token.num_field v parts
  else if k == "refresh_token" then Token.text_field 3i64 v parts
  else if k == "id_token" then Token.text_field 4i64 v parts
  else if k == "scope" then Token.text_field 5i64 v parts
  else Token.drop_value v parts

#[terminating]
def Token.collect_all (pairs : List (Pair String Json)) (parts : TokenParts) : TokenParts :=
  match pairs {
    List.empty => parts,
    List.cons p rest =>
      match p {
        Pair.pair k v => Token.collect_all rest (Token.collect_one k v parts)
      }
  }

def Token.with_scope
  (access_token : String) (token_type : String) (expires_in : Option I64)
  (refresh_token : Option String) (id_token : Option String) (scope : Option String)
  : Result OauthError OauthTokenSet :=
  match scope {
    Option.none =>
      Token.build access_token token_type expires_in refresh_token id_token List.empty,
    Option.some s =>
      Token.build access_token token_type expires_in refresh_token id_token
        (Token.split_scope s)
  }

def Token.build
  (access_token : String) (token_type : String) (expires_in : Option I64)
  (refresh_token : Option String) (id_token : Option String) (scope : List String)
  : Result OauthError OauthTokenSet :=
  let t : OauthTokenSet := {
    access_token := access_token,
    token_type := token_type,
    expires_in := expires_in,
    refresh_token := refresh_token,
    id_token := id_token,
    scope := scope
  } in
  Result.ok t

def Token.split_scope (s : String) : List String :=
  List.filter (fn (part : String) => Bool.not (String.is_empty part))
    (Strings.split_on " " s)

def Token.is_bearer (t : String) : Bool :=
  String.to_lowercase t == "bearer"

def Token.finish (parts : TokenParts) : Result OauthError OauthTokenSet :=
  match parts {
    { access_token, token_type, expires_in, refresh_token, id_token, scope, invalid } =>
      if Bool.not (String.is_empty invalid)
      then Result.err (OauthError.token_invalid_field invalid)
      else match access_token {
        Option.none => Result.err OauthError.token_missing_access_token,
        Option.some a =>
          match token_type {
            Option.none => Result.err OauthError.token_missing_token_type,
            Option.some traw =>
              let t : String := traw in
              if Token.is_bearer t
              then Token.with_scope a t expires_in refresh_token id_token scope
              else Result.err (OauthError.token_bad_token_type t)
          }
      }
  }

def Token.from_object (obj : BTreeMap String Json) : Result OauthError OauthTokenSet :=
  Token.finish (Token.collect_all (BTreeMap.to_list obj) Token.empty_parts)

pub def Token.parse_json (j : Json) : Result OauthError OauthTokenSet :=
  match Json.get_object j {
    Result.err _ => Result.err OauthError.token_invalid_json,
    Result.ok obj => Token.from_object obj
  }

pub def Token.parse_text (s : String) : Result OauthError OauthTokenSet :=
  match Json.parse s {
    Result.err _ => Result.err OauthError.token_invalid_json,
    Result.ok j => Token.parse_json j
  }

/// A token-endpoint response body, from its status and body.
pub def Token.parse (status : U16) (body : Body) : Result OauthError OauthTokenSet :=
  if U16.beq status Status.ok
  then Token.parse_text (String.from_list (Body.to_bytes_pure body))
  else Result.err (OauthError.token_status status)

pub def OauthTokenSet.is_bearer (t : OauthTokenSet) : Bool :=
  match t {
    { token_type, .. } => Token.is_bearer token_type
  }

def OauthTokenSet.expiry_text (e : Option I64) : String :=
  match e {
    Option.none => "expires_in=unknown",
    Option.some n => String.concat "expires_in=" (I64.to_string n)
  }

def OauthTokenSet.refresh_text (r : Option String) : String :=
  match r {
    Option.none => "refresh=no",
    Option.some _ => "refresh=yes"
  }

/// Loggable form: the type, a mask, and non-secret metadata. Never the
/// access, refresh, or ID token.
pub def OauthTokenSet.summary (t : OauthTokenSet) : String :=
  match t {
    { token_type, expires_in, refresh_token, .. } =>
      String.concat token_type
        (String.concat " **** "
          (String.concat (OauthTokenSet.expiry_text expires_in)
            (String.concat " " (OauthTokenSet.refresh_text refresh_token))))
  }
