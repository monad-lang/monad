/// Client configuration and its validation.
///
/// The issuer is CONFIGURATION, never user input: discovery and every
/// endpoint are derived from it, which is what makes the same-origin rule
/// enforceable. HTTPS is required except for an explicit localhost
/// development exception; custom native-app schemes are not supported in
/// this phase.

use http::types {Uri}
use http::uri {Uri.parse}
use std::list {List.intercalate}
use lib::errors {OauthError}

/// How the client authenticates at the token endpoint.
pub type ClientAuth {
  client_secret_basic,
  client_secret_post,
  client_public
}

pub struct OauthConfig {
  issuer : String,
  client_id : String,
  redirect_uri : String,
  client_secret : Option String := Option.none,
  client_auth : ClientAuth := ClientAuth.client_public,
  scopes : List String := List.empty,
  audience : Option String := Option.none,
  roles_claim : String := "roles",
  clock_skew_seconds : I64 := 60i64,
  secure_cookies : Bool := true,
  allow_insecure_localhost : Bool := false
}

/// The `scope` parameter: the configured scopes joined by single spaces.
pub def OauthConfig.scope_string (cfg : OauthConfig) : String :=
  List.intercalate " " cfg.scopes

/// Only these hosts get the plain-HTTP development exception. Bracketed
/// IPv6 literals are not supported (the URI parser does not accept them).
pub def OauthConfig.is_loopback_host (host : String) : Bool :=
  host == "localhost" || host == "127.0.0.1"

def OauthConfig.present (o : Option String) : Bool :=
  match o {
    Option.none => false,
    Option.some _ => true
  }

/// `true` when the scheme is not HTTPS and the development exception does
/// not apply.
def OauthConfig.insecure_scheme (allow_insecure : Bool) (scheme : String) (host : String) : Bool :=
  if scheme == "https" then false
  else if allow_insecure then Bool.not (OauthConfig.is_loopback_host host)
  else true

/// `strict` also rejects a query component (issuers must be plain origins
/// plus a path); fragments are always rejected.
def OauthConfig.check_url
  (allow_insecure : Bool) (what : String) (strict : Bool) (u : Uri)
  : Option OauthError :=
  match u {
    Uri.uri scheme userinfo host port path query fragment =>
      if OauthConfig.insecure_scheme allow_insecure scheme host
      then Option.some (OauthError.config_insecure_uri what)
      else if OauthConfig.present userinfo
      then Option.some (OauthError.config_invalid_uri what)
      else if strict && OauthConfig.present query
      then Option.some (OauthError.config_invalid_uri what)
      else if OauthConfig.present fragment
      then Option.some (OauthError.config_invalid_uri what)
      else Option.none
  }

def OauthConfig.url_error
  (allow_insecure : Bool) (what : String) (strict : Bool) (s : String)
  : Option OauthError :=
  match Uri.parse s {
    Result.err _ => Option.some (OauthError.config_invalid_uri what),
    Result.ok u => OauthConfig.check_url allow_insecure what strict u
  }

def OauthConfig.require_secret (client_secret : Option String) : Result OauthError Unit :=
  match client_secret {
    Option.none => Result.err OauthError.config_secret_required,
    Option.some s =>
      if String.is_empty s then Result.err OauthError.config_secret_required
      else Result.ok unit
  }

def OauthConfig.secret_error (client_secret : Option String) (client_auth : ClientAuth) : Result OauthError Unit :=
  match client_auth {
    ClientAuth.client_public => Result.ok unit,
    ClientAuth.client_secret_basic => OauthConfig.require_secret client_secret,
    ClientAuth.client_secret_post => OauthConfig.require_secret client_secret
  }

/// The field-level rules, by explicit arguments, so callers that still
/// need the config afterwards (discovery) do not have to consume it.
def OauthConfig.validate_fields
  (issuer : String) (client_id : String) (client_secret : Option String)
  (client_auth : ClientAuth) (redirect_uri : String)
  (clock_skew_seconds : I64) (allow_insecure_localhost : Bool)
  : Result OauthError Unit :=
  if String.is_empty client_id then Result.err OauthError.config_client_id_empty
  else if I64.lt clock_skew_seconds 0i64 then Result.err OauthError.config_skew_negative
  else if String.is_empty issuer then Result.err (OauthError.config_invalid_uri "issuer")
  else match OauthConfig.url_error allow_insecure_localhost "issuer" true issuer {
    Option.some e => Result.err e,
    Option.none =>
      if String.is_empty redirect_uri
      then Result.err (OauthError.config_invalid_uri "redirect_uri")
      else match OauthConfig.url_error allow_insecure_localhost "redirect_uri" false redirect_uri {
        Option.some e => Result.err e,
        Option.none => OauthConfig.secret_error client_secret client_auth
      }
  }

pub def OauthConfig.validate (cfg : OauthConfig) : Result OauthError Unit :=
  match cfg {
    { issuer, client_id, client_secret, client_auth, redirect_uri,
      clock_skew_seconds, allow_insecure_localhost, .. } =>
      OauthConfig.validate_fields issuer client_id client_secret client_auth
        redirect_uri clock_skew_seconds allow_insecure_localhost
  }
