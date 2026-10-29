/// The client flow: authorization URL, code exchange, refresh, userinfo.
///
/// Every request goes through the injected `OauthHttp`. Token requests are
/// form-encoded with `Form.encode` (space as `+`) and set `Content-Type`
/// explicitly — `motes/moose` adds only `Host` and `Content-Length`.
///
/// Client authentication: `client_secret_basic` puts the credential in an
/// `Authorization: Basic` header and omits `client_id` from the body;
/// `client_secret_post` and `client_public` put `client_id` (and the
/// secret, when configured) in the body.

use std::list {List.intercalate}
use http::types {Body, Headers, Headers.empty, Headers.set, Response, Status.ok, Uri}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::uri {Uri.format}
use json::json {Json, Json.get_object, Json.make_object, Json.parse}
use std::base64 {B64.encode_std}
use lib::config {ClientAuth, OauthConfig}
use lib::discovery {OauthEndpoints}
use lib::errors {OauthError, OauthError.to_string}
use moose::form {Form.encode, Form.encode_component}
use lib::http_client {OauthHttp, OauthHttp.send_get, OauthHttp.send_post}
use lib::pkce {Pkce.challenge, Pkce.method}
use lib::state {PendingAuth}
use lib::token {OauthTokenSet, Token.parse}

// ── the authorization URL ────────────────────────────────────────────────

def Client.append_query (base : String) (query : String) : String :=
  if String.is_empty query then base
  else if String.contains base "?" then String.concat base (String.concat "&" query)
  else String.concat base (String.concat "?" query)

def Client.authorize_pairs
  (client_id : String) (redirect_uri : String) (scope : String) (state : String)
  (nonce : String) (challenge : String) (audience : Option String)
  : List (Pair String String) :=
  let base : List (Pair String String) := [
    Pair.pair "response_type" "code",
    Pair.pair "client_id" client_id,
    Pair.pair "redirect_uri" redirect_uri
  ] in
  let with_scope : List (Pair String String) :=
    if String.is_empty scope then base else List.append base [Pair.pair "scope" scope]
  in
  let rest : List (Pair String String) := [
    Pair.pair "state" state,
    Pair.pair "nonce" nonce,
    Pair.pair "code_challenge" challenge,
    Pair.pair "code_challenge_method" Pkce.method
  ] in
  let all := List.append with_scope rest in
  match audience {
    Option.none => all,
    Option.some a => List.append all [Pair.pair "audience" a]
  }

/// `authorization_endpoint?...` with parameters in a fixed order:
/// `response_type`, `client_id`, `redirect_uri`, `scope` (when non-empty),
/// `state`, `nonce`, `code_challenge`,
/// `code_challenge_method=S256`, `audience` (when configured).
///
/// `redirect_uri` is taken from `cfg`, the same source `exchange_code`
/// uses: RFC 6749 §4.1.3 requires the token request to repeat the value
/// the authorization request carried, so there is exactly one spelling of
/// it. `OauthStateStore.begin` should be given that same value, since its
/// entry is what the callback is checked against.
pub def Client.authorize_url
  (cfg : OauthConfig) (ep : OauthEndpoints) (p : PendingAuth)
  : String :=
  match cfg {
    { client_id, scopes, audience, redirect_uri, .. } =>
      match ep {
        { authorization, .. } =>
          match p {
            { state, nonce, verifier, .. } =>
              let scope := List.intercalate " " scopes in
              let query := Form.encode
                (Client.authorize_pairs client_id redirect_uri scope state nonce
                  (Pkce.challenge verifier) audience) in
              Client.append_query (Uri.format authorization) query
          }
      }
  }

// ── token requests ───────────────────────────────────────────────────────

def Client.form_headers : Headers :=
  Headers.set "Accept" "application/json"
    (Headers.set "Content-Type" "application/x-www-form-urlencoded" Headers.empty)

/// RFC 6749 §2.3.1: both components form-urlencoded, then standard base64.
def Client.basic_auth (client_id : String) (secret : String) : String :=
  let userpass :=
    String.concat (Form.encode_component client_id)
      (String.concat ":" (Form.encode_component secret))
  in
  String.concat "Basic " (B64.encode_std (String.to_list userpass))

def Client.basic_of (client_id : String) (client_secret : Option String) : String :=
  match client_secret {
    Option.none => "",
    Option.some s => Client.basic_auth client_id s
  }

def Client.secret_pairs
  (client_id : String) (client_secret : Option String)
  : List (Pair String String) :=
  match client_secret {
    Option.none => [Pair.pair "client_id" client_id],
    Option.some s => [
      Pair.pair "client_id" client_id,
      Pair.pair "client_secret" s
    ]
  }

def Client.post_form
  (h : OauthHttp) (u : Uri) (hdrs : Headers) (pairs : List (Pair String String))
  : IO (Result OauthError OauthTokenSet) := do {
  let payload := Body.from_text (Form.encode pairs);
  let resp <- OauthHttp.send_post h u hdrs payload;
  return (match resp {
    Result.err e =>
      Result.err (OauthError.token_request_failed (OauthError.to_string e)),
    Result.ok r =>
      match r {
        { status, body, .. } => Token.parse status body
      }
  })
}

def Client.post_form_basic
  (h : OauthHttp) (u : Uri) (basic : String) (pairs : List (Pair String String))
  : IO (Result OauthError OauthTokenSet) :=
  Client.post_form h u (Headers.set "Authorization" basic Client.form_headers) pairs

def Client.token_request
  (h : OauthHttp) (u : Uri) (client_id : String) (client_secret : Option String)
  (client_auth : ClientAuth) (pairs : List (Pair String String))
  : IO (Result OauthError OauthTokenSet) :=
  match client_auth {
    ClientAuth.client_public =>
      Client.post_form h u Client.form_headers
        (List.append pairs [Pair.pair "client_id" client_id]),
    ClientAuth.client_secret_post =>
      Client.post_form h u Client.form_headers
        (List.append pairs (Client.secret_pairs client_id client_secret)),
    ClientAuth.client_secret_basic =>
      Client.post_form_basic h u (Client.basic_of client_id client_secret) pairs
  }

def Client.code_pairs
  (code : String) (redirect_uri : String) (verifier : String)
  : List (Pair String String) := [
  Pair.pair "grant_type" "authorization_code",
  Pair.pair "code" code,
  Pair.pair "redirect_uri" redirect_uri,
  Pair.pair "code_verifier" verifier
]

/// Exchange an authorization code (with its PKCE verifier) for tokens.
pub def Client.exchange_code
  (h : OauthHttp) (cfg : OauthConfig) (ep : OauthEndpoints)
  (code : String) (verifier : String)
  : IO (Result OauthError OauthTokenSet) :=
  match cfg {
    { client_id, client_secret, client_auth, redirect_uri, .. } =>
      match ep {
        { token, .. } =>
          Client.token_request h token client_id client_secret client_auth
            (Client.code_pairs code redirect_uri verifier)
      }
  }

/// Refresh an access token.
pub def Client.refresh
  (h : OauthHttp) (cfg : OauthConfig) (ep : OauthEndpoints) (refresh_token : String)
  : IO (Result OauthError OauthTokenSet) :=
  match cfg {
    { client_id, client_secret, client_auth, .. } =>
      match ep {
        { token, .. } =>
          let pairs : List (Pair String String) := [
            Pair.pair "grant_type" "refresh_token",
            Pair.pair "refresh_token" refresh_token
          ] in
          Client.token_request h token client_id client_secret client_auth pairs
      }
  }

// ── userinfo ─────────────────────────────────────────────────────────────

def Client.bearer_headers (token : String) : Headers :=
  Headers.set "Accept" "application/json"
    (Headers.set "Authorization" (String.concat "Bearer " token) Headers.empty)

def Client.userinfo_body (r : Response) : Result OauthError Json :=
  match r {
    { status, body, .. } =>
      if U16.beq status Status.ok
      then
        match Json.parse (String.from_list (Body.to_bytes_pure body)) {
          Result.err _ => Result.err OauthError.userinfo_invalid_json,
          Result.ok j =>
            match Json.get_object j {
              Result.err _ => Result.err OauthError.userinfo_invalid_json,
              Result.ok o => Result.ok (Json.make_object o)
            }
        }
      else Result.err (OauthError.userinfo_status status)
  }

def Client.get_userinfo
  (h : OauthHttp) (u : Uri) (token : String)
  : IO (Result OauthError Json) := do {
  let resp <- OauthHttp.send_get h u (Client.bearer_headers token);
  return (match resp {
    Result.err _ => Result.err OauthError.userinfo_request_failed,
    Result.ok r => Client.userinfo_body r,
  })
}

/// The userinfo claims as a JSON object. The plan's Phase 1 does not
/// compare the `sub` here against the ID token; that is Phase 2's
/// `Claims.validate_id_token`.
pub def Client.userinfo
  (h : OauthHttp) (ep : OauthEndpoints) (access_token : String)
  : IO (Result OauthError Json) := do {
  match ep {
    { userinfo, .. } =>
      match userinfo {
        Option.none => return (Result.err OauthError.userinfo_not_configured),
        Option.some u => Client.get_userinfo h u access_token
      }
  }
}
