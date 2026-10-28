/// OpenID Provider metadata discovery.
///
/// The discovery URL is DERIVED from the configured issuer — user input
/// never selects it — and the response must satisfy the plan's rules:
/// exactly HTTP 200 (a 3xx is an error, not a follow), byte-exact `issuer`
/// match, `authorization_endpoint` and `token_endpoint` present, and every
/// endpoint `http(s)` with a host, no userinfo or fragment, the same
/// origin as the issuer, and `https` unless the localhost development
/// exception applies. An optional endpoint that is present but invalid
/// fails the load rather than being dropped.

use std::map {BTreeMap, BTreeMap.to_list}
use json::json {Json, Json.get_object, Json.get_str, Json.parse}
use http::types {Body, Headers, Headers.empty, Headers.set, Response, Status.ok, Uri}
use http::body {Body.to_bytes_pure}
use http::uri {Uri.parse}
use lib::config {OauthConfig, OauthConfig.insecure_scheme, OauthConfig.validate_fields}
use lib::errors {OauthError}
use lib::http_client {OauthHttp, OauthHttp.send_get}

pub struct OauthEndpoints {
  authorization : Uri,
  token : Uri,
  userinfo : Option Uri,
  jwks : Option Uri,
  introspection : Option Uri,
  end_session : Option Uri
}

// ── URLs ─────────────────────────────────────────────────────────────────

/// `<issuer without one trailing slash>/.well-known/openid-configuration`.
pub def Discovery.discovery_url (issuer : String) : String :=
  let n := String.length issuer in
  let base : String :=
    if String.ends_with issuer "/"
    then String.slice issuer 0 (I64.sub n 1i64)
    else issuer
  in
  String.concat base "/.well-known/openid-configuration"

def Discovery.effective_port (scheme : String) (port : Option U16) : U16 :=
  match port {
    Option.some p => p,
    Option.none => if scheme == "https" then 443u16 else 80u16
  }

/// `scheme://host:port`, lowercased, with the scheme's default port made
/// explicit — the value every endpoint's origin is compared against.
pub def Discovery.origin (u : Uri) : String :=
  match u {
    Uri.uri scheme userinfo host port path query fragment =>
      Discovery.origin_parts scheme host port
  }

def Discovery.origin_text (issuer : String) : Option String :=
  match Uri.parse issuer {
    Result.err _ => Option.none,
    Result.ok u => Option.some (Discovery.origin u)
  }

// ── endpoint validation ──────────────────────────────────────────────────

def Discovery.present (o : Option String) : Bool :=
  match o {
    Option.none => false,
    Option.some _ => true
  }

/// The first rule an endpoint URI breaks, or `Option.none`.
def Discovery.validate_uri
  (allow_insecure : Bool) (issuer_origin : String) (name : String) (u : Uri)
  : Option OauthError :=
  match u {
    Uri.uri scheme userinfo host port path query fragment =>
      if String.is_empty host then Option.some (OauthError.discovery_invalid name)
      else if Discovery.present userinfo then Option.some (OauthError.discovery_invalid name)
      else if Discovery.present fragment then Option.some (OauthError.discovery_invalid name)
      else if Bool.not (scheme == "http" || scheme == "https")
      then Option.some (OauthError.discovery_invalid name)
      else if OauthConfig.insecure_scheme allow_insecure scheme host
      then Option.some (OauthError.discovery_insecure name)
      else if Bool.not (Discovery.origin_parts scheme host port == issuer_origin)
      then Option.some (OauthError.discovery_cross_origin name)
      else Option.none
  }

def Discovery.origin_parts (scheme : String) (host : String) (port : Option U16) : String :=
  let s := String.to_lowercase scheme in
  let h := String.to_lowercase host in
  let p := Discovery.effective_port s port in
  String.concat s
    (String.concat "://"
      (String.concat h (String.concat ":" (U16.to_string p))))

/// Validate one endpoint. `Pair` carries the parsed URI and the first
/// error (`Option.none` means fine). The URI is parsed again after
/// validation so the checked value can be returned whole — parsing twice
/// is cheaper than threading a consumed record through every rule.
def Discovery.check_endpoint
  (allow_insecure : Bool) (issuer_origin : String) (name : String) (raw : String)
  : Pair (Option Uri) (Option OauthError) :=
  if String.is_empty raw
  then Pair.pair Option.none Option.none
  else
    match Uri.parse raw {
      Result.err _ =>
        Pair.pair Option.none (Option.some (OauthError.discovery_invalid name)),
      Result.ok u =>
        match Discovery.validate_uri allow_insecure issuer_origin name u {
          Option.some e => Pair.pair Option.none (Option.some e),
          Option.none =>
            match Uri.parse raw {
              Result.err _ =>
                Pair.pair Option.none (Option.some (OauthError.discovery_invalid name)),
              Result.ok u2 => Pair.pair (Option.some u2) Option.none
            }
        }
    }

def Discovery.opt_endpoint
  (allow_insecure : Bool) (issuer_origin : String) (name : String) (raw : Option String)
  : Pair (Option Uri) (Option OauthError) :=
  match raw {
    Option.none => Pair.pair Option.none Option.none,
    Option.some s => Discovery.check_endpoint allow_insecure issuer_origin name s
  }

def Discovery.assemble
  (authorization : Option Uri) (token : Option Uri) (userinfo : Option Uri)
  (jwks : Option Uri) (introspection : Option Uri) (end_session : Option Uri)
  : Result OauthError OauthEndpoints :=
  match authorization {
    Option.none => Result.err (OauthError.discovery_missing "authorization_endpoint"),
    Option.some a =>
      match token {
        Option.none => Result.err (OauthError.discovery_missing "token_endpoint"),
        Option.some t =>
          let ep : OauthEndpoints := {
            authorization := a,
            token := t,
            userinfo := userinfo,
            jwks := jwks,
            introspection := introspection,
            end_session := end_session
          } in
          Result.ok ep
      }
  }

def Discovery.check_all
  (origin : String) (allow_insecure : Bool)
  (a_raw : String) (t_raw : String)
  (userinfo : Option String) (jwks : Option String)
  (introspection : Option String) (end_session : Option String)
  : Result OauthError OauthEndpoints :=
  match Discovery.check_endpoint allow_insecure origin "authorization_endpoint" a_raw {
    Pair.pair a_uri a_err =>
      match a_err {
        Option.some e => Result.err e,
        Option.none =>
          match Discovery.check_endpoint allow_insecure origin "token_endpoint" t_raw {
            Pair.pair t_uri t_err =>
              match t_err {
                Option.some e => Result.err e,
                Option.none =>
                  Discovery.check_optional origin allow_insecure a_uri t_uri
                    userinfo jwks introspection end_session
              }
          }
      }
  }

def Discovery.check_optional
  (origin : String) (allow_insecure : Bool) (a_uri : Option Uri) (t_uri : Option Uri)
  (userinfo : Option String) (jwks : Option String)
  (introspection : Option String) (end_session : Option String)
  : Result OauthError OauthEndpoints :=
  match Discovery.opt_endpoint allow_insecure origin "userinfo_endpoint" userinfo {
    Pair.pair ui_uri ui_err =>
      match ui_err {
        Option.some e => Result.err e,
        Option.none =>
          match Discovery.opt_endpoint allow_insecure origin "jwks_uri" jwks {
            Pair.pair jw_uri jw_err =>
              match jw_err {
                Option.some e => Result.err e,
                Option.none =>
                  match Discovery.opt_endpoint allow_insecure origin "introspection_endpoint" introspection {
                    Pair.pair in_uri in_err =>
                      match in_err {
                        Option.some e => Result.err e,
                        Option.none =>
                          match Discovery.opt_endpoint allow_insecure origin "end_session_endpoint" end_session {
                            Pair.pair es_uri es_err =>
                              match es_err {
                                Option.some e => Result.err e,
                                Option.none =>
                                  Discovery.assemble a_uri t_uri ui_uri jw_uri in_uri es_uri
                              }
                          }
                      }
                  }
              }
          }
      }
  }

// ── the document ─────────────────────────────────────────────────────────

struct DocFields {
  issuer : Option String,
  authorization : Option String,
  token : Option String,
  userinfo : Option String,
  jwks : Option String,
  introspection : Option String,
  end_session : Option String,
  wrong_type : String
}

def Discovery.empty_doc : DocFields :=
  let d : DocFields := {
    issuer := Option.none,
    authorization := Option.none,
    token := Option.none,
    userinfo := Option.none,
    jwks := Option.none,
    introspection := Option.none,
    end_session := Option.none,
    wrong_type := ""
  } in
  d

def Discovery.set_doc (which : I64) (s : String) (d : DocFields) : DocFields :=
  match d {
    { issuer, authorization, token, userinfo, jwks, introspection, end_session, wrong_type } =>
      let iss := if I64.beq which 0i64 then Option.some s else issuer in
      let auth := if I64.beq which 1i64 then Option.some s else authorization in
      let tok := if I64.beq which 2i64 then Option.some s else token in
      let ui := if I64.beq which 3i64 then Option.some s else userinfo in
      let jw := if I64.beq which 4i64 then Option.some s else jwks in
      let intr := if I64.beq which 5i64 then Option.some s else introspection in
      let es := if I64.beq which 6i64 then Option.some s else end_session in
      let out : DocFields := {
        issuer := iss,
        authorization := auth,
        token := tok,
        userinfo := ui,
        jwks := jw,
        introspection := intr,
        end_session := es,
        wrong_type := wrong_type
      } in
      out
  }

def Discovery.mark_wrong (field : String) (d : DocFields) : DocFields :=
  match d {
    { issuer, authorization, token, userinfo, jwks, introspection, end_session, wrong_type } =>
      let first : String :=
        if String.is_empty wrong_type then field else wrong_type
      in
      let out : DocFields := {
        issuer := issuer,
        authorization := authorization,
        token := token,
        userinfo := userinfo,
        jwks := jwks,
        introspection := introspection,
        end_session := end_session,
        wrong_type := first
      } in
      out
  }

def Discovery.doc_one (which : I64) (v : Json) (d : DocFields) : DocFields :=
  match Json.get_str v {
    Result.err _ => Discovery.mark_wrong (Discovery.field_name which) d,
    Result.ok s => Discovery.set_doc which s d
  }

def Discovery.field_name (which : I64) : String :=
  if I64.beq which 0i64 then "issuer"
  else if I64.beq which 1i64 then "authorization_endpoint"
  else if I64.beq which 2i64 then "token_endpoint"
  else if I64.beq which 3i64 then "userinfo_endpoint"
  else if I64.beq which 4i64 then "jwks_uri"
  else if I64.beq which 5i64 then "introspection_endpoint"
  else "end_session_endpoint"

def Discovery.collect_one (k : String) (v : Json) (d : DocFields) : DocFields :=
  if k == "issuer" then Discovery.doc_one 0i64 v d
  else if k == "authorization_endpoint" then Discovery.doc_one 1i64 v d
  else if k == "token_endpoint" then Discovery.doc_one 2i64 v d
  else if k == "userinfo_endpoint" then Discovery.doc_one 3i64 v d
  else if k == "jwks_uri" then Discovery.doc_one 4i64 v d
  else if k == "introspection_endpoint" then Discovery.doc_one 5i64 v d
  else if k == "end_session_endpoint" then Discovery.doc_one 6i64 v d
  else match v {
    _ => d
  }

#[terminating]
def Discovery.collect_all (pairs : List (Pair String Json)) (d : DocFields) : DocFields :=
  match pairs {
    List.empty => d,
    List.cons p rest =>
      match p {
        Pair.pair k v => Discovery.collect_all rest (Discovery.collect_one k v d)
      }
  }

def Discovery.finish
  (d : DocFields) (want_issuer : String) (allow_insecure : Bool)
  : Result OauthError OauthEndpoints :=
  match d {
    { issuer, authorization, token, userinfo, jwks, introspection, end_session, wrong_type } =>
      if Bool.not (String.is_empty wrong_type)
      then Result.err (OauthError.discovery_invalid wrong_type)
      else match issuer {
        Option.none => Result.err (OauthError.discovery_missing "issuer"),
        Option.some di =>
          if Bool.not (di == want_issuer) then Result.err OauthError.discovery_issuer_mismatch
          else match Discovery.origin_text want_issuer {
            Option.none => Result.err (OauthError.config_invalid_uri "issuer"),
            Option.some origin =>
              match (authorization, token) {
                Pair.pair a_raw t_raw =>
                  match a_raw {
                    Option.none => Result.err (OauthError.discovery_missing "authorization_endpoint"),
                    Option.some a =>
                      match t_raw {
                        Option.none => Result.err (OauthError.discovery_missing "token_endpoint"),
                        Option.some t =>
                          Discovery.check_all origin allow_insecure a t
                            userinfo jwks introspection end_session
                      }
                  }
              }
          }
      }
  }

// ── the request ──────────────────────────────────────────────────────────

def Discovery.json_headers : Headers :=
  Headers.set "Accept" "application/json" Headers.empty

def Discovery.parse_response
  (r : Response) (issuer : String) (allow_insecure : Bool)
  : Result OauthError OauthEndpoints :=
  match r {
    { status, body, .. } =>
      if U16.beq status Status.ok
      then Discovery.parse_document
             (String.from_list (Body.to_bytes_pure body)) issuer allow_insecure
      else if U16.gt status 299u16 && U16.gt 400u16 status
      then Result.err OauthError.discovery_redirect
      else Result.err (OauthError.discovery_status status)
  }

def Discovery.parse_document
  (s : String) (issuer : String) (allow_insecure : Bool)
  : Result OauthError OauthEndpoints :=
  match Json.parse s {
    Result.err _ => Result.err OauthError.discovery_invalid_json,
    Result.ok j =>
      match Json.get_object j {
        Result.err _ => Result.err OauthError.discovery_invalid_json,
        Result.ok obj => Discovery.finish (Discovery.collect_all (BTreeMap.to_list obj) Discovery.empty_doc) issuer allow_insecure
      }
  }

def Discovery.fetch_url
  (h : OauthHttp) (issuer : String) (allow_insecure : Bool) (u : Uri)
  : IO (Result OauthError OauthEndpoints) := do {
  let resp <- OauthHttp.send_get h u Discovery.json_headers;
  return (match resp {
    Result.err _ => Result.err OauthError.discovery_request_failed,
    Result.ok r => Discovery.parse_response r issuer allow_insecure,
  })
}

def Discovery.fetch
  (h : OauthHttp) (issuer : String) (allow_insecure : Bool)
  : IO (Result OauthError OauthEndpoints) := do {
  let url := Discovery.discovery_url issuer;
  match Uri.parse url {
    Result.err _ => return (Result.err OauthError.discovery_url_invalid),
    Result.ok u => Discovery.fetch_url h issuer allow_insecure u
  }
}

/// Validate the configuration, then fetch and validate the document.
/// Every endpoint is derived from `cfg.issuer`; nothing here accepts a
/// user-supplied discovery URL.
pub def Discovery.load (h : OauthHttp) (cfg : OauthConfig) : IO (Result OauthError OauthEndpoints) := do {
  match cfg {
    { issuer, client_id, client_secret, client_auth, redirect_uri,
      clock_skew_seconds, allow_insecure_localhost, .. } =>
      match OauthConfig.validate_fields issuer client_id client_secret client_auth
              redirect_uri clock_skew_seconds allow_insecure_localhost {
        Result.err e => return (Result.err e),
        Result.ok _ => Discovery.fetch h issuer allow_insecure_localhost
      }
  }
}
