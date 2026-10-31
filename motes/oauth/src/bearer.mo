/// Resource-server bearer authentication (Phases 3-4).
///
/// `Bearer.require` authenticates a bearer token in one of two modes:
///
///   * `BearerValidator.jwt` parses the JWT, fetches/caches the issuer's
///     JWKS through the injected `OauthHttp`, verifies it with
///     `jsonwebtoken`, and validates the access-token claims;
///   * `BearerValidator.introspect` sends the opaque token to the RFC 7662
///     introspection endpoint and maps the active response.
///
/// Both modes then enforce the required scopes and only call the handler with
/// a verified `Principal`. There is no Moon dependency: the handler has the
/// structural `Principal -> Request -> IO (Result String Response)` type.
///
/// Failures are RFC 6750 responses: 401 with `WWW-Authenticate: Bearer
/// realm="api"` (missing) or `error="invalid_token"` (invalid/expired/
/// inactive), 403 with `error="insufficient_scope", scope="..."`, and 503
/// with `error="temporarily_unavailable"` when the identity provider is
/// unavailable. Bodies are generic JSON and carry no token or claim detail;
/// every authentication response is `Cache-Control: no-store`.

use std::list {List.any, List.filter, List.intercalate, List.length}
use std::ref {Ref, Ref.get, Ref.new, Ref.update}
use json::json {Json, Json.get_array, Json.get_object, Json.object_get, Json.parse}
use http::types {
  Body, Headers, Headers.empty, Headers.get_all, Headers.set, Request, Response,
  Response.json, Response.with_header, Status.forbidden, Status.internal_server_error,
  Status.ok, Status.service_unavailable, Status.unauthorized,
}
use http::body {Body.to_bytes_pure}
use jsonwebtoken::claims {Claims.validate_access_token, Claims.validate_id_token}
use jsonwebtoken::errors {JwtError, JwtError.to_string}
use jsonwebtoken::jwt {Jwt, Jwt.parse, Jwt.verify}
use jsonwebtoken::principal {Principal}
use jsonwebtoken::verifier {JwtVerifier}
use lib::config {OauthConfig, OauthConfig.claims_config}
use lib::discovery {OauthEndpoints}
use lib::errors {AuthError}
use lib::http_client {OauthHttp, OauthHttp.send_get}
use lib::introspect {Introspector, Introspector.new, Introspector.principal}

def Bearer.realm : String := "api"
def Bearer.max_token_bytes : I64 := 16384i64
def Bearer.max_jwks_bytes : I64 := 65536i64
def Bearer.ttl_seconds : I64 := 300i64
def Bearer.min_fetch_seconds : I64 := 1i64

// ── state ──────────────────────────────────────────────────────────────────

/// One cached JWKS document.
pub struct JwksCache {
  jwks : Json,
  fetched_at : I64
}

/// The JWKS cache and the two fetch clocks.
///
/// `last_fetch` bounds ordinary (cold/expired) fetches; `last_forced` bounds
/// unknown-kid refetches independently, so a legitimate rotation is not
/// blocked by the TTL fetch that just happened. `claimed` is the outcome of
/// the update that produced this value: each caller reads its own
/// `Ref.update` result, so concurrent claimers get exactly one `true` and no
/// caller can lose another's cache write.
pub struct JwksState {
  cache : Option JwksCache,
  last_fetch : I64,
  last_forced : I64,
  claimed : Bool
}

/// The token-validation strategy. JWT mode carries the JWKS plumbing;
/// introspection mode carries the RFC 7662 client and its cache.
pub type TokenMode {
  token_jwt
    (cfg : OauthConfig)
    (endpoints : OauthEndpoints)
    (http : OauthHttp)
    (verifier : JwtVerifier)
    (state : Ref JwksState),
  token_introspect (intro : Introspector)
}

/// A configured guard. Construct it once with `jwt` or `introspect`.
pub struct BearerValidator {
  mode : TokenMode
}

/// JWT mode: verify with the given verifier and cache the issuer's JWKS.
pub def BearerValidator.jwt
  (cfg : OauthConfig) (ep : OauthEndpoints) (h : OauthHttp) (v : JwtVerifier)
  : IO BearerValidator := do {
  let empty : JwksState := {
    cache := Option.none,
    last_fetch := 0i64,
    last_forced := 0i64,
    claimed := false
  };
  let cell <- Ref.new empty;
  let out : BearerValidator := {
    mode := TokenMode.token_jwt cfg ep h v cell
  };
  return out
}

/// Opaque-token mode: RFC 7662 introspection, with its own response cache.
pub def BearerValidator.introspect
  (cfg : OauthConfig) (ep : OauthEndpoints) (h : OauthHttp)
  : IO BearerValidator := do {
  let intro <- Introspector.new cfg ep h;
  let out : BearerValidator := {
    mode := TokenMode.token_introspect intro
  };
  return out
}

// ── the guard ─────────────────────────────────────────────────────────────

/// Authenticate `req`, enforce `required` scopes, and call `handler` with the
/// verified `Principal`. Failures are returned as `Ok` RFC 6750 responses;
/// only a handler failure passes through as `Err`.
pub def Bearer.require
  (v : BearerValidator) (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request)
  : IO (Result String Response) := do {
  let ms <- IO.current_time;
  Bearer.require_at v required handler req (I64.div ms 1000i64)
}

/// The deterministic seam: `now` is epoch seconds. Tests use it; the public
/// wrapper reads the clock.
def Bearer.require_at
  (v : BearerValidator) (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64)
  : IO (Result String Response) := do {
  match Bearer.extract_token req {
    Result.err e => return (Result.ok (Bearer.response_of e)),
    Result.ok token => Bearer.dispatch v required handler req now token
  }
}

def Bearer.dispatch
  (v : BearerValidator) (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (token : String)
  : IO (Result String Response) :=
  match v.mode {
    TokenMode.token_jwt cfg ep http verifier state =>
      Bearer.check_jwt_token cfg ep http verifier state required handler req now token,
    TokenMode.token_introspect intro =>
      Bearer.check_introspected intro required handler req now token
  }

def Bearer.check_introspected
  (intro : Introspector) (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (token : String)
  : IO (Result String Response) := do {
  let r <- Introspector.principal intro now token;
  match r {
    Result.err e => return (Result.ok (Bearer.response_of e)),
    Result.ok principal => Bearer.authorize required handler principal req
  }
}

def Bearer.check_jwt_token
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (token : String)
  : IO (Result String Response) := do {
  match Jwt.parse token {
    Result.err e => return (Result.ok (Bearer.response_of (Bearer.auth_error e))),
    Result.ok jwt =>
      Bearer.load_and_verify cfg ep http verifier state required handler req now jwt false
  }
}

#[terminating]
def Bearer.load_and_verify
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (jwt : Jwt) (force : Bool)
  : IO (Result String Response) := do {
  let doc <- Bearer.jwks_doc state ep http now force;
  match doc {
    Result.err e => return (Result.ok (Bearer.response_of e)),
    Result.ok jwks =>
      Bearer.verify_jwt cfg ep http verifier state required handler req now jwks jwt force
  }
}

#[terminating]
def Bearer.verify_jwt
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (jwks : Json) (jwt : Jwt) (force : Bool)
  : IO (Result String Response) := do {
  let checked <- Jwt.verify verifier jwks jwt;
  match checked {
    Result.err e =>
      Bearer.on_jwt_error cfg ep http verifier state required handler req now jwt e force,
    Result.ok _ =>
      Bearer.validate_and_authorize cfg required handler req now jwt
  }
}

#[terminating]
def Bearer.on_jwt_error
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (jwt : Jwt) (e : JwtError) (force : Bool)
  : IO (Result String Response) :=
  match e {
    JwtError.jwks_unknown_kid =>
      if force
      then return (Result.ok (Bearer.response_of (Bearer.auth_error e)))
      else Bearer.load_and_verify cfg ep http verifier state required handler req now jwt true,
    _ => return (Result.ok (Bearer.response_of (Bearer.auth_error e)))
  }

def Bearer.validate_and_authorize
  (cfg : OauthConfig) (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (req : Request) (now : I64) (jwt : Jwt)
  : IO (Result String Response) := do {
  let claims_cfg := OauthConfig.claims_config cfg;
  match Claims.validate_access_token claims_cfg now jwt {
    Result.err e => return (Result.ok (Bearer.response_of (Bearer.auth_error e))),
    Result.ok principal => Bearer.authorize required handler principal req
  }
}

def Bearer.authorize
  (required : List String)
  (handler : Principal -> Request -> IO (Result String Response))
  (principal : Principal) (req : Request)
  : IO (Result String Response) :=
  let missing := Bearer.missing_scopes required principal.scopes in
  if I64.beq (List.length missing) 0i64
  then handler principal req
  else return (Result.ok (Bearer.response_of (AuthError.auth_insufficient_scope missing)))

def Bearer.missing_scopes
  (required : List String) (granted : List String)
  : List String :=
  List.filter
    (fn (s : String) =>
      Bool.not (List.any (fn (g : String) => g == s) granted))
    required

// ── token extraction ──────────────────────────────────────────────────────

/// Exactly one `Authorization` header, and it must be a non-empty Bearer
/// token no larger than 16 KiB with no embedded whitespace.
def Bearer.extract_token (req : Request) : Result AuthError String :=
  match Headers.get_all "Authorization" req.headers {
    List.empty => Result.err AuthError.auth_missing_token,
    List.cons single rest =>
      match rest {
        List.cons _ _ =>
          Result.err (AuthError.auth_invalid_token "duplicate Authorization headers"),
        List.empty => Bearer.bearer_value single
      }
  }

def Bearer.bearer_value (value : String) : Result AuthError String :=
  if I64.lt (String.length value) 8i64
  then Result.err AuthError.auth_missing_token
  else if Bool.not (String.to_lowercase (String.slice value 0i64 7i64) == "bearer ")
  then Result.err AuthError.auth_missing_token
  else Bearer.checked_token (String.drop 7i64 value)

def Bearer.checked_token (token : String) : Result AuthError String :=
  if String.is_empty token
  then Result.err AuthError.auth_missing_token
  else if I64.gt (String.length token) Bearer.max_token_bytes
  then Result.err (AuthError.auth_invalid_token "bearer token exceeds 16 KiB")
  else if String.contains token " "
  then Result.err (AuthError.auth_invalid_token "bearer token contains whitespace")
  else Result.ok token

// ── JWKS fetch and cache ───────────────────────────────────────────────────

def Bearer.fresh (now : I64) (fetched_at : I64) : Bool :=
  I64.lt (I64.sub now fetched_at) Bearer.ttl_seconds

def Bearer.rate_limited (now : I64) (last : I64) : Bool :=
  I64.lt (I64.sub now last) Bearer.min_fetch_seconds

def Bearer.declined
  (cache : Option JwksCache) (last_fetch : I64) (last_forced : I64)
  : JwksState :=
  let s : JwksState := {
    cache := cache,
    last_fetch := last_fetch,
    last_forced := last_forced,
    claimed := false
  } in
  s

def Bearer.granted
  (cache : Option JwksCache) (last_fetch : I64) (last_forced : I64)
  : JwksState :=
  let s : JwksState := {
    cache := cache,
    last_fetch := last_fetch,
    last_forced := last_forced,
    claimed := true
  } in
  s

/// Atomically claim the right to fetch. A forced refetch is bounded by its
/// own clock, so the TTL fetch of the same request does not consume it.
def Bearer.claim_fetch
  (state : Ref JwksState) (now : I64) (force : Bool)
  : IO Bool := do {
  let st <- Ref.update state (fn (s : JwksState) =>
    if force
    then if Bearer.rate_limited now s.last_forced
         then Bearer.declined s.cache s.last_fetch s.last_forced
         else Bearer.granted s.cache now now
    else if Bearer.rate_limited now s.last_fetch
         then Bearer.declined s.cache s.last_fetch s.last_forced
         else Bearer.granted s.cache now s.last_forced);
  return st.claimed
}

def Bearer.cached_doc
  (state : Ref JwksState)
  : IO (Result AuthError Json) := do {
  let st <- Ref.get state;
  match st.cache {
    Option.none => return (Result.err AuthError.auth_temporarily_unavailable),
    Option.some c => return (Result.ok c.jwks)
  }
}

def Bearer.jwks_doc
  (state : Ref JwksState) (ep : OauthEndpoints) (http : OauthHttp)
  (now : I64) (force : Bool)
  : IO (Result AuthError Json) := do {
  let st <- Ref.get state;
  match st.cache {
    Option.none => Bearer.refresh_jwks state ep http now force,
    Option.some c =>
      if Bool.not force && Bearer.fresh now c.fetched_at
      then return (Result.ok c.jwks)
      else Bearer.refresh_jwks state ep http now force
  }
}

def Bearer.refresh_jwks
  (state : Ref JwksState) (ep : OauthEndpoints) (http : OauthHttp)
  (now : I64) (force : Bool)
  : IO (Result AuthError Json) := do {
  let claimed <- Bearer.claim_fetch state now force;
  if claimed
  then Bearer.fetch_jwks state ep http now
  else return (Result.err AuthError.auth_temporarily_unavailable)
}

def Bearer.fetch_jwks
  (state : Ref JwksState) (ep : OauthEndpoints) (http : OauthHttp) (now : I64)
  : IO (Result AuthError Json) := do {
  match ep.jwks {
    Option.none => return (Result.err AuthError.auth_temporarily_unavailable),
    Option.some u => do {
      let hdrs := Headers.set "Accept" "application/json" Headers.empty;
      let resp <- OauthHttp.send_get http u hdrs;
      match resp {
        Result.err _ => return (Result.err AuthError.auth_temporarily_unavailable),
        Result.ok r =>
          if U16.beq r.status Status.ok
          then Bearer.store_then_read state now r.body
          else return (Result.err AuthError.auth_temporarily_unavailable)
      }
    }
  }
}

def Bearer.store_then_read
  (state : Ref JwksState) (now : I64) (body : Body)
  : IO (Result AuthError Json) := do {
  let stored <- Bearer.store_jwks state now body;
  match stored {
    Result.err e => return (Result.err e),
    Result.ok _ => Bearer.cached_doc state
  }
}

/// Validate before caching: a transient `{}` or `{"keys":[]}` must not
/// poison the cache for the whole TTL. The body is capped before parsing.
def Bearer.store_jwks
  (state : Ref JwksState) (now : I64) (body : Body)
  : IO (Result AuthError Unit) := do {
  let bytes := Body.to_bytes_pure body;
  if I64.gt (List.length bytes) Bearer.max_jwks_bytes
  then return (Result.err AuthError.auth_temporarily_unavailable)
  else match Json.parse (String.from_list bytes) {
    Result.err _ => return (Result.err AuthError.auth_temporarily_unavailable),
    Result.ok j =>
      if Bool.not (Bearer.valid_jwks j)
      then return (Result.err AuthError.auth_temporarily_unavailable)
      else do {
        let entry : JwksCache := { jwks := j, fetched_at := now };
        let _ <- Ref.update state (fn (s : JwksState) =>
          let next : JwksState := {
            cache := Option.some entry,
            last_fetch := s.last_fetch,
            last_forced := s.last_forced,
            claimed := s.claimed
          } in next);
        return (Result.ok unit)
      }
  }
}

def Bearer.nonempty_array (v : Json) : Bool :=
  match Json.get_array v {
    Result.err _ => false,
    Result.ok xs => I64.gt (List.length xs) 0i64
  }

def Bearer.valid_jwks (j : Json) : Bool :=
  match Json.get_object j {
    Result.err _ => false,
    Result.ok obj =>
      match Json.object_get "keys" obj {
        Option.none => false,
        Option.some v => Bearer.nonempty_array v
      }
  }

/// Validate an OIDC ID token (nonce required) with this JWT-mode
/// validator's JWKS cache and verifier. Introspection mode has no ID token,
/// so it reports a server misconfiguration.
pub def BearerValidator.validate_id_token
  (v : BearerValidator) (now : I64) (nonce : String) (token : String)
  : IO (Result AuthError Principal) :=
  match v.mode {
    TokenMode.token_jwt cfg ep http verifier state =>
      Bearer.check_id_token cfg ep http verifier state now nonce token,
    TokenMode.token_introspect _ =>
      return (Result.err AuthError.auth_server_misconfigured)
  }

def Bearer.check_id_token
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (now : I64) (nonce : String) (token : String)
  : IO (Result AuthError Principal) := do {
  match Jwt.parse token {
    Result.err e => return (Result.err (Bearer.auth_error e)),
    Result.ok jwt =>
      Bearer.load_id_and_verify cfg ep http verifier state now nonce jwt false
  }
}

#[terminating]
def Bearer.load_id_and_verify
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (now : I64) (nonce : String) (jwt : Jwt) (force : Bool)
  : IO (Result AuthError Principal) := do {
  let doc <- Bearer.jwks_doc state ep http now force;
  match doc {
    Result.err e => return (Result.err e),
    Result.ok jwks =>
      Bearer.verify_id_jwt cfg ep http verifier state now nonce jwks jwt force
  }
}

#[terminating]
def Bearer.verify_id_jwt
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (now : I64) (nonce : String) (jwks : Json) (jwt : Jwt) (force : Bool)
  : IO (Result AuthError Principal) := do {
  let checked <- Jwt.verify verifier jwks jwt;
  match checked {
    Result.err e =>
      Bearer.on_id_jwt_error cfg ep http verifier state now nonce jwt e force,
    Result.ok _ =>
      return (match Claims.validate_id_token
        (OauthConfig.claims_config cfg) now nonce jwt {
        Result.err e => Result.err (Bearer.auth_error e),
        Result.ok principal => Result.ok principal
      })
  }
}

#[terminating]
def Bearer.on_id_jwt_error
  (cfg : OauthConfig) (ep : OauthEndpoints) (http : OauthHttp)
  (verifier : JwtVerifier) (state : Ref JwksState)
  (now : I64) (nonce : String) (jwt : Jwt) (e : JwtError) (force : Bool)
  : IO (Result AuthError Principal) :=
  match e {
    JwtError.jwks_unknown_kid =>
      if force
      then return (Result.err (Bearer.auth_error e))
      else Bearer.load_id_and_verify cfg ep http verifier state now nonce jwt true,
    _ => return (Result.err (Bearer.auth_error e))
  }

// ── responses ─────────────────────────────────────────────────────────────

def Bearer.auth_error (e : JwtError) : AuthError :=
  match e {
    JwtError.claims_expired => AuthError.auth_expired,
    JwtError.verification_failed _ => AuthError.auth_temporarily_unavailable,
    // A document-level JWKS problem is the issuer's, not the token's: the
    // client should retry later, not conclude its credential is bad.
    JwtError.jwks_invalid_document => AuthError.auth_temporarily_unavailable,
    JwtError.jwks_missing_keys => AuthError.auth_temporarily_unavailable,
    JwtError.jwks_key_invalid _ => AuthError.auth_temporarily_unavailable,
    JwtError.jwks_unsupported_kty _ => AuthError.auth_temporarily_unavailable,
    JwtError.jwks_private_key => AuthError.auth_temporarily_unavailable,
    JwtError.jwks_weak_rsa => AuthError.auth_temporarily_unavailable,
    _ => AuthError.auth_invalid_token (JwtError.to_string e)
  }

def Bearer.challenge (params : Option String) : String :=
  match params {
    Option.none => "Bearer realm=\"" ++ Bearer.realm ++ "\"",
    Option.some p => "Bearer realm=\"" ++ Bearer.realm ++ "\", " ++ p
  }

def Bearer.auth_response
  (status : U16) (challenge : String) (body : String)
  : Response :=
  let res := Response.json status body in
  Response.with_header "Cache-Control" "no-store"
    (Response.with_header "WWW-Authenticate" challenge res)

/// A server-side failure: no Bearer challenge, because the caller's
/// credential is not the problem and retrying will not help.
def Bearer.plain_response (status : U16) (body : String) : Response :=
  Response.with_header "Cache-Control" "no-store" (Response.json status body)

def Bearer.response_of (e : AuthError) : Response :=
  match e {
    AuthError.auth_missing_token =>
      Bearer.auth_response Status.unauthorized (Bearer.challenge Option.none)
        "{\"error\":\"unauthorized\"}",
    AuthError.auth_invalid_token _ =>
      Bearer.auth_response Status.unauthorized
        (Bearer.challenge (Option.some "error=\"invalid_token\""))
        "{\"error\":\"invalid_token\"}",
    AuthError.auth_expired =>
      Bearer.auth_response Status.unauthorized
        (Bearer.challenge (Option.some "error=\"invalid_token\""))
        "{\"error\":\"invalid_token\"}",
    AuthError.auth_insufficient_scope required =>
      Bearer.auth_response Status.forbidden
        (Bearer.challenge
          (Option.some
            ("error=\"insufficient_scope\", scope=\""
              ++ List.intercalate " " required ++ "\"")))
        "{\"error\":\"insufficient_scope\"}",
    AuthError.auth_temporarily_unavailable =>
      Bearer.auth_response Status.service_unavailable
        (Bearer.challenge (Option.some "error=\"temporarily_unavailable\""))
        "{\"error\":\"temporarily_unavailable\"}",
    AuthError.auth_server_misconfigured =>
      Bearer.plain_response Status.internal_server_error
        "{\"error\":\"server_error\"}"
  }
