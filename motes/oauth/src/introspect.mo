/// RFC 7662 token introspection.
///
/// `Introspector.principal` POSTs the token (form-encoded, client-authenticated)
/// to the configured introspection endpoint and maps an `active` response into
/// a `Principal`. The client is the injected `OauthHttp`, so the whole flow is
/// testable with a scripted transport.
///
/// Caching: only ACTIVE responses are cached, keyed by `SHA-256(token)` (the
/// token itself is never stored), for at most 60 seconds and never past the
/// response's own `exp`. An inactive token, a malformed response, and a
/// transport or HTTP failure are never cached; an outage is
/// `auth_temporarily_unavailable` (503 at the bearer layer), never fail-open.
///
/// Response mapping: `iss`, when present, must equal the configured issuer;
/// `aud`, when present, must contain the configured audience (or the client
/// id when no audience is configured); `token_type`, when present, must be
/// `Bearer` (a refresh token introspects as active too); `sub` is required;
/// `aud`/`scp` may be a string or an array; `scope` is space-separated;
/// roles come from the configured claim (string or array). `exp`/`nbf` are
/// skew-bounded; a response without `exp` is bounded by the 60 s cache
/// horizon.
///
/// This client does not coalesce concurrent requests for the same token or
/// rate-limit cache misses; a random-token spray reaches the IdP one-for-one.
/// That is deliberate (a negative cache is forbidden, and a throttled
/// resource server must fail closed); deploy an ingress rate limit where
/// that matters.

use std::list {List.any, List.filter}
use std::map {BTreeMap}
use std::ref {Ref, Ref.new, Ref.update}
use std::sha256 {Sha256.hash}
use json::json {
    Json, Json.get_array, Json.get_bool, Json.get_num, Json.get_num_i64,
    Json.get_object, Json.get_str, Json.object_get, Json.parse,
}
use http::types {Body, Headers, Headers.empty, Headers.set, Status.ok, Uri}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::strings {Strings.split_on}
use jsonwebtoken::principal {Principal}
use moose::form {Form.encode}
use lib::client {Client.basic_auth}
use lib::config {ClientAuth, OauthConfig}
use lib::discovery {OauthEndpoints}
use lib::errors {AuthError}
use lib::http_client {OauthHttp, OauthHttp.send_post}

def Introspect.max_ttl : I64 := 60i64
def Introspect.max_cache_entries : I64 := 1024i64
def Introspect.max_body_bytes : I64 := 65536i64
def Introspect.max_token_bytes : I64 := 16384i64

// ── state ──────────────────────────────────────────────────────────────────

/// One cached active response. The key is the hex SHA-256 of the token; the
/// body is the introspection response, never the token.
pub struct IntrospectEntry {
    key : String,
    body : String,
    expires_at : I64
}

/// The introspection client: configuration, the injected transport, the
/// endpoint (absent when discovery did not publish one), and the cache.
pub struct Introspector {
    cfg : OauthConfig,
    http : OauthHttp,
    uri : Option Uri,
    cache : Ref (List IntrospectEntry)
}

/// Build an introspector for `ep`'s introspection endpoint. A missing endpoint
/// is not an error here; `principal` reports it as an unavailable IdP.
pub def Introspector.new
    (cfg : OauthConfig) (ep : OauthEndpoints) (h : OauthHttp)
    : IO Introspector := do {
    let empty : List IntrospectEntry := List.empty;
    let cell <- Ref.new empty;
    let out : Introspector := {
        cfg := cfg,
        http := h,
        uri := ep.introspection,
        cache := cell
    };
    return out
}

// ── the public entry point ─────────────────────────────────────────────────

/// Introspect `token` at `now` (epoch seconds) and return the active
/// response's `Principal`. A cached active response is reused for at most
/// `min(60 s, exp)`; inactive, malformed, and unavailable responses are not
/// cached.
pub def Introspector.principal
    (i : Introspector) (now : I64) (token : String)
    : IO (Result AuthError Principal) := do {
    if String.is_empty token
    then return (Result.err (AuthError.auth_invalid_token "empty token"))
    else if I64.gt (String.length token) Introspect.max_token_bytes
    then return (Result.err (AuthError.auth_invalid_token "token exceeds 16 KiB"))
    else do {
        let key := Sha256.hash token;
        let found <- Introspect.lookup i.cache key now;
        match found {
            Option.some body => Introspect.from_cache i now body,
            Option.none => Introspect.fetch i now key token
        }
    }
}

def Introspect.from_cache
    (i : Introspector) (now : I64) (body : String)
    : IO (Result AuthError Principal) := do {
    match Introspect.parse_principal i now body {
        Result.err e => return (Result.err e),
        Result.ok pair =>
            match pair {
                Pair.pair principal _until => return (Result.ok principal)
            }
    }
}

// ── the request ────────────────────────────────────────────────────────────

def Introspect.base_headers : Headers :=
    Headers.set "Accept" "application/json"
        (Headers.set "Content-Type" "application/x-www-form-urlencoded" Headers.empty)

def Introspect.headers (cfg : OauthConfig) : Headers :=
    match cfg.client_auth {
        ClientAuth.client_secret_basic =>
            match cfg.client_secret {
                Option.some s =>
                    Headers.set "Authorization" (Client.basic_auth cfg.client_id s)
                        Introspect.base_headers,
                Option.none => Introspect.base_headers
            },
        _ => Introspect.base_headers
    }

def Introspect.client_pairs (cfg : OauthConfig) : List (Pair String String) :=
    match cfg.client_auth {
        ClientAuth.client_secret_basic => List.empty,
        ClientAuth.client_secret_post =>
            match cfg.client_secret {
                Option.none => [Pair.pair "client_id" cfg.client_id],
                Option.some s => [
                    Pair.pair "client_id" cfg.client_id,
                    Pair.pair "client_secret" s
                ]
            },
        ClientAuth.client_public => [Pair.pair "client_id" cfg.client_id]
    }

def Introspect.form (cfg : OauthConfig) (token : String) : String :=
    let token_pairs : List (Pair String String) := [
        Pair.pair "token" token,
        Pair.pair "token_type_hint" "access_token"
    ] in
    Form.encode (List.append token_pairs (Introspect.client_pairs cfg))

def Introspect.fetch
    (i : Introspector) (now : I64) (key : String) (token : String)
    : IO (Result AuthError Principal) := do {
    match i.uri {
        Option.none => return (Result.err AuthError.auth_temporarily_unavailable),
        Option.some u => do {
            let payload := Body.from_text (Introspect.form i.cfg token);
            let resp <- OauthHttp.send_post i.http u (Introspect.headers i.cfg) payload;
            match resp {
                Result.err _ => return (Result.err AuthError.auth_temporarily_unavailable),
                Result.ok r =>
                    if U16.beq r.status Status.ok
                    then Introspect.from_response i now key r.body
                    else return (Result.err (Introspect.status_error r.status))
            }
        }
    }
}

/// A 4xx from the introspection endpoint is this server's credentials or URL,
/// not the caller's token: report a server error, not "retry later".
def Introspect.status_error (status : U16) : AuthError :=
    if U16.beq status 400u16
        || U16.beq status 401u16
        || U16.beq status 403u16
        || U16.beq status 404u16
    then AuthError.auth_server_misconfigured
    else AuthError.auth_temporarily_unavailable

def Introspect.from_response
    (i : Introspector) (now : I64) (key : String) (body : Body)
    : IO (Result AuthError Principal) := do {
    let bytes := Body.to_bytes_pure body;
    if I64.gt (List.length bytes) Introspect.max_body_bytes
    then return (Result.err AuthError.auth_temporarily_unavailable)
    else do {
        let text := String.from_list bytes;
        match Introspect.parse_principal i now text {
            Result.err e => return (Result.err e),
            Result.ok pair =>
                match pair {
                    Pair.pair principal until =>
                        if I64.gt until now
                        then do {
                            let _ <- Introspect.store i.cache key text until now;
                            return (Result.ok principal)
                        }
                        else return (Result.ok principal)
                }
        }
    }
}

// ── cache ──────────────────────────────────────────────────────────────────

def Introspect.prune
    (entries : List IntrospectEntry) (now : I64)
    : List IntrospectEntry :=
    List.filter (fn (e : IntrospectEntry) => I64.gt e.expires_at now) entries

#[terminating]
def Introspect.find
    (entries : List IntrospectEntry) (key : String) (now : I64)
    : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            if e.key == key && I64.gt e.expires_at now
            then Option.some e.body
            else Introspect.find rest key now
    }

/// A cache hit is a pure read: an expired entry is ignored here, and the
/// write (pruning) belongs to `store`.
def Introspect.lookup
    (cell : Ref (List IntrospectEntry)) (key : String) (now : I64)
    : IO (Option String) := do {
    let entries <- Ref.get cell;
    return (Introspect.find entries key now)
}

def Introspect.without_key
    (entries : List IntrospectEntry) (key : String)
    : List IntrospectEntry :=
    List.filter (fn (e : IntrospectEntry) => Bool.not (e.key == key)) entries

#[terminating]
def Introspect.take
    (n : I64) (entries : List IntrospectEntry)
    : List IntrospectEntry :=
    if I64.lt n 1i64
    then List.empty
    else match entries {
        List.empty => List.empty,
        List.cons e rest => List.cons e (Introspect.take (I64.sub n 1i64) rest)
    }

def Introspect.store
    (cell : Ref (List IntrospectEntry)) (key : String) (body : String)
    (expires_at : I64) (now : I64)
    : IO Unit := do {
    let entry : IntrospectEntry := {
        key := key,
        body := body,
        expires_at := expires_at
    };
    let _ <- Ref.update cell (fn (entries : List IntrospectEntry) =>
        let pruned := Introspect.prune entries now in
        Introspect.take Introspect.max_cache_entries
            (List.cons entry (Introspect.without_key pruned key)));
    return unit
}

// ── response mapping ───────────────────────────────────────────────────────

def Introspect.parse_principal
    (i : Introspector) (now : I64) (body : String)
    : Result AuthError (Pair Principal I64) :=
    match Json.parse body {
        Result.err _ => Result.err AuthError.auth_temporarily_unavailable,
        Result.ok j => Introspect.parse_json i now j
    }

def Introspect.parse_json
    (i : Introspector) (now : I64) (j : Json)
    : Result AuthError (Pair Principal I64) :=
    match Json.get_object j {
        Result.err _ => Result.err AuthError.auth_temporarily_unavailable,
        Result.ok obj => Introspect.parse_obj i now obj
    }

def Introspect.parse_obj
    (i : Introspector) (now : I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Json.object_get "active" obj {
        Option.none => Result.err AuthError.auth_temporarily_unavailable,
        Option.some v => Introspect.active_value i now v obj
    }

def Introspect.active_value
    (i : Introspector) (now : I64) (v : Json) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Json.get_bool v {
        Result.err _ => Result.err AuthError.auth_temporarily_unavailable,
        Result.ok active =>
            if active
            then Introspect.principal_of i now obj
            else Result.err (AuthError.auth_invalid_token "token is not active")
    }

def Introspect.principal_of
    (i : Introspector) (now : I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.check_issuer i.cfg obj {
        Result.err e => Result.err e,
        Result.ok _ => Introspect.after_issuer i now obj
    }

def Introspect.after_issuer
    (i : Introspector) (now : I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.check_token_type obj {
        Result.err e => Result.err e,
        Result.ok _ => Introspect.after_token_type i now obj
    }

def Introspect.after_token_type
    (i : Introspector) (now : I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.subject obj {
        Result.err e => Result.err e,
        Result.ok sub => Introspect.after_subject i now sub obj
    }

def Introspect.after_subject
    (i : Introspector) (now : I64) (sub : String) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.audiences obj {
        Result.err e => Result.err e,
        Result.ok auds => Introspect.after_audiences i now sub auds obj
    }

def Introspect.after_audiences
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.check_audience i.cfg auds {
        Result.err e => Result.err e,
        Result.ok _ => Introspect.after_audience i now sub auds obj
    }

def Introspect.after_audience
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.exp_value obj {
        Result.err e => Result.err e,
        Result.ok exp => Introspect.after_exp i now sub auds exp obj
    }

def Introspect.after_exp
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.check_exp i.cfg now exp {
        Result.err e => Result.err e,
        Result.ok _ => Introspect.after_nbf i now sub auds exp obj
    }

def Introspect.after_nbf
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.nbf_value obj {
        Result.err e => Result.err e,
        Result.ok nbf => Introspect.after_nbf_value i now sub auds exp nbf obj
    }

def Introspect.after_nbf_value
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (nbf : Option I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.check_nbf i.cfg now nbf {
        Result.err e => Result.err e,
        Result.ok _ => Introspect.after_nbf_check i now sub auds exp obj
    }

def Introspect.after_nbf_check
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.scopes obj {
        Result.err e => Result.err e,
        Result.ok scopes => Introspect.after_scopes i now sub auds exp scopes obj
    }

def Introspect.after_scopes
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (scopes : List String) (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    match Introspect.roles i.cfg obj {
        Result.err e => Result.err e,
        Result.ok roles => Introspect.build i now sub auds exp scopes roles obj
    }

def Introspect.build
    (i : Introspector) (now : I64) (sub : String) (auds : List String)
    (exp : Option I64) (scopes : List String) (roles : List String)
    (obj : BTreeMap String Json)
    : Result AuthError (Pair Principal I64) :=
    let expires_at : I64 :=
        match exp {
            Option.none => I64.add now Introspect.max_ttl,
            Option.some e => e
        } in
    let p : Principal := {
        subject := sub,
        issuer := i.cfg.issuer,
        audiences := auds,
        scopes := scopes,
        roles := roles,
        claims := obj,
        expires_at := expires_at
    } in
    Result.ok (Pair.pair p (Introspect.cache_until now exp))

// ── individual fields ──────────────────────────────────────────────────────

def Introspect.check_issuer
    (cfg : OauthConfig) (obj : BTreeMap String Json)
    : Result AuthError Unit :=
    match Json.object_get "iss" obj {
        Option.none => Result.ok unit,
        Option.some v => Introspect.issuer_value cfg v
    }

def Introspect.issuer_value
    (cfg : OauthConfig) (v : Json)
    : Result AuthError Unit :=
    match Json.get_str v {
        Result.err _ => Result.err (AuthError.auth_invalid_token "iss is not a string"),
        Result.ok iss =>
            if iss == cfg.issuer
            then Result.ok unit
            else Result.err (AuthError.auth_invalid_token "issuer mismatch")
    }

/// `sub` is required: `username` is human-readable and not guaranteed
/// unique, so it must not silently become `Principal.subject`.
def Introspect.expected_audience (cfg : OauthConfig) : String :=
    match cfg.audience {
        Option.none => cfg.client_id,
        Option.some a => a
    }

/// An absent `aud` is accepted (RFC 7662 makes it optional and some
/// providers omit it); a present one must name this resource.
def Introspect.check_audience
    (cfg : OauthConfig) (auds : List String)
    : Result AuthError Unit :=
    if I64.beq (List.length auds) 0i64
    then Result.ok unit
    else if List.any (fn (a : String) => a == Introspect.expected_audience cfg) auds
    then Result.ok unit
    else Result.err (AuthError.auth_invalid_token "audience mismatch")

/// RFC 7662 lets a refresh token introspect as active, and
/// `token_type_hint` is only a hint: reject a response that says the token is
/// not a bearer token.
def Introspect.check_token_type
    (obj : BTreeMap String Json)
    : Result AuthError Unit :=
    match Json.object_get "token_type" obj {
        Option.none => Result.ok unit,
        Option.some v =>
            match Json.get_str v {
                Result.err _ => Result.err (AuthError.auth_invalid_token "invalid token_type"),
                Result.ok t =>
                    if String.to_lowercase t == "bearer"
                    then Result.ok unit
                    else Result.err (AuthError.auth_invalid_token ("unsupported token_type " ++ t))
            }
    }

def Introspect.subject
    (obj : BTreeMap String Json)
    : Result AuthError String :=
    Introspect.str_claim "sub" obj

def Introspect.str_claim
    (name : String) (obj : BTreeMap String Json)
    : Result AuthError String :=
    match Json.object_get name obj {
        Option.none => Result.err (AuthError.auth_invalid_token ("missing " ++ name)),
        Option.some v =>
            match Json.get_str v {
                Result.err _ => Result.err (AuthError.auth_invalid_token ("invalid " ++ name)),
                Result.ok s =>
                    if String.is_empty s
                    then Result.err (AuthError.auth_invalid_token ("empty " ++ name))
                    else Result.ok s
            }
    }

def Introspect.aud_value (v : Json) : Result AuthError (List String) :=
    match Json.get_str v {
        Result.ok s =>
            if String.is_empty s
            then Result.err (AuthError.auth_invalid_token "invalid aud")
            else Result.ok [s],
        Result.err _ => Introspect.aud_array v
    }

def Introspect.aud_array (v : Json) : Result AuthError (List String) :=
    match Json.get_array v {
        Result.err _ => Result.err (AuthError.auth_invalid_token "invalid aud"),
        Result.ok xs => Introspect.strings_of "aud" xs
    }

def Introspect.audiences
    (obj : BTreeMap String Json)
    : Result AuthError (List String) :=
    match Json.object_get "aud" obj {
        Option.none => Result.ok List.empty,
        Option.some v => Introspect.aud_value v
    }

#[terminating]
def Introspect.strings_go
    (name : String) (xs : List Json) (acc : List String)
    : Result AuthError (List String) :=
    match xs {
        List.empty => Result.ok (List.reverse acc),
        List.cons x rest =>
            match Json.get_str x {
                Result.err _ => Result.err (AuthError.auth_invalid_token ("invalid " ++ name)),
                Result.ok s =>
                    if String.is_empty s
                    then Result.err (AuthError.auth_invalid_token ("invalid " ++ name))
                    else Introspect.strings_go name rest (List.cons s acc)
            }
    }

def Introspect.strings_of
    (name : String) (xs : List Json)
    : Result AuthError (List String) :=
    Introspect.strings_go name xs List.empty

def Introspect.words (s : String) : List String :=
    List.filter (fn (x : String) => Bool.not (String.is_empty x))
        (Strings.split_on " " s)

def Introspect.scope_value (v : Json) : Result AuthError (List String) :=
    match Json.get_str v {
        Result.ok s => Result.ok (Introspect.words s),
        Result.err _ => Introspect.scope_array v
    }

def Introspect.scope_array (v : Json) : Result AuthError (List String) :=
    match Json.get_array v {
        Result.err _ => Result.err (AuthError.auth_invalid_token "invalid scope"),
        Result.ok xs => Introspect.strings_of "scope" xs
    }

def Introspect.scopes
    (obj : BTreeMap String Json)
    : Result AuthError (List String) :=
    match Json.object_get "scope" obj {
        Option.none => Introspect.scp obj,
        Option.some v => Introspect.scope_value v
    }

def Introspect.scp
    (obj : BTreeMap String Json)
    : Result AuthError (List String) :=
    match Json.object_get "scp" obj {
        Option.none => Result.ok List.empty,
        Option.some v => Introspect.scope_value v
    }

def Introspect.roles_value
    (name : String) (v : Json)
    : Result AuthError (List String) :=
    match Json.get_str v {
        Result.ok s => Result.ok (Introspect.words s),
        Result.err _ => Introspect.roles_array name v
    }

def Introspect.roles_array
    (name : String) (v : Json)
    : Result AuthError (List String) :=
    match Json.get_array v {
        Result.err _ => Result.err (AuthError.auth_invalid_token ("invalid " ++ name)),
        Result.ok xs => Introspect.strings_of name xs
    }

def Introspect.roles
    (cfg : OauthConfig) (obj : BTreeMap String Json)
    : Result AuthError (List String) :=
    match Json.object_get cfg.roles_claim obj {
        Option.none => Result.ok List.empty,
        Option.some v => Introspect.roles_value cfg.roles_claim v
    }

def Introspect.exp_value
    (obj : BTreeMap String Json)
    : Result AuthError (Option I64) :=
    match Json.object_get "exp" obj {
        Option.none => Result.ok Option.none,
        Option.some v => Introspect.num_value "exp" v
    }

def Introspect.nbf_value
    (obj : BTreeMap String Json)
    : Result AuthError (Option I64) :=
    match Json.object_get "nbf" obj {
        Option.none => Result.ok Option.none,
        Option.some v => Introspect.num_value "nbf" v
    }

def Introspect.num_value
    (name : String) (v : Json)
    : Result AuthError (Option I64) :=
    match Json.get_num_i64 (Json.get_num v) {
        Result.err _ => Result.err (AuthError.auth_invalid_token ("invalid " ++ name)),
        Result.ok n => Result.ok (Option.some n)
    }

def Introspect.check_exp
    (cfg : OauthConfig) (now : I64) (exp : Option I64)
    : Result AuthError Unit :=
    match exp {
        Option.none => Result.ok unit,
        Option.some e =>
            if I64.gt now (I64.add e cfg.clock_skew_seconds)
            then Result.err AuthError.auth_expired
            else Result.ok unit
    }

def Introspect.check_nbf
    (cfg : OauthConfig) (now : I64) (nbf : Option I64)
    : Result AuthError Unit :=
    match nbf {
        Option.none => Result.ok unit,
        Option.some n =>
            if I64.lt (I64.add now cfg.clock_skew_seconds) n
            then Result.err (AuthError.auth_invalid_token "token not yet valid")
            else Result.ok unit
    }

/// `min(now + 60, exp)`; a response with no `exp` is cached for 60 seconds.
def Introspect.cache_until (now : I64) (exp : Option I64) : I64 :=
    let limit := I64.add now Introspect.max_ttl in
    match exp {
        Option.none => limit,
        Option.some e => if I64.lt e limit then e else limit
    }
