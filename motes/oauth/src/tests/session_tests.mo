/// Session-store tests: cookies, CSRF, idle/absolute TTL, rotation, destroy,
/// and the 401 path. No RNG and no network: `new_with_secret` and
/// `create_with_id` are the deterministic seams, so both hosts run these.

use std::list {List.all}
use std::map {BTreeMap}
use http::types {
    Headers.empty, Headers.get, Headers.get_all, Headers.set, Request, Request.get, Response, Response.text,
    Status.ok, Status.unauthorized, Uri,
}
use json::json {Json}
use jsonwebtoken::principal {Principal}
use oauth::session {
    AuthSession, OauthSessionStore, OauthSessionStore.check_csrf,
    OauthSessionStore.create_with_id, OauthSessionStore.csrf_cookie,
    OauthSessionStore.csrf_token, OauthSessionStore.destroy,
    OauthSessionStore.lookup, OauthSessionStore.new_with_secret,
    OauthSessionStore.rotate_with_id, OauthSessionStore.session_cookie,
    OauthSessionStore.session_name, OauthSessionStore.with_session,
}
use oauth::token {OauthTokenSet}

def secret : String := "0123456789abcdef0123456789abcdef"

def store_secure : IO OauthSessionStore :=
    OauthSessionStore.new_with_secret secret 3600i64 600i64 true

def store_plain : IO OauthSessionStore :=
    OauthSessionStore.new_with_secret secret 3600i64 600i64 false

def principal_of (subject : String) : Principal :=
    let claims : BTreeMap String Json := BTreeMap.empty in
    let p : Principal := {
        subject := subject,
        issuer := "https://idp.example",
        audiences := ["api://x"],
        scopes := ["read"],
        roles := List.empty,
        claims := claims,
        expires_at := 3000i64
    } in
    p

def tokens_of (refresh : Option String) : OauthTokenSet :=
    let t : OauthTokenSet := {
        access_token := "access",
        token_type := "Bearer",
        expires_in := Option.some 300i64,
        refresh_token := refresh,
        id_token := Option.none,
        scope := ["read"]
    } in
    t

def create_at (st : OauthSessionStore) (id : String) (now : I64) : IO AuthSession :=
    OauthSessionStore.create_with_id st id (principal_of "u1")
        (tokens_of (Option.some "refresh")) now

def api_uri : Uri :=
    Uri.uri "https" Option.none "api.example" Option.none "/me" Option.none Option.none

def request_cookie (value : String) : Request :=
    let base := Request.get api_uri in
    let out : Request := {
        base with headers := Headers.set "Cookie" value Headers.empty
    } in
    out

def request_session (st : OauthSessionStore) (s : AuthSession) : Request :=
    request_cookie
        (OauthSessionStore.session_name st ++ "=" ++ s.id)

def request_csrf
    (st : OauthSessionStore) (s : AuthSession) (token : String)
    : Request :=
    let base := request_session st s in
    let out : Request := {
        base with headers := Headers.set "X-CSRF-Token" token base.headers
    } in
    out

def cookie_value (p : Pair String String) : String :=
    match p {
        Pair.pair _ v => v
    }

def contains (haystack : String) (needle : String) : Bool :=
    String.contains haystack needle

def handler : AuthSession -> Request -> IO (Result String Response) :=
    fn (s : AuthSession) (_req : Request) =>
        IO.pure (Result.ok (Response.text Status.ok s.subject))

// ── cookie attributes ──────────────────────────────────────────────────────

#[test]
def test_session_cookie_secure : IO Bool := do {
    let st <- store_secure;
    let s <- create_at st "id1" 1000i64;
    let session := cookie_value (OauthSessionStore.session_cookie st s);
    let csrf := cookie_value (OauthSessionStore.csrf_cookie st s);
    return
        (contains session "__Host-oauth_session=id1"
            && contains session "Path=/"
            && contains session "HttpOnly"
            && contains session "Secure"
            && contains session "SameSite=Lax"
            && Bool.not (contains session "Domain")
            && contains csrf "__Host-oauth_csrf="
            && Bool.not (contains csrf "HttpOnly"))
}

#[test]
def test_session_cookie_insecure : IO Bool := do {
    let st <- store_plain;
    let s <- create_at st "id1" 1000i64;
    let session := cookie_value (OauthSessionStore.session_cookie st s);
    return
        (contains session "oauth_session=id1"
            && Bool.not (contains session "__Host-")
            && Bool.not (contains session "Secure"))
}

// ── lookup and TTL ─────────────────────────────────────────────────────────

#[test]
def test_session_lookup : IO Bool := do {
    let st <- store_secure;
    let s <- create_at st "id1" 1000i64;
    let found <- OauthSessionStore.lookup st (request_session st s) 1001i64;
    return (match found {
        Option.none => false,
        Option.some live => live.subject == "u1" && live.id == "id1"
    })
}

#[test]
def test_session_unknown_id_rejected : IO Bool := do {
    let st <- store_secure;
    let _ <- create_at st "id1" 1000i64;
    let found <- OauthSessionStore.lookup st
        (request_cookie (OauthSessionStore.session_name st ++ "=not-the-id")) 1001i64;
    return (match found { Option.none => true, Option.some _ => false })
}

#[test]
def test_session_duplicate_cookie_rejected : IO Bool := do {
    let st <- store_plain;
    let s <- create_at st "id1" 1000i64;
    let found <- OauthSessionStore.lookup st
        (request_cookie (OauthSessionStore.session_name st ++ "=id1; oauth_session=id1"))
        1001i64;
    return (match found { Option.none => true, Option.some _ => false })
}

#[test]
def test_session_absolute_ttl : IO Bool := do {
    let st <- OauthSessionStore.new_with_secret secret 100i64 1000i64 false;
    let s <- create_at st "id1" 1000i64;
    let found <- OauthSessionStore.lookup st (request_session st s) 1101i64;
    return (match found { Option.none => true, Option.some _ => false })
}

#[test]
def test_session_idle_ttl : IO Bool := do {
    let st <- OauthSessionStore.new_with_secret secret 1000i64 10i64 false;
    let s <- create_at st "id1" 1000i64;
    let first <- OauthSessionStore.lookup st (request_session st s) 1005i64;
    let second <- OauthSessionStore.lookup st (request_session st s) 1016i64;
    return (match first {
        Option.none => false,
        Option.some _ => match second { Option.none => true, Option.some _ => false }
    })
}

// ── rotation, destroy, 401 ─────────────────────────────────────────────────

#[test]
def test_session_rotate_changes_id : IO Bool := do {
    let st <- store_secure;
    let s <- create_at st "old" 1000i64;
    let rotated <- OauthSessionStore.rotate_with_id st s "new-id" 1005i64;
    let old <- OauthSessionStore.lookup st (request_session st s) 1006i64;
    let new <- OauthSessionStore.lookup st (request_session st rotated) 1006i64;
    return (Bool.not (rotated.id == s.id)
        && (match old { Option.none => true, Option.some _ => false })
        && (match new { Option.some live => live.subject == "u1", Option.none => false }))
}

#[test]
def test_session_destroy : IO Bool := do {
    let st <- store_secure;
    let s <- create_at st "id1" 1000i64;
    let _ <- OauthSessionStore.destroy st (request_session st s);
    let found <- OauthSessionStore.lookup st (request_session st s) 1001i64;
    return (match found { Option.none => true, Option.some _ => false })
}

#[test]
def test_with_session_401_clears_cookies : IO Bool := do {
    let st <- store_secure;
    let r <- OauthSessionStore.with_session st handler (Request.get api_uri);
    match r {
        Result.err _ => return false,
        Result.ok res => do {
            let cookies := Headers.get_all "Set-Cookie" res.headers;
            let cache := Headers.get "Cache-Control" res.headers;
            return (U16.beq res.status Status.unauthorized
                && I64.beq (List.length cookies) 2i64
                && List.all (fn (c : String) => String.contains c "Max-Age=0") cookies
                && (match cache { Option.some v => v == "no-store", Option.none => false }))
        }
    }
}

// ── CSRF ───────────────────────────────────────────────────────────────────

#[test]
def test_csrf_round_trip : IO Bool := do {
    let st <- store_secure;
    let s <- create_at st "id1" 1000i64;
    let token := OauthSessionStore.csrf_token st s;
    return (OauthSessionStore.check_csrf st s (request_csrf st s token)
        && Bool.not (OauthSessionStore.check_csrf st s (request_csrf st s "wrong"))
        && Bool.not (OauthSessionStore.check_csrf st s (request_session st s)))
}

#[test]
def test_csrf_cookie_carries_the_token : IO Bool := do {
    let st <- store_plain;
    let s <- create_at st "id1" 1000i64;
    let token := OauthSessionStore.csrf_token st s;
    let csrf := cookie_value (OauthSessionStore.csrf_cookie st s);
    return (String.contains csrf ("oauth_csrf=" ++ token))
}
