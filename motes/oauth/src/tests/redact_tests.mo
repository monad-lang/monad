/// Redaction tests: known secrets must not survive a redacted header, query
/// or URL. Pure, so both hosts run them.

use std::list {List.any}
use http::types {Headers.empty, Headers.set}
use oauth::redact {Redact.headers, Redact.query, Redact.url, Redact.value}

def has_value (pairs : List (Pair String String)) (name : String) (value : String) : Bool :=
    List.any
        (fn (p : Pair String String) =>
            match p {
                Pair.pair k v => k == name && v == value
            })
        pairs

def contains (haystack : String) (needle : String) : Bool :=
    String.contains haystack needle

#[test]
def test_redact_headers : Bool :=
    let h := Headers.set "Accept" "application/json"
        (Headers.set "Authorization" "Bearer super-secret" Headers.empty) in
    let pairs := Redact.headers h in
    has_value pairs "accept" "application/json"
        && has_value pairs "authorization" Redact.value
        && Bool.not (contains (String.concat_all
            (List.map (fn (p : Pair String String) => match p { Pair.pair _ v => v }) pairs))
            "super-secret")

#[test]
def test_redact_query : Bool :=
    let pairs := Redact.query [
        Pair.pair "code" "auth-code",
        Pair.pair "state" "state-value",
        Pair.pair "scope" "read write"
    ] in
    has_value pairs "code" Redact.value
        && has_value pairs "state" Redact.value
        && has_value pairs "scope" "read write"
        && Bool.not (contains (String.concat_all
            (List.map (fn (p : Pair String String) => match p { Pair.pair _ v => v }) pairs))
            "auth-code")

#[test]
def test_redact_url : Bool :=
    let out := Redact.url "https://app.example/callback?code=auth-code&state=state-value&scope=read" in
    contains out "https://app.example/callback?"
        && contains out "scope=read"
        && Bool.not (contains out "auth-code")
        && Bool.not (contains out "state-value")

#[test]
def test_redact_url_without_query : Bool :=
    Redact.url "https://app.example/login" == "https://app.example/login"

#[test]
def test_redact_is_case_insensitive : Bool :=
    has_value (Redact.headers
        (Headers.set "Cookie" "session=id" Headers.empty)) "cookie" Redact.value
        && has_value (Redact.query [Pair.pair "Access_Token" "tok"]) "Access_Token" Redact.value

#[test]
def test_redact_url_fragment_token : Bool :=
    let out := Redact.url "https://app.example/cb?code=auth-code#access_token=hidden&state=st" in
    Bool.not (contains out "auth-code")
        && Bool.not (contains out "hidden")
        && Bool.not (contains out "state=st")
        && contains out "#<redacted>"

#[test]
def test_redact_url_hash_route : Bool :=
    let out := Redact.url "https://app.example/cb#/route?code=SECRET&state=st" in
    Bool.not (contains out "SECRET")
        && Bool.not (contains out "state=st")
        && contains out "#/route?code=%3Credacted%3E"

#[test]
def test_redact_url_route_fragment_kept : Bool :=
    Redact.url "https://app.example/docs#/section" == "https://app.example/docs#/section"

#[test]
def test_redact_url_bare_fragment_redacted : Bool :=
    Redact.url "https://app.example/docs#section" == "https://app.example/docs#<redacted>"
