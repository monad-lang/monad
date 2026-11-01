/// Redaction for logs, audit output and error messages.
///
/// The security rules name the fields that must never be logged:
/// `Authorization`, `Cookie`, `Set-Cookie`, the callback `code`/`state`/
/// `nonce`, and every token or secret. These helpers replace those values with
/// `<redacted>` while keeping the surrounding shape (header or parameter
/// names, the rest of the URL) so a log line is still useful.
///
/// Pure and deliberately conservative: an unknown name is left alone, so a
/// caller should prefer `Redact.headers`/`Redact.query` over printing raw
/// values.

use std::list {List.any, List.length}
use http::types {Headers}
use http::strings {Strings.split_at_byte}
use http::uri {Uri.format_query, Uri.parse_query}

pub def Redact.value : String := "<redacted>"

/// Lowercase header names whose values are never safe to log.
def Redact.sensitive_headers : List String := [
  "authorization",
  "proxy-authorization",
  "cookie",
  "set-cookie",
  "x-csrf-token",
  "x-api-key",
  "x-auth-token"
]

/// Query/form parameter names whose values are never safe to log.
def Redact.sensitive_params : List String := [
  "access_token",
  "refresh_token",
  "id_token",
  "id_token_hint",
  "token",
  "client_secret",
  "client_assertion",
  "assertion",
  "password",
  "code",
  "code_verifier",
  "code_challenge",
  "state",
  "nonce"
]

def Redact.header (name : String) (value : String) : Pair String String :=
  let lower := String.to_lowercase name in
  if List.any (fn (n : String) => n == lower) Redact.sensitive_headers
  then Pair.pair name Redact.value
  else Pair.pair name value

/// Every header pair, sensitive values redacted. Names keep their case.
pub def Redact.headers (h : Headers) : List (Pair String String) :=
  match h {
    Headers.headers pairs =>
      List.map
        (fn (p : Pair String String) =>
          match p {
            Pair.pair k v => Redact.header k v
          })
        pairs
  }

def Redact.param (name : String) (value : String) : Pair String String :=
  let lower := String.to_lowercase name in
  if List.any (fn (n : String) => n == lower) Redact.sensitive_params
  then Pair.pair name Redact.value
  else Pair.pair name value

/// Every query/form pair, sensitive values redacted.
pub def Redact.query
  (params : List (Pair String String))
  : List (Pair String String) :=
  List.map
    (fn (p : Pair String String) =>
      match p {
        Pair.pair k v => Redact.param k v
      })
    params

def Redact.redact_query (s : String) : String :=
  match Strings.split_at_byte 63u8 (String.to_list s) {
    Pair.pair base_b query_b =>
      if I64.beq (List.length query_b) 0i64
      then s
      else
        String.concat (String.from_list base_b)
          (String.concat "?"
            (Uri.format_query
              (Redact.query (Uri.parse_query (String.from_list query_b)))))
  }

/// A fragment is a route (kept, query redacted) or an opaque value (a
/// possible implicit-flow token), which is replaced outright.
def Redact.fragment (frag : String) : String :=
  if String.starts_with "/" frag
  then Redact.redact_query frag
  else Redact.value

/// A URL with its query and fragment redacted. The path is untouched; a
/// fragment that is a route keeps its shape, and a bare/hash-routed fragment
/// is treated as a possible token, so nothing after `#` can leak.
pub def Redact.url (s : String) : String :=
  match Strings.split_at_byte 35u8 (String.to_list s) {
    Pair.pair before_b frag_b =>
      let base := Redact.redact_query (String.from_list before_b) in
      if I64.beq (List.length frag_b) 0i64
      then base
      else
        String.concat base
          (String.concat "#" (Redact.fragment (String.from_list frag_b)))
  }
