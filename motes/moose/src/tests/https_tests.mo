/// moose / tests / https — HTTPS requests and the http→https redirect chain.
///
/// Two halves. The policy half is pure and always runs: the scheme-aware
/// defaults (443, and `:443` elided from the Host header) and the
/// credential rule on a scheme-crossing redirect (http→https leaves the
/// origin, so `Client.redirect_request` must not carry credentials over).
///
/// The network half is env-gated exactly like tls's `e2e_tests.mo`
/// (same env var, so one flag turns on both motes' internet-facing
/// tests): each test consults `tls_network_enabled` and passes trivially
/// when it is unset, keeping the offline sweep green. badssl.com is the
/// fixture because it is the one host whose whole purpose is speaking
/// TLS badly in every specific way; its plain-HTTP root 301s to the
/// https one, which is the plain-hop-then-secure-hop chain.

use moose::client {
  Client.get, Client.host_header_value, Client.host_port,
  Client.redirect_request,
}
use http::types {Body, Headers, HttpVersion, Method, Request, Response, Status.found, Status.ok, Uri}
use http::uri {Uri.parse}
use std::io {IO.get_env, IO.println}

// ── scheme-aware defaults (pure) ────────────────────────────────────────

/// An `https` URI with no port connects on 443.
#[test]
def test_host_port_https_default : Bool :=
  match Uri.parse "https://example.com/" {
    Result.err _ => false,
    Result.ok u =>
      let hp := Client.host_port u in
      U16.beq hp.second 443u16
  }

/// An explicit `:443` on `https` is as default as `:80` on `http`: the
/// Host header carries no port.
#[test]
def test_host_header_elides_default_https_port : Bool :=
  match Uri.parse "https://example.com:443/" {
    Result.err _ => false,
    Result.ok u => String.beq (Client.host_header_value u) "example.com"
  }

/// A non-default port still appears.
#[test]
def test_host_header_keeps_non_default_port : Bool :=
  match Uri.parse "https://example.com:8443/" {
    Result.err _ => false,
    Result.ok u => String.beq (Client.host_header_value u) "example.com:8443"
  }

// ── credentials across a scheme change (pure) ──────────────────────────
//
// `Uri.same_origin` compares schemes, so http→https is a cross-origin
// hop: the redirect policy must leave the credentials behind.

/// True when `h` carries no value under `name`.
def h_absent (name : String) (h : Headers) : Bool :=
  match Headers.get name h {
    Option.none => true,
    Option.some _ => false
  }

/// True when `h` carries exactly `want` under `name`.
def h_is (name : String) (want : String) (h : Headers) : Bool :=
  match Headers.get name h {
    Option.some v => String.beq v want,
    Option.none => false
  }

/// GET with a credential attached -- the thing a redirect must not leak.
def cred_req (u : Uri) : Request :=
  { method := Method.GET,
    uri := u,
    headers := Headers.set "Authorization" "Bearer t" Headers.empty,
    version := HttpVersion.http1_1,
    body := Body.empty }

/// A redirect that changes the scheme leaves the origin, so the
/// credential stays behind.
#[test]
def test_redirect_scheme_change_drops_credentials : Bool :=
  match Uri.parse "http://example.com/start" {
    Result.err _ => false,
    Result.ok from =>
      match Uri.parse "https://example.com/start" {
        Result.err _ => false,
        Result.ok to =>
          let r := Client.redirect_request (cred_req from) Status.found to in
          h_absent "Authorization" r.headers
      }
  }

/// The control: within one origin the credential travels.
#[test]
def test_redirect_same_origin_keeps_credentials : Bool :=
  match Uri.parse "http://example.com/start" {
    Result.err _ => false,
    Result.ok from =>
      match Uri.parse "http://example.com/other" {
        Result.err _ => false,
        Result.ok to =>
          let r := Client.redirect_request (cred_req from) Status.found to in
          h_is "Authorization" "Bearer t" r.headers
      }
  }

// ── network (env-gated; same env var as tls's e2e_tests) ────────────────

/// True when the network gate is set. Unset means "not running these".
def tls_network_enabled : IO Bool := do {
  let env <- IO.get_env "MONAD_TLS_NETWORK_TESTS";
  match env {
    Option.none => return false,
    Option.some v => return (Bool.not (String.beq v ""))
  }
}

/// badssl.com drops connections outright at a meaningful rate (curl sees
/// it too), and a drop is not a verdict — retry it, the same way tls's
/// `e2e_tests.mo` does at the handshake.
def is_transient (e : String) : Bool :=
  String.contains e "SSL_ERROR_SYSCALL" || String.contains e "tcp_connect"

#[terminating]
def get_retry (url : String) (attempts : I64) : IO (Result String Response) := do {
  let res <- Client.get url;
  match res {
    Result.ok r => return (Result.ok r),
    Result.err e =>
      if Bool.and (is_transient e) (I64.gt attempts 0)
      then get_retry url (attempts - 1)
      else return (Result.err e)
  }
}

/// One https request end to end: `Transport.secure` carries
/// `Tls.read`/`write`/`close` under Client's whole request/response
/// path, over a handshake whose chain AND hostname were verified.
#[test]
def test_https_get_badssl : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else do {
    let res <- get_retry "https://badssl.com" 5;
    match res {
      Result.err e => do { IO.println ("https_get: " ++ e); return false },
      Result.ok r => return (U16.beq r.status Status.ok)
    }
  }
}

/// The http→https redirect chain: the first hop speaks `Transport.plain`,
/// the second `Transport.secure`, and one `Client.get` does both —
/// badssl.com's plain root 301s to its https one.
#[test]
def test_http_to_https_redirect_chain : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else do {
    let res <- get_retry "http://badssl.com" 5;
    match res {
      Result.err e => do { IO.println ("redirect_chain: " ++ e); return false },
      Result.ok r => return (U16.beq r.status Status.ok)
    }
  }
}