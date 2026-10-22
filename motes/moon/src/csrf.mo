/// CSRF tokens bound to a session.
///
/// The token is `SHA-256(secret ++ session.id)`, compared with the
/// constant-time helper. The secret comes from `CSRF_SECRET` in production
/// (`secret_from_env`); a stable deployment secret is what makes a token
/// unforgeable. `check` reads the `csrf_token` form field produced by
/// `hidden_field`.

use std::sha256 {Sha256.hash}
use http::request {Request.param}
use http::strings {Strings.ct_eq}
use lib::session {Session}

pub def Csrf.token (secret : String) (s : Session) : String :=
  Sha256.hash (String.concat secret s.id)

pub def Csrf.verify (secret : String) (s : Session) (submitted : String) : Bool :=
  Strings.ct_eq (Csrf.token secret s) submitted

pub def Csrf.hidden_field (secret : String) (s : Session) : Pair String String :=
  Pair.pair "csrf_token" (Csrf.token secret s)

pub def Csrf.check (secret : String) (s : Session) (form : List (Pair String String)) : Bool :=
  match Request.param "csrf_token" form {
    Option.none => false,
    Option.some submitted => Csrf.verify secret s submitted
  }

/// `CSRF_SECRET`, with a deliberately obvious development fallback. A
/// deployment that does not set the variable shares the fallback with every
/// other such deployment; set it.
pub def Csrf.secret_from_env : IO String := do {
  let v <- IO.get_env "CSRF_SECRET";
  match v {
    Option.none => return "oak-csrf-development-secret",
    Option.some s => return s
  }
}
