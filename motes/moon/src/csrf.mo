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

/// The explicit development-only secret. Never use it in a deployment:
/// every process that does not set `CSRF_SECRET` would share it.
pub def Csrf.development_secret : String := "oak-csrf-development-secret"

/// `CSRF_SECRET`, FAIL CLOSED: unset or empty is an error. New code should
/// use this rather than the historical `secret_from_env`.
pub def Csrf.secret_from_env_checked : IO (Result String String) := do {
  let v <- IO.get_env "CSRF_SECRET";
  match v {
    Option.none => IO.pure (Result.err "CSRF_SECRET is not set"),
    Option.some s =>
      if String.is_empty s
      then IO.pure (Result.err "CSRF_SECRET is empty")
      else IO.pure (Result.ok s)
  }
}

/// The historical fallback. It keeps existing programs working; a
/// deployment that uses it shares a public constant with every other such
/// deployment. Prefer `secret_from_env_checked`.
pub def Csrf.secret_from_env : IO String := do {
  let checked <- Csrf.secret_from_env_checked;
  match checked {
    Result.ok s => IO.pure s,
    Result.err _ => IO.pure Csrf.development_secret
  }
}
