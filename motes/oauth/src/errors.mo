/// The oauth mote's error type.
///
/// One variant per failure the client can report, so a caller can branch on
/// the reason; `OauthError.to_string` is the ONE render point, and its text
/// is what the earlier per-message constructors produced. No message
/// interpolates a token, code, state, verifier, client secret, or response
/// body — the payloads are configuration field names, status codes, and the
/// transport's own failure text.

use jsonwebtoken::errors {JwtError, JwtError.to_string}

pub type OauthError {
  // ── configuration ─────────────────────────────────────────────────────
  config_client_id_empty,
  config_skew_negative,
  config_invalid_uri (what : String),
  config_insecure_uri (what : String),
  config_secret_required,

  // ── discovery ─────────────────────────────────────────────────────────
  discovery_url_invalid,
  discovery_request_failed,
  discovery_status (status : U16),
  discovery_redirect,
  discovery_invalid_json,
  discovery_issuer_mismatch,
  discovery_missing (field : String),
  discovery_invalid (field : String),
  discovery_insecure (field : String),
  discovery_cross_origin (field : String),

  // ── token endpoint ────────────────────────────────────────────────────
  token_request_failed (msg : String),
  token_status (status : U16),
  token_invalid_json,
  token_missing_access_token,
  token_missing_token_type,
  token_bad_token_type (t : String),
  token_invalid_field (field : String),

  // ── userinfo ──────────────────────────────────────────────────────────
  userinfo_not_configured,
  userinfo_request_failed,
  userinfo_status (status : U16),
  userinfo_invalid_json,

  // ── state store and transports ────────────────────────────────────────
  state_too_many_pending,
  rng_failed,
  fake_no_response (path : String),

  /// The ONE boundary wrap: an HTTP client (moose) failure, text verbatim.
  /// The transport does not know which flow it serves, so the caller either
  /// discards it or renders it into its own message.
  transport (detail : String),

  /// The ONE JWT boundary wrap: a `jsonwebtoken` rejection, text verbatim.
  /// `jsonwebtoken` owns the structured error; oauth renders it at the
  /// point where a flow reports it.
  jwt (detail : String)
}

pub def OauthError.to_string (e : OauthError) : String :=
  match e {
    OauthError.config_client_id_empty => "config: client_id is empty",
    OauthError.config_skew_negative => "config: clock_skew_seconds is negative",
    OauthError.config_invalid_uri what => String.concat "config: invalid " what,
    OauthError.config_insecure_uri what =>
      String.concat "config: " (String.concat what " must use https"),
    OauthError.config_secret_required =>
      "config: client_secret is required for confidential clients",

    OauthError.discovery_url_invalid => "discovery: invalid discovery URL",
    OauthError.discovery_request_failed => "discovery: request failed",
    OauthError.discovery_status status =>
      String.concat "discovery: status " (U16.to_string status),
    OauthError.discovery_redirect => "discovery: redirect not followed",
    OauthError.discovery_invalid_json => "discovery: invalid JSON",
    OauthError.discovery_issuer_mismatch => "discovery: issuer mismatch",
    OauthError.discovery_missing field => String.concat "discovery: missing " field,
    OauthError.discovery_invalid field => String.concat "discovery: invalid " field,
    OauthError.discovery_insecure field =>
      String.concat "discovery: insecure " field,
    OauthError.discovery_cross_origin field =>
      String.concat "discovery: cross-origin " field,

    OauthError.token_request_failed msg =>
      String.concat "token: request failed: " msg,
    OauthError.token_status status =>
      String.concat "token: status " (U16.to_string status),
    OauthError.token_invalid_json => "token: invalid JSON",
    OauthError.token_missing_access_token => "token: missing access_token",
    OauthError.token_missing_token_type => "token: missing token_type",
    OauthError.token_bad_token_type t =>
      String.concat "token: unsupported token_type " t,
    OauthError.token_invalid_field field => String.concat "token: invalid " field,

    OauthError.userinfo_not_configured => "userinfo: not configured",
    OauthError.userinfo_request_failed => "userinfo: request failed",
    OauthError.userinfo_status status =>
      String.concat "userinfo: status " (U16.to_string status),
    OauthError.userinfo_invalid_json => "userinfo: invalid JSON",

    OauthError.state_too_many_pending =>
      "state: too many pending authorizations",
    OauthError.rng_failed => "state: random generator failed",
    OauthError.fake_no_response path =>
      String.concat "fake: no scripted response for " path,

    OauthError.transport detail => detail,

    OauthError.jwt detail => detail
  }

/// The boundary conversion: one place where a `jsonwebtoken` rejection
/// becomes an `OauthError`. The rendered text is the JWT error's own.
pub def OauthError.of_jwt (e : JwtError) : OauthError :=
  OauthError.jwt (JwtError.to_string e)
