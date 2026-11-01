// The oauth mote's library root -- bare `use oauth` resolves here.
//
// Name paths, not bare names: the declaration's own spelling is what a
// brace item matches. `OauthError` is the ONE error type of every API
// below, re-exported with its renderer; form encoding lives in
// `moose::form`, since it is an HTTP-client concern.
//
// Deliberately no `moon` and no `eclipse` here: handlers are plain
// `Request -> IO (Result String Response)` values the APPLICATION wires
// into whichever server it uses.
//
// JWT/JWKS/claims validation is `motes/jsonwebtoken`'s job, not this
// mote's. oauth exposes only the adapter (`OauthConfig.claims_config`,
// `OauthError.of_jwt`) and deliberately does not re-export its types:
// applications that validate tokens import `jsonwebtoken` directly, so
// there is exactly one JWT API.

pub use lib::redact {Redact.headers, Redact.query, Redact.url, Redact.value}
pub use lib::audit {
  Audit.allowed,
  Audit.denied,
  Audit.denied_status,
  Audit.reason_of,
  Audit.status_of,
  AuditDecision,
  AuditEvent,
  AuditEvent.render,
}
pub use lib::errors {
  AuthError,
  AuthError.to_string,
  OauthError,
  OauthError.of_jwt,
  OauthError.to_string,
}
pub use lib::config {
  ClientAuth,
  OauthConfig,
  OauthConfig.claims_config,
  OauthConfig.is_loopback_host,
  OauthConfig.scope_string,
  OauthConfig.validate,
}
pub use lib::http_client {
  OauthHttp,
  OauthHttp.fake,
  OauthHttp.real,
  OauthHttp.send_get,
  OauthHttp.send_post,
  ScriptedExchange,
}
pub use lib::pkce {Pkce.challenge, Pkce.method, Pkce.valid_verifier, Pkce.verifier}
pub use lib::token {
  OauthTokenSet,
  OauthTokenSet.is_bearer,
  OauthTokenSet.summary,
  Token.parse,
  Token.parse_json,
  Token.parse_text,
}
pub use lib::discovery {
  Discovery.discovery_url,
  Discovery.load,
  Discovery.origin,
  OauthEndpoints,
}
pub use lib::state {OauthStateStore, PendingAuth}
pub use lib::client {
  Client.authorize_url,
  Client.exchange_code,
  Client.refresh,
  Client.userinfo,
}
pub use lib::bearer {
  Bearer.require,
  BearerValidator,
  BearerValidator.introspect,
  BearerValidator.jwt,
  BearerValidator.validate_id_token,
  BearerValidator.with_audit,
}
pub use lib::session {
  AuthSession,
  OauthSessionStore,
  OauthSessionStore.check_csrf,
  OauthSessionStore.clear_cookies,
  OauthSessionStore.create,
  OauthSessionStore.csrf_cookie,
  OauthSessionStore.csrf_token,
  OauthSessionStore.destroy,
  OauthSessionStore.lookup,
  OauthSessionStore.new,
  OauthSessionStore.new_with_secret,
  OauthSessionStore.rotate,
  OauthSessionStore.rotate_with_tokens,
  OauthSessionStore.session_cookie,
  OauthSessionStore.session_name,
  OauthSessionStore.unauthorized,
  OauthSessionStore.with_session,
}
pub use lib::login {
  Login.deps,
  Login.handle_callback,
  Login.handle_login,
  Login.handle_logout,
  Login.handle_refresh,
  Login.safe_return_to,
  Login.with_userinfo,
  Login.with_audit,
  LoginDeps,
}
pub use lib::introspect {
  Introspector,
  Introspector.new,
  Introspector.principal,
}
