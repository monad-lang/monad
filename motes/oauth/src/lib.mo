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

pub use lib::errors {OauthError, OauthError.to_string}
pub use lib::config {
  ClientAuth,
  OauthConfig,
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
