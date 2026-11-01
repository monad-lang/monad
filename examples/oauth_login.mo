/// A minimal browser-login application: Moon routes for `/login`, `/callback`
/// and a bearer-protected `/me`.
///
/// This is wiring, not a runnable deployment: point `issuer`/`client_id`/
/// `redirect_uri` at a real identity provider, terminate TLS at a reverse
/// proxy (Moon has no server-side TLS, and the `__Host-`/`Secure` cookies
/// need HTTPS at the edge), and run a single process -- the state and session
/// stores are in-memory, so a restart logs everyone out.
///
/// The handlers keep Moon's canonical `Request -> IO (Result String Response)`
/// type; `Login.handle_login`/`handle_callback` are wrapped by `Handler.try`
/// so an unexpected failure becomes a 500 instead of a dropped connection.

use std::io {IO.println}
use http::types {Request, Response, Status.internal_server_error, Status.ok}
use jsonwebtoken::principal {Principal}
use jsonwebtoken::verifier {JwtVerifier}
use moon::handler {Handler.try}
use moon::router {Route, Router.get, Router.route}
use moon::server {Server.run, ServerConfig.default}
use oauth::bearer {Bearer.require, BearerValidator, BearerValidator.jwt}
use oauth::config {ClientAuth, OauthConfig}
use oauth::discovery {Discovery.load}
use oauth::errors {OauthError.to_string}
use oauth::http_client {OauthHttp.real}
use oauth::login {Login.deps, Login.handle_callback, Login.handle_login}
use oauth::session {OauthSessionStore.new}
use oauth::state {OauthStateStore.new}

def config : OauthConfig := {
  issuer := "https://idp.example",
  client_id := "monad-example",
  redirect_uri := "https://app.example/callback",
  client_secret := Option.none,
  client_auth := ClientAuth.client_public,
  scopes := ["openid", "profile"],
  audience := Option.none,
  roles_claim := "roles",
  clock_skew_seconds := 60i64,
  secure_cookies := true,
  allow_insecure_localhost := false
}

def me_handler (p : Principal) (_req : Request) : IO (Result String Response) :=
  IO.pure (Result.ok (Response.text Status.ok p.subject))

def main : IO Unit := do {
  let http := OauthHttp.real;
  let ep_res <- Discovery.load http config;
  match ep_res {
    Result.err e => IO.println (OauthError.to_string e),
    Result.ok ep => do {
      let states <- OauthStateStore.new 600i64 8i64;
      let sessions_res <- OauthSessionStore.new 86400i64 3600i64 true;
      match sessions_res {
        Result.err e => IO.println (OauthError.to_string e),
        Result.ok sessions => do {
          let bearer <- BearerValidator.jwt config ep http JwtVerifier.real;
          let login := Login.deps config ep states sessions http bearer;
          let fallback : Response :=
            Response.text Status.internal_server_error "login failed";
          let routes : List Route := [
            Router.get "/login" (Handler.try fallback (Login.handle_login login)),
            Router.get "/callback" (Handler.try fallback (Login.handle_callback login)),
            Router.get "/me"
              (Handler.try fallback (Bearer.require bearer List.empty me_handler))
          ];
          let _ <- Server.run ServerConfig.default (Router.route routes);
          return unit
        }
      }
    }
  }
}
