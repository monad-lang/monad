# oauth

OAuth 2.1 / OpenID Connect for Monad, in two roles:

- **Client + relying party** — authorization code with PKCE S256, discovery,
  token exchange/refresh, userinfo, and login/callback/refresh/logout
  handlers.
- **Resource server** — bearer-JWT validation (JWKS) or RFC 7662
  introspection, with RFC 6750 401/403/503 responses.

The mote has no Moon dependency: every handler is a plain
`Request -> IO (Result String Response)`, so it wires into Moon (or any
server) without this mote importing it. JWT/JWKS/claim validation lives in
[`motes/jsonwebtoken`](../jsonwebtoken), and the OpenSSL primitives live in
[`motes/crypto`](../crypto).

## Wiring

```text
http   := oauth::http_client::OauthHttp.real
ep     := oauth::discovery::Discovery.load http cfg        // validates HTTPS,
                                                          // issuer, same-origin
states := oauth::state::OauthStateStore.new 600 8
sess   := oauth::session::OauthSessionStore.new 86400 3600 true
bearer := oauth::bearer::BearerValidator.jwt cfg ep http JwtVerifier.real
login  := oauth::login::Login.deps cfg ep states sess http bearer

routes := [
  Router.get "/login"    (Handler.try fallback (Login.handle_login login)),
  Router.get "/callback" (Handler.try fallback (Login.handle_callback login)),
  Router.get "/api/me"   (Handler.try fallback (Bearer.require bearer [] me))
]
```

See [`examples/oauth_login.mo`](../../examples/oauth_login.mo) for the
compiling version. `Login.with_userinfo` additionally requires the userinfo
`sub` to equal the ID token's; `BearerValidator.introspect` selects opaque-token
mode instead of JWKS.

## Security model (and what you must provide)

- **TLS.** Moon has no server-side TLS. Terminate HTTPS at a reverse proxy;
  `Secure` and `__Host-` cookies require HTTPS at the edge.
- **Single process.** The state store, session store, JWKS cache and
  introspection cache are in-memory. A restart logs everyone out. A
  multi-process deployment needs a shared store (Redis or similar) and a
  shared CSRF secret (`OauthSessionStore.new_with_secret`, at least 32 bytes);
  the default `new` generates a process-local CSPRNG secret. The session table
  is a list capped at 1024 entries, so its lookup is O(sessions).
- **One issuer per configuration.** Multi-tenant issuer routing is future
  work.
- **Tokens stay server-side.** The session cookie carries a CSPRNG id; the
  CSRF cookie carries `base64url(HMAC-SHA256(secret, session.id))`. Access,
  refresh and ID tokens, the callback `code`, and `state` never appear in
  cookies or URLs after the callback.
- **Cookies.** The session and `oauth_state` cookies are `HttpOnly`; the CSRF
  cookie is deliberately readable (not `HttpOnly`) so the page can send
  `X-CSRF-Token`. All are `SameSite=Lax`, `Path=/`, no `Domain`; `__Host-`
  names and `Secure` when `secure_cookies` is set. `SameSite=Lax` is required
  for the OIDC callback redirect.
- **CSRF.** Refresh and logout require `X-CSRF-Token` equal to the derived
  token, compared with `Ct.eq`. Login CSRF is blocked by an HttpOnly
  `oauth_state` cookie set at `/login` and required at `/callback`.
- **Return targets.** `return_to` must be a relative path (`/...`, not
  `//...`) or a same-origin absolute URL (compared against the configured
  `redirect_uri`); control characters are rejected. Anything else becomes `/`.
- **Logging.** Never log raw headers or query strings. `Redact.headers`,
  `Redact.query` and `Redact.url` replace `Authorization`, `Cookie`,
  `Set-Cookie`, `code`, `state`, `nonce` and every token/secret with
  `<redacted>`; URL query values are percent-encoded, so a redacted one reads
  `%3Credacted%3E`, a bare fragment becomes `#<redacted>`, and a hash route
  keeps its path with its query redacted. `AuditEvent.render` emits only the
  decision, status, subject, issuer and a short reason code, quoting fields
  and dropping control/non-ASCII bytes; attach a hook with
  `BearerValidator.with_audit` and `Login.with_audit`.
- **Errors.** Public bodies carry only an error code; detailed reasons belong
  in audit output. Every authentication response is `Cache-Control: no-store`
  and `Referrer-Policy: no-referrer`.

## Tests

```bash
monad test motes/oauth
MONAD_OAUTH_FFI_TESTS=1 <compiled-monad> test motes/oauth
```

The suite runs against a scripted fake IdP (`OauthHttp.fake`) and a fake
verifier, so there is no socket and no network; the RNG/OpenSSL-backed paths
are gated on the compiled backend.
