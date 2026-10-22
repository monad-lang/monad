/// Phase 8 tests — HTTP router path matching and method dispatch.
///
/// All tests are pure (no TCP). They call `Router.route` with a request
/// and check the response status and body.

use http::types {
  GET, Headers.empty, Headers.get, Method, POST, Request, Response,
  Status.method_not_allowed, Status.no_content, Status.not_found,
  Status.ok, empty, http1_1, uri,
}
use moon::router {
  Router.get, Router.head, Router.mount, Router.param, Router.post, Router.route,
}
use http::body {Body.to_bytes_pure}
use http::strings {}

// ── test infrastructure ─────────────────────────────────────────────────

/// Build a request with a given method and path.
def mk_req (method : Method) (path : String) : Request :=
  { method := method, uri := Uri.uri "" Option.none "" Option.none path Option.none Option.none, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// Check a response: status matches and body text matches.
def resp_ok (res : Response) (want_status : U16) (want_body : String) : Bool :=
  Bool.and (U16.beq res.status want_status) (String.beq (String.from_list (Body.to_bytes_pure res.body)) want_body)

/// Handler that echoes the captured param value.
def echo_param_handler (req : Request) : IO Response :=
  match Router.param "id" req {
    Option.some v => return (Response.ok_text v),
    Option.none => return (Response.ok_text "no-param")
  }

/// Handler that returns 200 "ok".
def ok_handler (_ : Request) : IO Response :=
  return (Response.ok_text "ok")

/// Handler that returns 200 "users".
def users_handler (_ : Request) : IO Response :=
  return (Response.ok_text "users")

// ── tests ──────────────────────────────────────────────────────────────

/// Exact match: GET /health → 200.
#[test]
def test_route_exact_match : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/health");
  return (resp_ok res Status.ok "ok")
}

/// Param capture: GET /users/42 → 200 "42".
#[test]
def test_route_param_capture : IO Bool := do {
  let routes := List.cons (Router.get "/users/:id" echo_param_handler) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/users/42");
  return (resp_ok res Status.ok "42")
}

/// Method mismatch: POST /health when only GET registered → 405 + Allow.
#[test]
def test_route_method_mismatch : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.POST "/health");
  let allow := match Headers.get "Allow" res.headers {
    Option.some v => v,
    Option.none => ""
  };
  return (Bool.and (U16.beq res.status Status.method_not_allowed) (String.beq allow "GET, HEAD"))
}

/// OPTIONS on a known path → 204 with Allow.
#[test]
def test_route_options_returns_allow : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.OPTIONS "/health");
  let allow := match Headers.get "Allow" res.headers {
    Option.some v => v,
    Option.none => ""
  };
  return (Bool.and (U16.beq res.status Status.no_content) (String.beq allow "GET, HEAD"))
}

/// HEAD falls back to the GET route (the server suppresses the body).
#[test]
def test_route_head_falls_back_to_get : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.HEAD "/health");
  return (resp_ok res Status.ok "ok")
}

/// A path parameter is percent-decoded after the split.
#[test]
def test_route_param_percent_decoded : IO Bool := do {
  let routes := List.cons (Router.get "/users/:id" echo_param_handler) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/users/a%20b");
  return (resp_ok res Status.ok "a b")
}

/// No match: GET /unknown → 404.
#[test]
def test_route_no_match : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/unknown");
  return (resp_ok res Status.not_found "Not Found")
}

/// Multiple routes: first match wins.
#[test]
def test_route_first_match : IO Bool := do {
  let routes := List.cons (Router.get "/health" ok_handler) (List.cons (Router.get "/users" users_handler) List.empty);
  let res <- Router.route routes (mk_req Method.GET "/health");
  return (resp_ok res Status.ok "ok")
}

/// Multiple params: GET /users/42/posts/7 → 200 "42:7".
#[test]
def test_route_multi_params : IO Bool := do {
  let routes := List.cons (Router.get "/users/:id/posts/:pid" (fn req => do {
    let uid := match Router.param "id" req { Option.some v => v, Option.none => "?" };
    let pid := match Router.param "pid" req { Option.some v => v, Option.none => "?" };
    return (Response.ok_text (String.concat (String.concat uid ":") pid))
  })) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/users/42/posts/7");
  return (resp_ok res Status.ok "42:7")
}

/// Wildcard match: GET /assets/* → 200.
#[test]
def test_route_wildcard : IO Bool := do {
  let routes := List.cons (Router.get "/assets/*" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/assets/css/main.css");
  return (resp_ok res Status.ok "ok")
}

/// POST route matches POST method.
#[test]
def test_route_post : IO Bool := do {
  let routes := List.cons (Router.post "/submit" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.POST "/submit");
  return (resp_ok res Status.ok "ok")
}

/// Sub-router: mount at /api, strip prefix, dispatch to sub-routes.
#[test]
def test_route_mount : IO Bool := do {
  let sub_routes := List.cons (Router.get "/status" ok_handler) List.empty;
  let routes := List.cons (Router.get "/api/*" (fn req => Router.mount "/api" sub_routes req)) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/api/status");
  return (resp_ok res Status.ok "ok")
}

/// Mounting at `/api` also serves the bare prefix: the sub-router's `/`
/// route answers `/api` itself.
#[test]
def test_route_mount_bare_prefix : IO Bool := do {
  let sub_routes := List.cons (Router.get "/" ok_handler) List.empty;
  let routes := List.cons (Router.get "/api/*" (fn req => Router.mount "/api" sub_routes req)) List.empty;
  let res <- Router.route routes (mk_req Method.GET "/api");
  return (resp_ok res Status.ok "ok")
}

/// An explicit HEAD route wins even when the GET route is declared first.
#[test]
def test_explicit_head_beats_get : IO Bool := do {
  let routes := [
    Router.get "/x" ok_handler,
    Router.head "/x" (fn (_ : Request) => IO.pure (Response.ok_text "head"))
  ];
  let res <- Router.route routes (mk_req Method.HEAD "/x");
  return (resp_ok res Status.ok "head")
}

/// HEAD still falls back to GET when no explicit HEAD route exists.
#[test]
def test_head_falls_back_to_get : IO Bool := do {
  let routes := List.cons (Router.get "/x" ok_handler) List.empty;
  let res <- Router.route routes (mk_req Method.HEAD "/x");
  return (resp_ok res Status.ok "ok")
}
