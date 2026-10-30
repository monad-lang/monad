/// `MiddlewareT` — transformer middleware over `HandlerT IO Response`.

use std::test {}
use http::types {
  Body, Headers, Headers.add, Headers.empty, Headers.get, HttpVersion, Method,
  Request, Request.get, Response, Response.ok_text, Response.text,
  Response.with_header, Status.forbidden, Status.no_content, Status.ok,
  Status.unauthorized, Uri,
}
use http::body {Body.to_bytes_pure}
use moon::handler_t {
  HandlerT, HandlerT.pure_io, HandlerT.run_io, HandlerT.throw_io,
  HttpError, HttpError.make,
}
use moon::middleware_t {
  CorsConfig, CorsConfig.allow_origin, CorsConfig.default,
  MiddlewareT.auth_basic_ct, MiddlewareT.auth_bearer_ct, MiddlewareT.content_type,
  MiddlewareT.cors, MiddlewareT.cors_with, MiddlewareT.map_response,
  MiddlewareT.recover,
}

def get_req (path : String) : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

def with_header (name : String) (value : String) (req : Request) : Request :=
  match req {
    { method, uri, headers, version, body, params } =>
      let req2 : Request :=
        { method := method, uri := uri,
          headers := Headers.add name value headers,
          version := version, body := body, params := params } in
      req2
  }

def ok_handler : HandlerT IO Response :=
  HandlerT.pure_io (Response.ok_text "ok")

def text_handler : HandlerT IO Response :=
  HandlerT.pure_io (Response.text 200u16 "hi")

def failing : HandlerT IO Response :=
  HandlerT.throw_io (HttpError.make 500u16 "boom")

def header_adder (res : Response) : Response :=
  Response.with_header "X-Test" "1" res

#[test]
def test_mt_map_response : IO Bool := do {
  let h := MiddlewareT.map_response header_adder ok_handler;
  let r <- HandlerT.run_io h (get_req "/");
  match r {
    Result.ok res =>
      IO.pure (match Headers.get "X-Test" res.headers {
        Option.some v => String.beq v "1",
        Option.none => false
      }),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_content_type : IO Bool := do {
  let h := MiddlewareT.content_type text_handler;
  let r <- HandlerT.run_io h (get_req "/");
  match r {
    Result.ok res =>
      IO.pure (match Headers.get "Content-Type" res.headers {
        Option.some v => String.beq v "text/plain; charset=utf-8",
        Option.none => false
      }),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_cors : IO Bool := do {
  let h := MiddlewareT.cors ok_handler;
  let r <- HandlerT.run_io h (get_req "/");
  match r {
    Result.ok res =>
      IO.pure (match Headers.get "Access-Control-Allow-Origin" res.headers {
        Option.some v => String.beq v "*",
        Option.none => false
      }),
    Result.err _ => IO.pure false
  }
}

def error_page (e : HttpError) : Response :=
  match e {
    { status, detail, .. } => Response.text status detail
  }

#[test]
def test_mt_recover : IO Bool := do {
  let h := MiddlewareT.recover error_page failing;
  let r <- HandlerT.run_io h (get_req "/");
  match r {
    Result.ok res =>
      IO.pure (Bool.and (U16.beq res.status 500u16)
        (String.beq (String.from_list (Body.to_bytes_pure res.body)) "boom")),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_auth_bearer_valid : IO Bool := do {
  let h := MiddlewareT.auth_bearer_ct "secret" ok_handler;
  let r <- HandlerT.run_io h (with_header "Authorization" "Bearer secret" (get_req "/"));
  match r {
    Result.ok res => IO.pure (U16.beq res.status Status.ok),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_auth_bearer_invalid : IO Bool := do {
  let h := MiddlewareT.auth_bearer_ct "secret" ok_handler;
  let r <- HandlerT.run_io h (with_header "Authorization" "Bearer nope" (get_req "/"));
  match r {
    Result.ok res => IO.pure (U16.beq res.status Status.unauthorized),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_auth_basic_valid : IO Bool := do {
  let h := MiddlewareT.auth_basic_ct "user:pass" ok_handler;
  let r <- HandlerT.run_io h (with_header "Authorization" "Basic dXNlcjpwYXNz" (get_req "/"));
  match r {
    Result.ok res => IO.pure (U16.beq res.status Status.ok),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_auth_basic_invalid : IO Bool := do {
  let h := MiddlewareT.auth_basic_ct "user:pass" ok_handler;
  let r <- HandlerT.run_io h (with_header "Authorization" "Basic bm9wZQ==" (get_req "/"));
  match r {
    Result.ok res => IO.pure (U16.beq res.status Status.forbidden),
    Result.err _ => IO.pure false
  }
}

// ── configurable CORS ───────────────────────────────────────────────────

def method_req (method : Method) (path : String) : Request :=
  let r : Request :=
    { method := method,
      uri := Uri.uri "" Option.none "" Option.none path Option.none Option.none,
      headers := Headers.empty, version := HttpVersion.http1_1,
      body := Body.empty, params := List.empty } in
  r

def app_cors : CorsConfig :=
  CorsConfig.allow_origin "https://app.example" CorsConfig.default

#[test]
def test_mt_cors_with_allowed_origin : IO Bool := do {
  let h := MiddlewareT.cors_with app_cors ok_handler;
  let req := with_header "Origin" "https://app.example" (get_req "/");
  let r <- HandlerT.run_io h req;
  match r {
    Result.ok res =>
      IO.pure (Bool.and
        (match Headers.get "Access-Control-Allow-Origin" res.headers {
          Option.some v => String.beq v "https://app.example",
          Option.none => false
        })
        (match Headers.get "Vary" res.headers {
          Option.some v => String.contains v "Origin",
          Option.none => false
        })),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_cors_with_rejects_unknown_origin : IO Bool := do {
  let h := MiddlewareT.cors_with app_cors ok_handler;
  let req := with_header "Origin" "https://evil.example" (get_req "/");
  let r <- HandlerT.run_io h req;
  match r {
    Result.ok res =>
      IO.pure (match Headers.get "Access-Control-Allow-Origin" res.headers {
        Option.some _ => false,
        Option.none => true
      }),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_mt_cors_with_preflight : IO Bool := do {
  let h := MiddlewareT.cors_with app_cors ok_handler;
  let req := with_header "Access-Control-Request-Method" "POST"
    (with_header "Origin" "https://app.example" (method_req Method.OPTIONS "/"));
  let r <- HandlerT.run_io h req;
  match r {
    Result.ok res =>
      IO.pure (Bool.and (U16.beq res.status Status.no_content)
        (match Headers.get "Access-Control-Allow-Methods" res.headers {
          Option.some v => String.contains v "POST",
          Option.none => false
        })),
    Result.err _ => IO.pure false
  }
}
