/// `RouterT` — the transformer router, sharing matcher semantics with the
/// original `Router`.

use std::test {}
use http::types {
    Body, Headers.empty, HttpVersion, Method, Request, Request.get, Response,
    Response.ok_text, Status.method_not_allowed, Status.no_content,
    Status.not_found, Status.ok, Uri,
}
use http::body {Body.to_bytes_pure}
use moon::handler_t {
    HandlerT, HandlerT.param_io, HandlerT.pure_io, HandlerT.run_io,
    HandlerT.throw_io, HttpError, HttpError.make,
}
use moon::router {
    RouteT, RouterT.get, RouterT.post, RouterT.route, RouterT.scope,
}

def get_req (path : String) : Request :=
    Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

def method_req (method : Method) (path : String) : Request :=
    let r : Request :=
        { method := method,
            uri := Uri.uri "" Option.none "" Option.none path Option.none Option.none,
            headers := Headers.empty, version := HttpVersion.http1_1,
            body := Body.empty, params := List.empty } in
    r

def ok_handler : HandlerT IO Response :=
    HandlerT.pure_io (Response.ok_text "ok")

def other_handler : HandlerT IO Response :=
    HandlerT.pure_io (Response.ok_text "other")

def param_handler : HandlerT IO Response := do {
    let id : Option String <- HandlerT.param_io "id";
    match id {
        Option.some v => HandlerT.pure_io (Response.ok_text v),
        Option.none => HandlerT.throw_io (HttpError.make 500u16 "missing param")
    }
}

def run_route (routes : List RouteT) (req : Request) : IO (Result HttpError Response) :=
    HandlerT.run_io (RouterT.route routes) req

#[test]
def test_rt_exact_match : IO Bool := do {
    let r <- run_route [RouterT.get "/health" ok_handler] (get_req "/health");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.ok),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_param_capture : IO Bool := do {
    let r <- run_route [RouterT.get "/users/:id" param_handler] (get_req "/users/42");
    match r {
        Result.ok res =>
            IO.pure (String.beq (String.from_list (Body.to_bytes_pure res.body)) "42"),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_method_mismatch : IO Bool := do {
    let r <- run_route [RouterT.get "/x" ok_handler] (method_req Method.POST "/x");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.method_not_allowed),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_options : IO Bool := do {
    let r <- run_route [RouterT.get "/x" ok_handler] (method_req Method.OPTIONS "/x");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.no_content),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_head_falls_back_to_get : IO Bool := do {
    let r <- run_route [RouterT.get "/x" ok_handler] (method_req Method.HEAD "/x");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.ok),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_no_match : IO Bool := do {
    let r <- run_route [RouterT.get "/x" ok_handler] (get_req "/y");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.not_found),
        Result.err _ => IO.pure false
    }
}

def scoped_app : HandlerT IO Response :=
    RouterT.scope "/api" [RouterT.get "/x" ok_handler] other_handler

#[test]
def test_rt_scope_match : IO Bool := do {
    let r <- HandlerT.run_io scoped_app (get_req "/api/x");
    match r {
        Result.ok res => IO.pure (U16.beq res.status Status.ok),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_rt_scope_falls_through : IO Bool := do {
    let r <- HandlerT.run_io scoped_app (get_req "/elsewhere");
    match r {
        Result.ok res =>
            IO.pure (String.beq (String.from_list (Body.to_bytes_pure res.body)) "other"),
        Result.err _ => IO.pure false
    }
}
