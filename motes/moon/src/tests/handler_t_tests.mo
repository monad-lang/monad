/// `HandlerT` — the transformer handler API.
///
/// These run compiled (`monad test motes/moon`), which is the point: a
/// missing dictionary or a constrained call inside a lambda is invisible to
/// `check` and shows up here as a wrong answer or a crash.

use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new}
use std::test {}
use http::types {Request, Request.get, Response, Uri}
use moon::handler_t {
    HandlerT, HandlerT.catch_io, HandlerT.lift_io, HandlerT.map_error_io,
    HandlerT.param_io, HandlerT.path_io, HandlerT.pure_io, HandlerT.run_io,
    HandlerT.throw_io, HandlerT.to_old, HandlerT.with_route,
    HttpError, HttpError.make,
}

def get_req (path : String) : Request :=
    Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

// ── core monad ──────────────────────────────────────────────────────────

#[test]
def test_pure_run : IO Bool := do {
    let r <- HandlerT.run_io (HandlerT.pure_io 42i64) (get_req "/");
    match r {
        Result.ok v => IO.pure (I64.beq v 42i64),
        Result.err _ => IO.pure false
    }
}

def two_actions (log : Ref I64) : HandlerT IO I64 := do {
    let _a : I64 <- HandlerT.lift_io (Ref.add_i64 log 1i64);
    let b : I64 <- HandlerT.lift_io (Ref.add_i64 log 1i64);
    return b
}

#[test]
def test_bind_order : IO Bool := do {
    let log : Ref I64 <- Ref.new 0i64;
    let r <- HandlerT.run_io (two_actions log) (get_req "/");
    let n <- Ref.get log;
    match r {
        Result.ok v => IO.pure (Bool.and (I64.beq v 2i64) (I64.beq n 2i64)),
        Result.err _ => IO.pure false
    }
}

def throwing_with_log (log : Ref I64) : HandlerT IO I64 := do {
    let e : HttpError := HttpError.make 500u16 "boom";
    let _u : Unit <- HandlerT.throw_io e;
    let _n : I64 <- HandlerT.lift_io (Ref.add_i64 log 1i64);
    return 1i64
}

#[test]
def test_throw_short_circuits : IO Bool := do {
    let log : Ref I64 <- Ref.new 0i64;
    let r <- HandlerT.run_io (throwing_with_log log) (get_req "/");
    let n <- Ref.get log;
    match r {
        Result.ok _ => IO.pure false,
        Result.err e => IO.pure (Bool.and (U16.beq e.status 500u16) (I64.beq n 0i64))
    }
}

#[test]
def test_catch_recovers : IO Bool := do {
    let log : Ref I64 <- Ref.new 0i64;
    let h : HandlerT IO I64 :=
        HandlerT.catch_io (throwing_with_log log)
            (fn (_e : HttpError) => HandlerT.pure_io 7i64);
    let r <- HandlerT.run_io h (get_req "/");
    match r {
        Result.ok v => IO.pure (I64.beq v 7i64),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_catch_can_rethrow : IO Bool := do {
    let log : Ref I64 <- Ref.new 0i64;
    let h : HandlerT IO I64 :=
        HandlerT.catch_io (throwing_with_log log)
            (fn (e : HttpError) => HandlerT.throw_io e);
    let r <- HandlerT.run_io h (get_req "/");
    match r {
        Result.ok _ => IO.pure false,
        Result.err e => IO.pure (U16.beq e.status 500u16)
    }
}

def set_status_418 (e : HttpError) : HttpError :=
    match e {
        { status, headers, body, detail } =>
            let e2 : HttpError :=
                { status := 418u16, headers := headers, body := body, detail := detail } in
            e2
    }

#[test]
def test_map_error_changes_status : IO Bool := do {
    let log : Ref I64 <- Ref.new 0i64;
    let h : HandlerT IO I64 :=
        HandlerT.map_error_io set_status_418 (throwing_with_log log);
    let r <- HandlerT.run_io h (get_req "/");
    match r {
        Result.ok _ => IO.pure false,
        Result.err e => IO.pure (U16.beq e.status 418u16)
    }
}

// ── context ─────────────────────────────────────────────────────────────

def request_path : HandlerT IO String := do {
    let p : String <- HandlerT.path_io;
    return p
}

#[test]
def test_path_read_twice : IO Bool := do {
    let h : HandlerT IO Bool := do {
        let a : String <- HandlerT.path_io;
        let b : String <- HandlerT.path_io;
        return (Bool.and (String.beq a "/a") (String.beq b "/a"))
    };
    let r <- HandlerT.run_io h (get_req "/a");
    match r {
        Result.ok v => IO.pure v,
        Result.err _ => IO.pure false
    }
}

def path_with (path : String) : HandlerT IO String :=
    HandlerT.with_route path List.empty request_path

#[test]
def test_with_route_replaces_path : IO Bool := do {
    let r <- HandlerT.run_io (path_with "/b") (get_req "/a");
    match r {
        Result.ok p => IO.pure (String.beq p "/b"),
        Result.err _ => IO.pure false
    }
}

#[test]
def test_param_lookup : IO Bool := do {
    let h : HandlerT IO Bool := do {
        let id : Option String <- HandlerT.param_io "id";
        match id {
            Option.some v => return (String.beq v "42"),
            Option.none => return false
        }
    };
    let r <- HandlerT.run_io (HandlerT.with_route "/users/42" [Pair.pair "id" "42"] h)
        (get_req "/users/42");
    match r {
        Result.ok v => IO.pure v,
        Result.err _ => IO.pure false
    }
}

// ── old-API adapter ─────────────────────────────────────────────────────

def error_handler : HandlerT IO Response :=
    HandlerT.throw_io (HttpError.make 500u16 "boom")

#[test]
def test_to_old_maps_error : IO Bool := do {
    let res : Response <- HandlerT.to_old error_handler (get_req "/");
    IO.pure (U16.beq res.status 500u16)
}
