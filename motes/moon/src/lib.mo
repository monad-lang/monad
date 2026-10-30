// The moon mote's library root -- bare `use moon` resolves here.
//
// This is the server's curated API: the serve entry points, the pure
// router, and middleware as function composition. Helpers and the
// connection/fiber loops stay private; `Route` is constructed through
// `Router.get/post/...` rather than by hand.

pub use lib::server {
    Server.serve, Server.serve_result, Server.serve_concurrent, Server.static,
    Server.handle_connection, Server.serve_connection,
    Server.max_keep_alive_requests, Server.max_header_bytes, Server.max_body_bytes,
    ServerConfig, ServerConfig.default, ServerConfig.on, ServerConfig.with_host,
    ServerConfig.with_timeouts, ServerConfig.with_limits, ServerConfig.dev,
    ServerHandle,
    Server.run, Server.run_response, Server.start, Server.wait, Server.shutdown,
    ServerHandleT, Server.run_t, Server.run_with, Server.start_t, Server.wait_t,
    Server.shutdown_t, Server.plain_transport, Server.keep_alive_with,
}

pub use lib::handler {
    Handler.of_response, Handler.recover, Handler.map_error, Handler.try,
}

pub use lib::router {
    Route, Router.route, Router.get, Router.post, Router.put, Router.delete,
    Router.patch, Router.head, Router.options, Router.mount, Router.allowed,
    Router.param,
    RouteT, RouterT.get, RouterT.post, RouterT.put, RouterT.delete,
    RouterT.patch, RouterT.head, RouterT.options, RouterT.route, RouterT.scope,
    RouterT.find, RouterT.allowed,
}

pub use lib::context {
    Ctx, Ctx.make, Ctx.request, Ctx.session, Ctx.with_request, Ctx.with_session,
    SessionSlot, SessionSlot.handle,
}

pub use lib::handler_t {
    HttpError, HttpError.make, HttpError.to_response, HttpError.with_header,
    HttpError.not_found, HttpError.bad_request, HttpError.forbidden,
    HttpError.unauthorized, HttpError.internal, HttpError.payload_too_large,
    HttpError.headers_too_large,
    HandlerT, HandlerT.run, HandlerT.pure, HandlerT.lift, HandlerT.ask,
    HandlerT.request, HandlerT.session, HandlerT.throw, HandlerT.catch,
    HandlerT.map_error, HandlerT.local, HandlerT.with_request,
    HandlerT.with_session, HandlerT.pure_io, HandlerT.throw_io, HandlerT.lift_io,
    HandlerT.ask_io, HandlerT.request_io, HandlerT.session_io, HandlerT.catch_io,
    HandlerT.map_error_io, HandlerT.io_bind, HandlerT.run_io, HandlerT.to_old,
    HandlerT.of_old,
}

pub use lib::middleware_t {
    MiddlewareT.logging, MiddlewareT.map_response, MiddlewareT.cors,
    MiddlewareT.content_type, MiddlewareT.recover, MiddlewareT.auth_basic_ct,
    MiddlewareT.auth_bearer_ct,
}

pub use lib::middleware {
    Middleware.logging, Middleware.cors, Middleware.content_type,
    Middleware.recover, Middleware.auth_basic, Middleware.auth_bearer,
}

pub use lib::static_files {
    StaticConfig, StaticConfig.default,
    Static.handler, Static.safe_path, Static.relative_after_slash,
    Static.mime_of, Static.etag, Static.etag_matches, Static.range,
    Static.respond, Static.url_path_of,
}

// Form data is decoded in `http`; re-export the request-level helpers so a
// `moon` handler can import its whole surface from one place.
pub use http::request {Request.form_fields, Request.multipart, Request.param}

pub use lib::session {
    Session, Session.get, Session.put, SessionHandle, SessionHandle.make,
    SessionHandle.get, SessionHandle.put,
    SessionStore, SessionStore.new, SessionStore.begin, SessionStore.load,
    SessionStore.commit, SessionStore.rotate, SessionStore.destroy,
    SessionStore.with_session, SessionStore.middleware,
}

pub use lib::session_mw {SessionStore.with_session_t}

pub use lib::csrf {
    Csrf.token, Csrf.verify, Csrf.hidden_field, Csrf.check,
    Csrf.secret_from_env,
}

pub use lib::live {
    Live.events, Live.reload, Live.reload_t, Live.watch, Live.watch_files,
    Live.watch_tree, Live.script, Live.inject, Live.dev_middleware,
    Live.dev_middleware_t,
}
