// The moon mote's library root -- bare `use moon` resolves here.
//
// This is the server's curated API: the serve entry points, the pure
// router, and middleware as function composition. Helpers and the
// connection/fiber loops stay private; `Route` is constructed through
// `Router.get/post/...` rather than by hand.

pub use lib::server {
    Server.serve, Server.serve_result, Server.serve_concurrent, Server.static,
    Server.handle_connection, Server.serve_connection,
    Server.max_keep_alive_requests,
    ServerConfig, ServerConfig.default, ServerConfig.on, ServerHandle,
    Server.run, Server.run_response, Server.start, Server.wait, Server.shutdown,
}

pub use lib::handler {
    Handler.of_response, Handler.recover, Handler.map_error, Handler.try,
}

pub use lib::router {
    Route, Router.route, Router.get, Router.post, Router.put, Router.delete,
    Router.patch, Router.head, Router.options, Router.mount, Router.allowed,
    Router.param,
}

pub use lib::middleware {
    Middleware.logging, Middleware.cors, Middleware.content_type,
    Middleware.recover, Middleware.auth_basic, Middleware.auth_bearer,
}

pub use lib::static_files {
    StaticConfig, StaticConfig.default,
    Static.handler, Static.safe_path, Static.mime_of, Static.etag, Static.range,
    Static.respond,
}

// Form data is decoded in `http`; re-export the request-level helpers so a
// `moon` handler can import its whole surface from one place.
pub use http::request {Request.form_fields, Request.multipart, Request.param}
