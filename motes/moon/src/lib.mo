// The moon mote's library root -- bare `use moon` resolves here.
//
// This is the server's curated API: the serve entry points, the pure
// router, and middleware as function composition. Helpers and the
// connection/fiber loops stay private; `Route` is constructed through
// `Router.get/post/...` rather than by hand.

pub use lib::server {
    Server.serve, Server.serve_concurrent, Server.static,
    Server.handle_connection, Server.serve_connection,
    Server.max_keep_alive_requests,
}

pub use lib::router {
    Route, Router.route, Router.get, Router.post, Router.put, Router.delete,
    Router.patch, Router.mount, Router.param,
}

pub use lib::middleware {
    Middleware.logging, Middleware.cors, Middleware.content_type,
    Middleware.recover, Middleware.auth_basic, Middleware.auth_bearer,
}

// Form data is decoded in `http`; re-export the request-level helpers so a
// `moon` handler can import its whole surface from one place.
pub use http::request {Request.form_fields, Request.multipart, Request.param}
