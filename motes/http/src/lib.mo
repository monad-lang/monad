// The http mote's library root -- bare `use http` resolves here.
//
// This is the mote's curated API: the protocol types, the pure wire
// format, URI/query helpers, form and multipart parsing, the SSE client
// state machine, and the `Transport` byte surface. Helpers stay private;
// constructors are reached through their type namespace
// (`HttpVersion.http1_1`, `Body.text`), and no `{*}` globs are used.
//
// Names are added here in the same commit that adds the module, so the
// surface never drifts from what the mote actually exports.

pub use lib::types {
    Method, HttpVersion, Headers, Uri, Body, Framing, Request, Response, Transport,

    Status.ok, Status.created, Status.accepted, Status.no_content,
    Status.moved_permanently, Status.found, Status.see_other,
    Status.not_modified, Status.temporary_redirect, Status.permanent_redirect,
    Status.bad_request, Status.unauthorized, Status.forbidden, Status.not_found,
    Status.method_not_allowed, Status.conflict, Status.internal_server_error,
    Status.bad_gateway, Status.service_unavailable,

    Headers.empty, Headers.get, Headers.set, Headers.add, Headers.remove,
    Headers.is_empty, Headers.get_all,

    Uri.host, Body.is_empty, Body.is_text, Request.get, Response.ok_text,
}

pub use lib::uri {
    Uri.parse, Uri.format, Uri.resolve, Uri.percent_encode, Uri.percent_decode,
    Uri.percent_decode_or, Uri.parse_query, Uri.format_query,
}

pub use lib::strings {
    Strings.split_on, Strings.list_starts_with, Strings.list_drop_prefix,
    Strings.drop_bytes, Strings.base64_decode,
}

pub use lib::wire {
    Wire.parse_request, Wire.parse_response, Wire.parse_response_with_method,
    Wire.format_request, Wire.format_response, Wire.format_response_head,
    Wire.frame_request, Wire.frame_response,
    Wire.response_framing, Wire.response_has_body,
    Wire.chunk_step, Wire.decode_chunked,
}

pub use lib::body {
    MultipartPart,
    MultipartPart.field_name, MultipartPart.file_name,
    MultipartPart.content_type, MultipartPart.bytes,
    Body.from_bytes, Body.from_text, Body.from_form, Body.to_bytes_pure,
    Body.length, Body.content_type, Body.parse_multipart,
    Body.media_type, Body.boundary_of, Body.parse_urlencoded,
    Body.parse_form, Body.parse_multipart_of,
}

pub use lib::request {Request.form_fields, Request.multipart, Request.param}

pub use lib::sse {SseState, SseEvent, Sse.init, Sse.push}
