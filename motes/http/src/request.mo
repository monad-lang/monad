/// Request-level form helpers.
///
/// `moon` handlers should not have to know about `Content-Type` parsing or
/// multipart boundaries: these dispatch on the request's headers and body and
/// return fields or parts. The pure parsers live in `body.mo`; this module is
/// the caller-facing convenience layer.
///
/// A body that is a `Body.stream` cannot be decoded here — the handler must
/// drain it first with the IO body API. Errors name the media type rather than
/// returning an empty form, so a missing or wrong `Content-Type` is visible.

use lib::types {Request}
use lib::body {Body.parse_form, Body.parse_multipart_of, MultipartPart}

/// Decode an `application/x-www-form-urlencoded` body into fields.
pub def Request.form_fields (req : Request) : Result String (List (Pair String String)) :=
  Body.parse_form req.headers req.body

/// Decode a `multipart/form-data` body into parts (fields and files).
pub def Request.multipart (req : Request) : Result String (List MultipartPart) :=
  Body.parse_multipart_of req.headers req.body

/// Look up a field by name. Duplicate names are preserved by the parser;
/// this returns the first one.
pub def Request.param (name : String) (fields : List (Pair String String)) : Option String :=
  Request.param_go name fields

#[terminating]
def Request.param_go (name : String) (fields : List (Pair String String)) : Option String :=
  match fields {
    List.empty => Option.none,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq k name
          then Option.some v
          else Request.param_go name rest
      }
  }
