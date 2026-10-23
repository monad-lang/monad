/// JSON-RPC 2.0: the message layer both of this toolkit's protocols sit on.
///
/// `framing` answers "where does a message end"; this module answers "what does
/// it say". Both LSP and MCP are JSON-RPC 2.0 over their own framing, which is
/// the whole reason the two layers are separate modules rather than one
/// protocol-specific reader.
///
/// THE ID IS KEPT AS THE NODE THE CLIENT SENT, never as a parsed number, and
/// that is the one decision in this file that is load-bearing rather than
/// stylistic. A client sends `"id": 1` and matches the response to its request BY
/// THAT VALUE; a server that parsed the id into an `I64` and re-rendered it would
/// eventually emit `1.0` (or `"1"`) for some id and the client would have a
/// response it cannot place -- a hang with no error anywhere, since JSON-RPC has
/// no way to complain about an unmatched id. Carrying the `Json` node and
/// splicing it back out makes that impossible by construction: nothing in the
/// encode path can change a value it never inspects.
///
/// Nothing here is LSP-specific, and nothing here frames: `rpc_encode_*` returns
/// a JSON BODY, and the caller wraps it with `framing`. That split is what lets
/// the same module serve MCP's newline-delimited transport, and it is what makes
/// every test below runnable without a socket.

use json::json {Json}
// `BTreeMap` IS NAMED, and the warning that costs is the right trade.
//
// `std/src/map.mo` has no `pub` decls at all, so naming `BTreeMap` here raises
// `cross_mote_package_private` -- that part of this comment's earlier advice was
// correct, and `lang/src/json.mo:7` carries the same warning for the same reason.
// What changed is the other side: an EMPTY filter is now a hard ERROR, because a
// `use` line is the complete dependency declaration and a brace item names a
// top-level declaration exactly (the `use`-completeness rule, enforced by
// default in the loader). A warning shared with main's own corpus beats an
// error that fails the build, and `lang/src/json.mo:7`'s `{BTreeMap, BTreeMap.to_list, empty}` is the
// spelling to match. The 21 such warnings in this corpus all predate these motes.
use std::map {Map, BTreeMap}

// --- Error codes ---
//
// The five the specification reserves. They are the whole error vocabulary this
// server needs: a method it does not implement is `method not found`, malformed
// params are `invalid params`, and anything the server itself could not do is
// `internal`, which is also the code for every failure with no better one.
//
// Written as `0 - n` rather than `-n` so the negative literal cannot be read as
// subtraction by a reader or a reparse; these are the only negative constants in
// this mote and they are worth the four extra characters.

/// The payload was not JSON at all. The one error whose id is necessarily
/// unknown, since the request that would have carried it could not be read.
pub def rpc_code_parse_error : I64 := 0 - 32700

/// JSON, but not a JSON-RPC request object.
pub def rpc_code_invalid_request : I64 := 0 - 32600

/// Well-formed, but this server does not implement the method. The server MUST
/// answer this rather than ignore an unknown request, and it is the code that
/// makes a client able to tell a missing feature from a hung one.
pub def rpc_code_method_not_found : I64 := 0 - 32601

pub def rpc_code_invalid_params : I64 := 0 - 32602

pub def rpc_code_internal : I64 := 0 - 32603

/// The version string every message carries, in and out.
pub def rpc_version : String := "2.0"

/// An id, as an `Option`: a message that carries one is a request and MUST be
/// answered; a message that does not is a notification and MUST NOT be. The
/// `Option` is not a nicety -- answering a notification, or failing to answer a
/// request, are both protocol violations, and this is the type that makes the
/// distinction visible at every call site.
///
/// `Option (Option Json)` would be the honest type for a RESPONSE (where an
/// absent id is legal and means "the request could not be read"), which is why
/// `RpcMessage.failure` below carries `Option Json` rather than reusing
/// `RpcId`-style naming. That asymmetry is the specification's, not this
/// module's.
pub type RpcMessage {
  /// A request: it has an id and it must be answered.
  request (id : Json) (method : String) (params : Option Json),
  /// A notification: no id, and answering it is a protocol violation.
  notification (method : String) (params : Option Json),
  /// A response to something this server sent. It never sends requests, so
  /// this arrives only from a confused or hostile peer.
  response (id : Json) (result : Json),
  /// An error to send. Ids are absent when the request that would have carried
  /// one was unreadable.
  failure (id : Option Json) (code : I64) (message : String),
  /// Input this module could not turn into any of the above. Carries a reason
  /// for the log, and the server answers `rpc_code_parse_error` (or
  /// `rpc_code_invalid_request`) with a null id.
  unparseable (reason : String),
}

/// Does this message demand an answer?
///
/// The single question the server loop must get right: it decides whether to
/// write anything back. A notification treated as a request puts an unsolicited
/// response on the stream, which clients report as an internal error; a request
/// treated as a notification leaves the client waiting forever.
pub def rpc_wants_reply (m : RpcMessage) : Bool :=
  match m {
    RpcMessage.request _id _method _params => true,
    RpcMessage.notification _method _params => false,
    RpcMessage.response _id _result => false,
    RpcMessage.failure _id _code _message => false,
    RpcMessage.unparseable _reason => false,
  }

/// The method name, or the empty string for a message that has none.
pub def rpc_method (m : RpcMessage) : String :=
  match m {
    RpcMessage.request _id method _params => method,
    RpcMessage.notification method _params => method,
    RpcMessage.response _id _result => "",
    RpcMessage.failure _id _code _message => "",
    RpcMessage.unparseable _reason => "",
  }

/// The params node, or `Option.none` for a request that omitted it.
///
/// A JSON-RPC request may legitimately omit `params` entirely, and an empty
/// array is NOT the same as an absent one for methods that take none -- so this
/// stays an `Option` all the way to the handler rather than being defaulted
/// here.
pub def rpc_params (m : RpcMessage) : Option Json :=
  match m {
    RpcMessage.request _id _method params => params,
    RpcMessage.notification _method params => params,
    RpcMessage.response _id _result => Option.none,
    RpcMessage.failure _id _code _message => Option.none,
    RpcMessage.unparseable _reason => Option.none,
  }

/// The id node of a message that has one, so a caller can echo it into an error
/// without re-deriving which constructor it came from.
pub def rpc_id (m : RpcMessage) : Option Json :=
  match m {
    RpcMessage.request id _method _params => Option.some id,
    RpcMessage.notification _method _params => Option.none,
    RpcMessage.response id _result => Option.some id,
    RpcMessage.failure id _code _message => id,
    RpcMessage.unparseable _reason => Option.none,
  }

// --- Object building ---

/// Start an empty JSON object.
///
/// THE `BTreeMap String Json` ANNOTATION IS LOAD-BEARING, and the reason is a
/// trap worth recording. `Map`'s class declaration gives it a DEFAULT instance
/// (`class Map (M := HashMap)`, `std/src/map.mo:18`), so an unannotated
/// `Map.empty` resolves to a `HashMap` and NOT to the `BTreeMap` that
/// `Json.make_object` requires. Inference does not catch it at the `Map.empty`
/// site -- the expected type is not known there -- so the mistake surfaces much
/// later, while the `Json` node is being built, as a constructor-arity error
/// naming none of these types. One annotated binding, here, is what stops every
/// call site in this mote from having to know it.
def rpc_empty_object : BTreeMap String Json := Map.empty

/// Build an object from its fields. Later pairs win, which cannot arise from the
/// callers here -- each names its keys once -- so nothing depends on it.
///
/// This exists so that no caller in another mote has to name `BTreeMap`: the
/// signature is `List (Pair String Json) -> Json` and the map never appears.
#[partial]
pub def rpc_object (ps : List (Pair String Json)) : Json :=
  rpc_object_go ps rpc_empty_object

#[partial]
def rpc_object_go (ps : List (Pair String Json)) (m : BTreeMap String Json) : Json :=
  match ps {
    List.empty => Json.make_object m,
    List.cons p rest =>
      match p {
        Pair.pair k v => rpc_object_go rest (Map.insert k v m),
      },
  }

/// One field of a JSON object, or `Option.none` when the value is not an object
/// or the key is absent. Both are the same answer to every caller here: a
/// request without `method` is malformed and a request without `params` is fine,
/// and neither is worth a distinct error.
#[partial]
pub def rpc_field (key : String) (j : Json) : Option Json :=
  match Json.get_object j {
    Result.err _e => Option.none,
    Result.ok o => Json.object_get key o,
  }

/// Render a parse failure for the log.
///
/// `Json.ParseError`'s own `to_string` is not `pub`, but its constructors are,
/// so this matches them rather than asking for a promotion: the two-constructor
/// type is the whole vocabulary and rendering it cannot drift from the type
/// without a compile error.
def rpc_parse_error_text (pe : Json.ParseError) : String :=
  match pe {
    Json.ParseError.expected e f =>
      String.concat "expected " (String.concat e (String.concat ", found " f)),
    Json.ParseError.generic s => s,
  }

// --- Parsing ---

/// Turn a message body into an outcome.
///
/// Never fails: a body that cannot be read is `RpcMessage.unparseable` carrying
/// why, because the server has to answer SOMETHING for a malformed frame and a
/// function that returned an error would leave the caller to invent the reply.
///
/// A message with a `method` is a request when it carries an id and a
/// notification when it does not -- that is the specification's whole
/// distinction, and `"id": null` is NOT the same as an absent id. This reads
/// presence, not null-ness, and treats an explicit null id as present, which is
/// what a strict reading of the spec says and the safe way round: answering a
/// notification is a visible protocol error, while ignoring a request hangs the
/// client.
#[partial]
pub def rpc_parse (text : String) : RpcMessage :=
  match Json.parse text {
    Result.err pe => RpcMessage.unparseable (rpc_parse_error_text pe),
    Result.ok j => rpc_of_json j,
  }

#[partial]
def rpc_of_json (j : Json) : RpcMessage :=
  match rpc_field "method" j {
    Option.none => rpc_of_json_without_method j,
    Option.some mj =>
      match Json.get_str mj {
        Result.err _e => RpcMessage.unparseable "method is not a string",
        Result.ok method =>
          match rpc_field "id" j {
            Option.none => RpcMessage.notification method (rpc_field "params" j),
            Option.some id => RpcMessage.request id method (rpc_field "params" j),
          },
      },
  }

/// An object with no `method`. Either a response to a request this server never
/// sent, or not a JSON-RPC message at all -- and it is `response` only when it
/// carries both an id and a `result`, since guessing the other way would answer
/// a message the peer considers a reply.
#[partial]
def rpc_of_json_without_method (j : Json) : RpcMessage :=
  match rpc_field "id" j {
    Option.none => RpcMessage.unparseable "no method and no id",
    Option.some id =>
      match rpc_field "result" j {
        Option.none => RpcMessage.unparseable "no method and no result",
        Option.some result => RpcMessage.response id result,
      },
  }

// --- Encoding ---
//
// Every encoder returns a JSON BODY, unframed. `framing` adds `Content-Length`
// (or the newline), which is what keeps this module independent of which
// protocol is asking.

/// A response: the same id node the request carried, spliced back in untouched.
#[partial]
pub def rpc_encode_result (id : Json) (result : Json) : String :=
  Json.to_string
    (rpc_object [
      Pair.pair "jsonrpc" (Json.make_str rpc_version),
      Pair.pair "id" id,
      Pair.pair "result" result,
    ])

/// An error with a known id.
#[partial]
pub def rpc_encode_error (id : Json) (code : I64) (message : String) : String :=
  Json.to_string
    (rpc_object [
      Pair.pair "jsonrpc" (Json.make_str rpc_version),
      Pair.pair "id" id,
      Pair.pair "error" (rpc_error_node code message),
    ])

/// An error with NO id, which is what a parse failure gets: the request that
/// would have carried one could not be read, so the specification requires a
/// null there rather than any guess.
#[partial]
pub def rpc_encode_error_no_id (code : I64) (message : String) : String :=
  Json.to_string
    (rpc_object [
      Pair.pair "jsonrpc" (Json.make_str rpc_version),
      Pair.pair "id" Json.make_null,
      Pair.pair "error" (rpc_error_node code message),
    ])

def rpc_error_node (code : I64) (message : String) : Json :=
  rpc_object [
    Pair.pair "code" (Json.make_num_int code),
    Pair.pair "message" (Json.make_str message),
  ]

/// A message the server initiates, which for this server means diagnostics and
/// nothing else. A notification has no id by definition, so there is no id
/// parameter to get wrong.
#[partial]
pub def rpc_encode_notification (method : String) (params : Json) : String :=
  Json.to_string
    (rpc_object [
      Pair.pair "jsonrpc" (Json.make_str rpc_version),
      Pair.pair "method" (Json.make_str method),
      Pair.pair "params" params,
    ])

/// A request, which this server sends only in tests and in the session replay
/// harness -- it is a client-side message, and having it here is what lets the
/// replay script be the same code path as a real client.
#[partial]
pub def rpc_encode_request (id : Json) (method : String) (params : Json) : String :=
  Json.to_string
    (rpc_object [
      Pair.pair "jsonrpc" (Json.make_str rpc_version),
      Pair.pair "id" id,
      Pair.pair "method" (Json.make_str method),
      Pair.pair "params" params,
    ])
