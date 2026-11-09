/// JSON-RPC tests: the two things a broken message layer does silently.
///
/// The first is the id. A response whose id does not match the request's is a HANG,
/// not an error -- the client has no way to report it, so it waits, and the
/// server believes it answered. The id therefore has to be echoed as the node the
/// client sent, and `test_a_numeric_id_is_echoed_without_becoming_a_float` is the
/// pin: an implementation that parsed the id into an `I64` and re-rendered it
/// through a float path emits `1.0` and hangs the client with nothing in any log.
///
/// The second is the request/notification split. Answering a notification is a
/// protocol violation the client reports; failing to answer a request is the same
/// silent hang. Both are one `if` apart in the server loop, so the distinction is
/// pinned here rather than left to the loop to get right.
///
/// Several tests assert EXACT wire strings, which pins the key order that
/// `Json.to_string` produces. That is deliberate: the order is what the client
/// parses, and a change to the object representation that reorders keys is a
/// change to what this server puts on the wire whether or not anything here
/// intended it. The strings below are the observed output, not a guess --
/// alphabetical, because the object is a `BTreeMap`.
use json::json {Json}
use toolkit::jsonrpc {
    RpcMessage, rpc_code_internal, rpc_code_invalid_params, rpc_code_invalid_request,
    rpc_code_method_not_found, rpc_code_parse_error, rpc_encode_error,
    rpc_encode_error_no_id, rpc_encode_notification, rpc_encode_request,
    rpc_encode_result, rpc_id, rpc_method, rpc_object, rpc_params, rpc_parse,
    rpc_version, rpc_wants_reply,
}

// --- Helpers ---
//
// Every helper is a single-level match on `RpcMessage`, so no `#[test]` def holds
// a value it then reaches into.

def jr_is_request (m : RpcMessage) : Bool :=
    match m {
        RpcMessage.request _i _me _p => true,
        _ => false,
    }

def jr_is_notification (m : RpcMessage) : Bool :=
    match m {
        RpcMessage.notification _me _p => true,
        _ => false,
    }

def jr_is_response (m : RpcMessage) : Bool :=
    match m {
        RpcMessage.response _i _r => true,
        _ => false,
    }

def jr_is_unparseable (m : RpcMessage) : Bool :=
    match m {
        RpcMessage.unparseable _r => true,
        _ => false,
    }

def jr_reason (m : RpcMessage) : String :=
    match m {
        RpcMessage.unparseable r => r,
        _ => "<not unparseable>",
    }

/// Render a node. Every assertion below compares wire text, so this is the one
/// place `Json` appears in a TYPE position in this file -- without it the import
/// is used only as a qualified prefix and the unused-import pass reports it.
def jr_json_text (j : Json) : String := Json.to_string j

/// The id rendered as JSON text, or a sentinel no assertion can mistake for an
/// id.
def jr_id_text (m : RpcMessage) : String :=
    match rpc_id m {
        Option.none => "<absent>",
        Option.some i => jr_json_text i,
    }

/// `"absent"`, `"null"`, or the rendered value -- the three cases a params field
/// has, kept apart because absent and null are different requests.
def jr_params_text (m : RpcMessage) : String :=
    match rpc_params m {
        Option.none => "absent",
        Option.some p => jr_json_text p,
    }

def jr_method_of (body : String) : String :=
    rpc_method (rpc_parse body)

// --- The id, echoed verbatim ---

/// A numeric id comes back as `1`, never `1.0`. This is the pin for the whole
/// module doc: the id is spliced, not re-rendered.
#[test]
def test_a_numeric_id_is_echoed_without_becoming_a_float : Bool :=
    String.beq (rpc_encode_result (Json.make_num_int 1) (Json.make_str "ok"))
        "{\"id\":1,\"jsonrpc\":\"2.0\",\"result\":\"ok\"}"

/// A string id stays a string, including the quotes. A server that coerced ids
/// to numbers would answer `"x1"` with `1` and desynchronize every client that
/// numbers its ids as strings.
#[test]
def test_a_string_id_is_echoed_verbatim : Bool :=
    String.beq (jr_id_text (rpc_parse (rpc_encode_request (Json.make_str "x1") "m" Json.make_null)))
        "\"x1\""

/// The other half of the same rule: an id the client sent as a number is a number
/// in the REQUEST we parse, so the round trip is a true identity and not a
/// coincidence of two renderings.
#[test]
def test_the_id_of_a_parsed_request_is_the_node_that_was_sent : Bool :=
    String.beq (jr_id_text (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"m\"}"))
        "42"

// --- Request versus notification ---

#[test]
def test_a_request_without_an_id_is_a_notification_that_wants_no_reply : Bool :=
    let m : RpcMessage := rpc_parse "{\"jsonrpc\":\"2.0\",\"method\":\"m\"}" in
    jr_is_notification m && Bool.not (rpc_wants_reply m)

/// An id that is PRESENT but null is a request, per the specification's
/// "notification has no id member" rule. The safe direction: answering a
/// notification is a visible error, ignoring a request is a hang.
#[test]
def test_an_explicitly_null_id_is_still_a_request : Bool :=
    let m : RpcMessage := rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":null,\"method\":\"m\"}" in
    jr_is_request m && rpc_wants_reply m && String.beq (jr_id_text m) "null"

#[test]
def test_a_message_with_an_id_and_a_result_is_a_response : Bool :=
    let m : RpcMessage := rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":null}" in
    jr_is_response m && Bool.not (rpc_wants_reply m)

/// The full matrix, so the loop's `if` has one place to be wrong instead of two.
#[test]
def test_only_a_request_wants_a_reply : Bool :=
    Bool.not (rpc_wants_reply (rpc_parse "{\"jsonrpc\":\"2.0\",\"method\":\"n\"}"))
        && rpc_wants_reply (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"r\"}")
        && Bool.not (rpc_wants_reply (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":1}"))
        && Bool.not (rpc_wants_reply (rpc_parse "not json"))
        && String.beq (jr_method_of "{\"jsonrpc\":\"2.0\",\"method\":\"n\"}") "n"

// --- Params: absent is not null ---

/// `params` omitted and `params: null` are DIFFERENT requests, and the difference
/// reaches the handler rather than being defaulted away here.
#[test]
def test_absent_params_is_not_the_same_as_null_params : Bool :=
    String.beq (jr_params_text (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"m\"}")) "absent"
        && String.beq (jr_params_text (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"m\",\"params\":null}")) "null"

#[test]
def test_params_are_available_to_the_handler : Bool :=
    String.beq (jr_params_text (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"m\",\"params\":{\"a\":1}}"))
        "{\"a\":1}"

// --- Malformed input ---

#[test]
def test_malformed_json_is_unparseable_with_a_reason : Bool :=
    let m : RpcMessage := rpc_parse "{\"jsonrpc\":" in
    jr_is_unparseable m && Bool.not (String.beq (jr_reason m) "")

/// JSON, but not a request: no method, no id, so there is nothing to answer and
/// nothing to answer it with.
#[test]
def test_an_object_with_neither_method_nor_id_is_unparseable : Bool :=
    jr_is_unparseable (rpc_parse "{\"jsonrpc\":\"2.0\"}")

#[test]
def test_a_method_that_is_not_a_string_is_unparseable : Bool :=
    jr_is_unparseable (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":42}")

/// An array body is valid JSON and not a JSON-RPC message. It must come back as
/// something the loop can answer, not as a crash or a silent drop.
#[test]
def test_a_non_object_body_is_unparseable : Bool :=
    jr_is_unparseable (rpc_parse "[1,2,3]")

/// A parse failure has no id, so the reply the server sends must carry a null one.
#[test]
def test_a_parse_error_is_answered_with_a_null_id : Bool :=
    String.beq (rpc_encode_error_no_id rpc_code_parse_error "bad json")
        "{\"error\":{\"code\":-32700,\"message\":\"bad json\"},\"id\":null,\"jsonrpc\":\"2.0\"}"

// --- Encoding ---

/// The key order is `BTreeMap`'s, i.e. alphabetical, and it is pinned because it
/// is what the client parses.
#[test]
def test_a_result_frame_sorts_its_keys_and_carries_the_version : Bool :=
    String.beq (rpc_encode_result (Json.make_num_int 1) (Json.make_str "ok"))
        "{\"id\":1,\"jsonrpc\":\"2.0\",\"result\":\"ok\"}"

/// A notification has NO id field. An implementation that emitted `"id":null` here
/// would make the client treat a notification as a request it must match.
#[test]
def test_a_notification_frame_has_no_id_field_at_all : Bool :=
    String.beq (rpc_encode_notification "m" Json.make_null)
        "{\"jsonrpc\":\"2.0\",\"method\":\"m\",\"params\":null}"

#[test]
def test_an_error_frame_nests_the_code_and_message : Bool :=
    String.beq (rpc_encode_error (Json.make_str "a") rpc_code_method_not_found "no such method")
        "{\"error\":{\"code\":-32601,\"message\":\"no such method\"},\"id\":\"a\",\"jsonrpc\":\"2.0\"}"

/// The four reserved codes, by value. They are wire constants: a client branches
/// on the number, so a typo here is invisible until a client misbehaves.
#[test]
def test_the_reserved_error_codes_have_their_specified_values : Bool :=
    I64.beq rpc_code_parse_error (0 - 32700)
        && I64.beq rpc_code_invalid_request (0 - 32600)
        && I64.beq rpc_code_method_not_found (0 - 32601)
        && I64.beq rpc_code_invalid_params (0 - 32602)
        && I64.beq rpc_code_internal (0 - 32603)

#[test]
def test_the_version_string_is_two_point_oh : Bool :=
    String.beq rpc_version "2.0"

// --- Escaping, through the whole layer ---

/// Hover text and diagnostics contain quotes, newlines and backslashes, and a
/// frame that renders them raw is not merely ugly -- it is unparseable by the
/// client, which turns a hover into a dropped connection. Escaping is
/// `Json.to_string`'s job and this proves the layer inherits it rather than
/// building strings by hand.
#[test]
def test_a_string_with_quotes_newlines_and_backslashes_survives_a_round_trip : Bool :=
    let nasty : String := "a\"b\nc\\d\te" in
    let body : String := rpc_encode_result (Json.make_num_int 1) (Json.make_str nasty) in
    let m : RpcMessage := rpc_parse body in
    match rpc_id m {
        Option.none => false,
        Option.some _i => String.beq body "{\"id\":1,\"jsonrpc\":\"2.0\",\"result\":\"a\\\"b\\nc\\\\d\\te\"}",
    }

/// A method name with a slash and a capital, which is every LSP method there is.
/// Pinned because a lowercasing or path-mangling step anywhere in the layer would
/// break method dispatch for all of them at once.
#[test]
def test_a_method_name_is_carried_through_unescaped : Bool :=
    String.beq (jr_method_of (rpc_encode_request Json.make_null "textDocument/hover" Json.make_null))
        "textDocument/hover"

// --- The method accessor on messages that have none ---

/// `rpc_method` answers the empty string for a message with no method, so a loop
/// that dispatches first and checks the kind second gets an unmatched name rather
/// than an unbound value.
#[test]
def test_a_message_without_a_method_reports_an_empty_method : Bool :=
    String.beq (rpc_method (rpc_parse "not json")) ""
        && String.beq (rpc_method (rpc_parse "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":1}")) ""

// --- A payload the size of a real buffer ---
//
// The tests above are all a few dozen bytes, and every one of them passed while
// the server crashed on the first real `didOpen` -- because the payload of a
// `didOpen` is the file, and this layer parses it, so the message layer's cost is
// linear in the size of the buffer the editor opens. `lang/src/module.mo` is
// 331 KB, and the layer has to survive it in constant stack: it did not, and the
// shape that failed is pinned by the size below rather than by a comment.
//
// The size is the mechanism, so it is asserted, not just used: 327,680 bytes is
// well past the ~90 KB at which a per-character non-tail recursion exhausts the
// default 8 MB stack, which is why the pin still bites if the accumulator in
// `many0` or the one-allocation join in `Json.parse_string_content` is ever
// rewritten back into the obvious shape.

/// One line of the big payload: 39 ASCII bytes and a newline, so the buffer has a
/// line structure to preserve and an escape for the parser to decode.
def jr_big_line : String :=
    "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"

def jr_big_block : String :=
    String.concat (String.concat jr_big_line jr_big_line)
        (String.concat jr_big_line jr_big_line)

#[partial]
def jr_big_grow (n : I64) (s : String) : String :=
    if I64.lt n 1
    then s
    else jr_big_grow (I64.sub n 1) (String.concat s s)

def jr_big_text (n : I64) : String :=
    jr_big_grow n jr_big_block

/// The `params` of a `didOpen` for a buffer holding `text` -- the shape
/// `motes/lsp` sends, at the size the editor actually opens.
def jr_did_open_params (text : String) : Json :=
    rpc_object [
        Pair.pair "textDocument" (rpc_object [
            Pair.pair "uri" (Json.make_str "file:///tmp/jr_big.mo"),
            Pair.pair "languageId" (Json.make_str "monad"),
            Pair.pair "version" (Json.make_num_int 1),
            Pair.pair "text" (Json.make_str text),
        ]),
    ]

/// Encode, frame-parse, and read back a `didOpen` for a 320 KB buffer. The
/// comparison is against the same params rendered before encoding, so it pins the
/// whole round trip -- nothing truncated, nothing dropped at an escape, nothing
/// reordered -- and not merely that parsing returned *something*.
///
/// The size is 160 bytes x 2^11, the same 327,680 bytes the position tests scan,
/// chosen because it is a size that is *known* to abort: the per-character
/// spellings this pins were measured dying there with `rc=-11` inside
/// `GC_clear_stack_inner`, well past the ~90 KB at which a frame-per-character
/// recursion exhausts the default 8 MB stack.
#[test]
def test_a_didopen_payload_the_size_of_a_real_buffer_round_trips : Bool :=
    let big : String := jr_big_text 11 in
    let params : Json := jr_did_open_params big in
    let frame : String := rpc_encode_notification "textDocument/didOpen" params in
    let m : RpcMessage := rpc_parse frame in
    I64.beq (String.length big) 327680
        && String.beq (rpc_method m) "textDocument/didOpen"
        && String.beq (jr_params_text m) (Json.to_string params)
