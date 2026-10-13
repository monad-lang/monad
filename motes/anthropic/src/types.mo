/// Wire-faithful types for the Anthropic Messages API -- deliberately
/// NOT shuttle's own normalized `Message`/`Turn` shape: this mote knows
/// nothing about "tools," "turns," or an agent loop, only the JSON this
/// specific API actually sends and expects. The adapter to shuttle's
/// normal form lives in `motes/shuttle/src/wire/anthropic.mo`.
///
/// Every codec here is HAND-WRITTEN, not derived: content is a TAGGED
/// block array (`{"type":"tool_use",...}`), which the derive cannot
/// emit or read (it does flat field-per-field objects only), and the
/// request carries optional whole-key segments (`system`/`tools`/
/// `thinking`/`output_config` are OMITTED, not nulled, when unused) --
/// which the derive's field-per-field shape also cannot express. With
/// zero `reflect_type_info!` invocations in this file, the
/// same-file-constructor capture limitation that forces `motes/openai`
/// and `motes/shuttle` to split types from hand-written codecs does not
/// apply, so types and codecs live together.
///
/// Type names are deliberately `Anthropic`-prefixed or wire-specific:
/// this is a whole-program-scope language (`mote.toml`'s own comment),
/// and a bare `Message`/`Usage`/`ToolDef` here would collide by
/// bare-name `mk` resolution with shuttle's and openai's own
/// same-arity constructors once the motes load together -- the exact
/// hazard `motes/openai/src/client.mo`'s `ApiUsage` header documents.
///
/// Two wire facts are load-bearing, not cosmetic:
///   * `tool_use.input` is a real JSON OBJECT, not a string of JSON --
///     unlike the OpenAI wire's `function.arguments`, which must be
///     parsed a second time. No double decode happens here.
///   * `tool_result.tool_use_id` is the WIRE name; shuttle's normal
///     form calls the same field `call_id`. Only the adapter renames.
use json::json {
    Json, Json.make_str, Json.make_bool, Json.make_num_int, Json.make_array,
    Json.make_object, Json.get_str, Json.get_bool, Json.get_num, Json.get_num_i64,
    Json.get_object, Json.get_array, Json.object_get,
}
use std::map {BTreeMap}

// ─── Content blocks ───

/// One content block. Every variant carries `cache : Bool`: the wire
/// expresses a prompt-cache breakpoint as an extra `cache_control`
/// object ON a block (or a tool), and a wire-faithful type must be
/// able to represent one anywhere the API allows it, not just where
/// the harness happens to set one today.
pub type Block {
    text (s : String) (cache : Bool),
    thinking (s : String) (cache : Bool),
    tool_use (id : String) (name : String) (input : Json) (cache : Bool),
    tool_result (tool_use_id : String) (content : String) (is_error : Bool) (cache : Bool),
}

def obj_field (name : String) (obj : BTreeMap String Json) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "missing field: " name),
    }

def obj_str_field (name : String) (obj : BTreeMap String Json) : Result String String :=
    match obj_field name obj {
        Result.err e => Result.err e,
        Result.ok j => Json.get_str j,
    }

def obj_int_field (name : String) (obj : BTreeMap String Json) : Result String I64 :=
    match obj_field name obj {
        Result.err e => Result.err e,
        Result.ok j => Json.get_num_i64 (Json.get_num j),
    }

/// A bool field that is ABSENT when false -- the wire's own convention
/// for `is_error` (and for nothing else here): decode absent-or-bad as
/// false rather than erroring.
def obj_bool_or_false (name : String) (obj : BTreeMap String Json) : Bool :=
    match Json.object_get name obj {
        Option.some j =>
            match Json.get_bool j {
                Result.ok b => b,
                Result.err _ => false,
            },
        Option.none => false,
    }

/// Same absent-means-zero convention for the cache-usage counters:
/// `cache_read_input_tokens` is omitted entirely on the first turn of
/// a conversation (nothing cached yet), so treating it as required
/// would fail every cold-start response body.
def obj_int_or_zero (name : String) (obj : BTreeMap String Json) : I64 :=
    match Json.object_get name obj {
        Option.some j =>
            match Json.get_num_i64 (Json.get_num j) {
                Result.ok n => n,
                Result.err _ => 0,
            },
        Option.none => 0,
    }

/// `cache_control` is an object, but only one shape exists today
/// (`{"type":"ephemeral"}`, optionally with a `ttl`); a Bool captures
/// breakpoint presence without inventing a ttl model nothing sets.
def block_cache_of (obj : BTreeMap String Json) : Bool :=
    match Json.object_get "cache_control" obj {
        Option.some _ => true,
        Option.none => false,
    }

def with_cache (cache : Bool) (obj : BTreeMap String Json) : BTreeMap String Json :=
    if cache then
        let ctrl : Json := Json.make_object (Map.insert "type" (Json.make_str "ephemeral") BTreeMap.empty) in
        Map.insert "cache_control" ctrl obj
    else
        obj

/// The `Json.make_object (Map.insert ...)` values in this file are
/// deliberately let-bound BEFORE being handed to an outer `Map.insert`:
/// a class-method call (`Map.insert`) nested in the VALUE argument of
/// another `Map.insert` call misdispatches at run time under the Rust
/// host -- the outer call's dict argument is wired to the map instead
/// of the dictionary, and the dict-projection match dies with
/// "no match arm for tag 1" (the BTreeMap.node tag). Nesting in the
/// MAP argument position (the `Map.insert "type" v (Map.insert ...)`
/// chains everywhere below) is fine; only the value position is
/// affected, and only when the value itself contains a class-method
/// call. Same family as the known `Map`-dispatch issue in the repo
/// AGENTS (Known Type Checker Issues #3).
def effort_to_json (effort : Option String) (with_thinking : BTreeMap String Json) : Json :=
    match effort {
        Option.some s =>
            let cfg : Json := Json.make_object (Map.insert "effort" (Json.make_str s) BTreeMap.empty) in
            Json.make_object (Map.insert "output_config" cfg with_thinking),
        Option.none => Json.make_object with_thinking,
    }

/// `is_error` is emitted only when TRUE, matching the wire (the API
/// docs mark it optional; false is the default and is simply not
/// sent). The decode side accepts either form.
pub def Block.serialize_json (b : Block) : Json :=
    match b {
        Block.text s cache =>
            Json.make_object (with_cache cache
                (Map.insert "type" (Json.make_str "text")
                (Map.insert "text" (Json.make_str s)
                BTreeMap.empty))),
        Block.thinking s cache =>
            Json.make_object (with_cache cache
                (Map.insert "type" (Json.make_str "thinking")
                (Map.insert "thinking" (Json.make_str s)
                BTreeMap.empty))),
        Block.tool_use id name input cache =>
            Json.make_object (with_cache cache
                (Map.insert "type" (Json.make_str "tool_use")
                (Map.insert "id" (Json.make_str id)
                (Map.insert "name" (Json.make_str name)
                (Map.insert "input" input
                BTreeMap.empty))))),
        Block.tool_result tool_use_id content is_error cache =>
            let base :=
                Map.insert "type" (Json.make_str "tool_result")
                (Map.insert "tool_use_id" (Json.make_str tool_use_id)
                (Map.insert "content" (Json.make_str content)
                BTreeMap.empty)) in
            let with_err :=
                if is_error then Map.insert "is_error" (Json.make_bool true) base else base in
            Json.make_object (with_cache cache with_err),
    }

def block_text_of (obj : BTreeMap String Json) : Result String Block :=
    match obj_str_field "text" obj {
        Result.err e => Result.err e,
        Result.ok s => Result.ok (Block.text s (block_cache_of obj)),
    }

def block_thinking_of (obj : BTreeMap String Json) : Result String Block :=
    match obj_str_field "thinking" obj {
        Result.err e => Result.err e,
        Result.ok s => Result.ok (Block.thinking s (block_cache_of obj)),
    }

def block_tool_use_of (obj : BTreeMap String Json) : Result String Block :=
    match obj_str_field "id" obj {
        Result.err e => Result.err e,
        Result.ok id =>
            match obj_str_field "name" obj {
                Result.err e => Result.err e,
                Result.ok name =>
                    match obj_field "input" obj {
                        Result.err e => Result.err e,
                        Result.ok input => Result.ok (Block.tool_use id name input (block_cache_of obj)),
                    },
            },
    }

def block_tool_result_of (obj : BTreeMap String Json) : Result String Block :=
    match obj_str_field "tool_use_id" obj {
        Result.err e => Result.err e,
        Result.ok tool_use_id =>
            match obj_str_field "content" obj {
                Result.err e => Result.err e,
                Result.ok content => Result.ok (Block.tool_result tool_use_id content (obj_bool_or_false "is_error" obj) (block_cache_of obj)),
            },
    }

pub def Block.deserialize_json (j : Json) : Result String Block :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match obj_str_field "type" obj {
                Result.err e => Result.err e,
                Result.ok tag =>
                    if tag == "text" then block_text_of obj
                    else if tag == "thinking" then block_thinking_of obj
                    else if tag == "tool_use" then block_tool_use_of obj
                    else if tag == "tool_result" then block_tool_result_of obj
                    else Result.err (String.concat "unknown block type: " tag),
            },
    }

// ─── Request side ───

/// One `messages[]` entry. `role` is only `user`/`assistant` on the
/// wire -- the system prompt is a TOP-LEVEL request field, not a
/// message, and `tool_result` blocks ride inside a `user` message.
pub struct AnthropicMessage {
    role : String,
    content : List Block,
}

pub def AnthropicMessage.serialize_json (m : AnthropicMessage) : Json :=
    Json.make_object
        (Map.insert "role" (Json.make_str m.role)
        (Map.insert "content" (Json.make_array (List.map (fn (b : Block) => Block.serialize_json b) m.content))
        BTreeMap.empty))

/// Anthropic's tool table is FLAT (`{name, description, input_schema}`)
/// -- no `function` nesting, unlike the OpenAI wire. `input_schema` is
/// already a `Json` value, so it is embedded as-is.
pub struct AnthropicTool {
    name : String,
    description : String,
    input_schema : Json,
    cache : Bool,
}

pub def AnthropicTool.serialize_json (t : AnthropicTool) : Json :=
    Json.make_object (with_cache t.cache
        (Map.insert "name" (Json.make_str t.name)
        (Map.insert "description" (Json.make_str t.description)
        (Map.insert "input_schema" t.input_schema
        BTreeMap.empty))))

/// The request. `max_tokens` is REQUIRED by the wire (unlike the
/// OpenAI side, where it is optional); `system`/`tools` are OMITTED
/// when empty rather than sent as empty arrays; `thinking := true`
/// emits `{"type":"adaptive"}`; `effort := Option.some e` emits
/// `{"output_config":{"effort":e}}`. Serialize is the only direction
/// this mote needs -- a request is never decoded.
pub struct MessagesRequest {
    model : String,
    max_tokens : I64,
    system : List Block,
    messages : List AnthropicMessage,
    tools : List AnthropicTool,
    thinking : Bool,
    effort : Option String,
}

/// Positional destructure, matching the corpus's hand-written-codec
/// precedent (`motes/shuttle/src/message_types.mo`). Note the
/// `Map.insert`-in-value-position constraint documented above
/// `effort_to_json`: this def's `Json.make_object (Map.insert ...)`
/// values are all let-bound for that reason, never inlined into the
/// outer `Map.insert` call.
pub def MessagesRequest.serialize_json (r : MessagesRequest) : Json :=
    match r {
        MessagesRequest.mk model max_tokens system messages tools thinking effort =>
            let base :=
                Map.insert "model" (Json.make_str model)
                (Map.insert "max_tokens" (Json.make_num_int max_tokens)
                BTreeMap.empty) in
            let with_system :=
                match system {
                    List.empty => base,
                    List.cons _ _ =>
                        Map.insert "system" (Json.make_array (List.map (fn (b : Block) => Block.serialize_json b) system)) base,
                } in
            let with_messages :=
                Map.insert "messages" (Json.make_array (List.map (fn (m : AnthropicMessage) => AnthropicMessage.serialize_json m) messages)) with_system in
            let with_tools :=
                match tools {
                    List.empty => with_messages,
                    List.cons _ _ =>
                        Map.insert "tools" (Json.make_array (List.map (fn (t : AnthropicTool) => AnthropicTool.serialize_json t) tools)) with_messages,
                } in
            let with_thinking :=
                if thinking then
                    let tval : Json := Json.make_object (Map.insert "type" (Json.make_str "adaptive") BTreeMap.empty) in
                    Map.insert "thinking" tval with_tools
                else
                    with_tools in
            effort_to_json effort with_thinking,
    }

// ─── Response side ───

pub struct AnthropicUsage {
    input_tokens : I64,
    output_tokens : I64,
    cache_read_input_tokens : I64,
}

pub def AnthropicUsage.deserialize_json (j : Json) : Result String AnthropicUsage :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match obj_int_field "input_tokens" obj {
                Result.err e => Result.err e,
                Result.ok input_tokens =>
                    match obj_int_field "output_tokens" obj {
                        Result.err e => Result.err e,
                        Result.ok output_tokens =>
                            Result.ok (AnthropicUsage.mk input_tokens output_tokens (obj_int_or_zero "cache_read_input_tokens" obj)),
                    },
            },
    }

pub struct MessagesResponse {
    content : List Block,
    stop_reason : String,
    usage : AnthropicUsage,
}

#[partial]
def deserialize_blocks (js : List Json) : Result String (List Block) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest =>
            match Block.deserialize_json j {
                Result.err e => Result.err e,
                Result.ok b =>
                    match deserialize_blocks rest {
                        Result.err e => Result.err e,
                        Result.ok bs => Result.ok (List.cons b bs),
                    },
            },
    }

pub def MessagesResponse.deserialize_json (j : Json) : Result String MessagesResponse :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match obj_field "content" obj {
                Result.err e => Result.err e,
                Result.ok content_j =>
                    match Json.get_array content_j {
                        Result.err e => Result.err e,
                        Result.ok block_js =>
                            match deserialize_blocks block_js {
                                Result.err e => Result.err e,
                                Result.ok blocks =>
                                    match obj_str_field "stop_reason" obj {
                                        Result.err e => Result.err e,
                                        Result.ok stop_reason =>
                                            match obj_field "usage" obj {
                                                Result.err e => Result.err e,
                                                Result.ok usage_j =>
                                                    match AnthropicUsage.deserialize_json usage_j {
                                                        Result.err e => Result.err e,
                                                        Result.ok usage => Result.ok (MessagesResponse.mk blocks stop_reason usage),
                                                    },
                                            },
                                    },
                            },
                    },
            },
    }
