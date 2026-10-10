/// `Role`/`Content`/`StopReason` -- the sum-type half of `message.mo`'s
/// Core Types, split into their own file. The derive macro's own
/// single-constructor restriction means these need hand-written
/// `serialize_json`/`deserialize_json` regardless; splitting them out
/// ALSO works around a separate, measured limitation: a top-level
/// function in the SAME FILE as a `reflect_type_info!` invocation
/// (`message.mo` derives `Message`/`Usage`/`Turn`) that references one
/// of this file's OWN constructors fails macro-expansion's "check +
/// capture the loaded program" pass with `unbound variable`, even
/// though the constructor is perfectly real -- the capture pass is
/// measurably weaker than normal type-checking for locally-defined
/// constructors (the same family as struct literals needing a `let`
/// instead of a top-level `def`, probed in `motes/serde`). Defining
/// these in a sibling file sidesteps it entirely.
use json::json {Json}
use json::json {
    Json.make_str, Json.make_bool, Json.make_object, Json.get_str,
    Json.get_bool, Json.get_object, Json.object_get,
}
use std::map {}

pub type Role {
    system_,
    user,
    assistant,
    tool,
}

def role_tag (r : Role) : String :=
    match r {
        Role.system_ => "system",
        Role.user => "user",
        Role.assistant => "assistant",
        Role.tool => "tool",
    }

pub def Role.serialize_json (r : Role) : Json := Json.make_str (role_tag r)

def role_of_tag (s : String) : Result String Role :=
    if s == "system" then Result.ok Role.system_
    else if s == "user" then Result.ok Role.user
    else if s == "assistant" then Result.ok Role.assistant
    else if s == "tool" then Result.ok Role.tool
    else Result.err (String.concat "unknown role: " s)

pub def Role.deserialize_json (j : Json) : Result String Role :=
    match Json.get_str j {
        Result.err e => Result.err e,
        Result.ok s => role_of_tag s,
    }

pub type Content {
    text (s : String),
    tool_use (id : String) (name : String) (input : Json),
    tool_result (call_id : String) (output : String) (is_error : Bool),
    thinking (s : String),
}

def content_field (name : String) (obj : BTreeMap String Json) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "missing field: " name),
    }

def content_str_field (name : String) (obj : BTreeMap String Json) : Result String String :=
    match content_field name obj {
        Result.err e => Result.err e,
        Result.ok j => Json.get_str j,
    }

pub def Content.serialize_json (c : Content) : Json :=
    match c {
        Content.text s =>
            Json.make_object (Map.insert "type" (Json.make_str "text") (Map.insert "text" (Json.make_str s) BTreeMap.empty)),
        Content.tool_use id name input =>
            Json.make_object (Map.insert "type" (Json.make_str "tool_use")
                (Map.insert "id" (Json.make_str id)
                (Map.insert "name" (Json.make_str name)
                (Map.insert "input" input BTreeMap.empty)))),
        Content.tool_result call_id output is_error =>
            Json.make_object (Map.insert "type" (Json.make_str "tool_result")
                (Map.insert "call_id" (Json.make_str call_id)
                (Map.insert "output" (Json.make_str output)
                (Map.insert "is_error" (Json.make_bool is_error) BTreeMap.empty)))),
        Content.thinking s =>
            Json.make_object (Map.insert "type" (Json.make_str "thinking") (Map.insert "text" (Json.make_str s) BTreeMap.empty)),
    }

def content_tool_use_of (obj : BTreeMap String Json) : Result String Content :=
    match content_str_field "id" obj {
        Result.err e => Result.err e,
        Result.ok id =>
            match content_str_field "name" obj {
                Result.err e => Result.err e,
                Result.ok name =>
                    match content_field "input" obj {
                        Result.err e => Result.err e,
                        Result.ok input => Result.ok (Content.tool_use id name input),
                    },
            },
    }

def content_tool_result_of (obj : BTreeMap String Json) : Result String Content :=
    match content_str_field "call_id" obj {
        Result.err e => Result.err e,
        Result.ok call_id =>
            match content_str_field "output" obj {
                Result.err e => Result.err e,
                Result.ok output =>
                    match content_field "is_error" obj {
                        Result.err e => Result.err e,
                        Result.ok j =>
                            match Json.get_bool j {
                                Result.err e => Result.err e,
                                Result.ok is_error => Result.ok (Content.tool_result call_id output is_error),
                            },
                    },
            },
    }

def content_of_tagged_obj (tag : String) (obj : BTreeMap String Json) : Result String Content :=
    if tag == "text" then
        match content_str_field "text" obj { Result.err e => Result.err e, Result.ok s => Result.ok (Content.text s) }
    else if tag == "tool_use" then content_tool_use_of obj
    else if tag == "tool_result" then content_tool_result_of obj
    else if tag == "thinking" then
        match content_str_field "text" obj { Result.err e => Result.err e, Result.ok s => Result.ok (Content.thinking s) }
    else Result.err (String.concat "unknown content type: " tag)

pub def Content.deserialize_json (j : Json) : Result String Content :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match content_str_field "type" obj {
                Result.err e => Result.err e,
                Result.ok tag => content_of_tagged_obj tag obj,
            },
    }

pub type StopReason {
    end_turn,
    tool_use_stop,
    max_tokens,
    refusal,
    other (s : String),
}

pub def StopReason.serialize_json (r : StopReason) : Json :=
    match r {
        StopReason.end_turn => Json.make_str "end_turn",
        StopReason.tool_use_stop => Json.make_str "tool_use_stop",
        StopReason.max_tokens => Json.make_str "max_tokens",
        StopReason.refusal => Json.make_str "refusal",
        StopReason.other s => Json.make_str s,
    }

def stop_reason_of_tag (s : String) : StopReason :=
    if s == "end_turn" then StopReason.end_turn
    else if s == "tool_use_stop" then StopReason.tool_use_stop
    else if s == "max_tokens" then StopReason.max_tokens
    else if s == "refusal" then StopReason.refusal
    else StopReason.other s

pub def StopReason.deserialize_json (j : Json) : Result String StopReason :=
    match Json.get_str j {
        Result.err e => Result.err e,
        Result.ok s => Result.ok (stop_reason_of_tag s),
    }
