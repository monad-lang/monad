/// The tool-related wire types and their HAND-WRITTEN JSON codecs --
/// `ToolCall`/`ToolDef`, the two types whose wire shape is NESTED
/// under a `"function"` key, which the derive cannot emit or read (it
/// does flat field-per-field objects only). Both the types AND the
/// codecs live here, split from `types.mo` for the same reason
/// `motes/shuttle`'s `message_types.mo` and `file_args.mo` are split:
/// a hand-written def in the SAME file as a `reflect_type_info!`
/// invocation (every derive in `types.mo` is one) cannot reference the
/// file's own constructors or use `{ .. }` struct patterns -- the
/// macro expansion capture pass fails on both, measured directly.
/// Keeping the types here too gives the dependency ONE direction
/// (`types.mo` imports this; this imports nothing in the mote), so
/// the codec defs are in scope exactly where `types.mo`'s generated
/// code calls them.
///
/// The nested shape is load-bearing, not cosmetic -- verified live
/// against Ollama (`localhost:11434/v1/chat/completions`, 2026-10-13):
/// a FLAT tool definition reaches the model with the function name
/// stripped (the response's `function.name` comes back empty and the
/// model guesses the argument key), and a flat tool-call decode
/// cannot read a real response at all.
use json::json {
    Json, Json.make_str, Json.make_object, Json.get_str, Json.get_object, Json.object_get,
}
use std::map {Map, BTreeMap}

pub struct ToolCall {
    id : String,
    name : String,
    arguments : String,
}

/// Wire request shape: `{"id":..,"type":"function","function":{name,
/// arguments}}` -- an assistant message's prior tool calls are echoed
/// back in the history of the NEXT request, so the request direction
/// needs the nested wrapper too.
pub def ToolCall.serialize_json (t : ToolCall) : Json :=
    let fn_obj : Json := Json.make_object (Map.insert "name" (Json.make_str t.name) (Map.insert "arguments" (Json.make_str t.arguments) BTreeMap.empty)) in
    Json.make_object (Map.insert "id" (Json.make_str t.id) (Map.insert "type" (Json.make_str "function") (Map.insert "function" fn_obj BTreeMap.empty)))

def toolcall_str_field (name : String) (obj : BTreeMap String Json) : Result String String :=
    match Json.object_get name obj {
        Option.some j => Json.get_str j,
        Option.none => Result.err (String.concat "ToolCall: missing field: " name),
    }

/// Wire response shape (a real Ollama/OpenAI body): `{"id":..,
/// "index":0,"type":"function","function":{"name":..,"arguments":..}}`
/// -- `index`/`type` are skipped, name and arguments live one level
/// down under `function`.
pub def ToolCall.deserialize_json (j : Json) : Result String ToolCall :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match toolcall_str_field "id" obj {
                Result.err e => Result.err e,
                Result.ok id =>
                    match Json.object_get "function" obj {
                        Option.some fn_json =>
                            match Json.get_object fn_json {
                                Result.err e => Result.err e,
                                Result.ok fobj =>
                                    match toolcall_str_field "name" fobj {
                                        Result.err e => Result.err e,
                                        Result.ok name =>
                                            match toolcall_str_field "arguments" fobj {
                                                Result.err e => Result.err e,
                                                Result.ok arguments => Result.ok (ToolCall.mk id name arguments),
                                            },
                                    },
                            },
                        Option.none => Result.err "ToolCall: missing field: function",
                    },
            },
    }

pub struct ToolDef {
    name : String,
    description : String,
    parameters : Json,
}

/// Wire request shape: `{"type":"function","function":{"name":..,
/// "description":..,"parameters":..}}` -- `parameters` is already a
/// `Json` value, so it is embedded as-is.
pub def ToolDef.serialize_json (t : ToolDef) : Json :=
    let fn_obj : Json := Json.make_object (Map.insert "name" (Json.make_str t.name) (Map.insert "description" (Json.make_str t.description) (Map.insert "parameters" t.parameters BTreeMap.empty))) in
    Json.make_object (Map.insert "type" (Json.make_str "function") (Map.insert "function" fn_obj BTreeMap.empty))

def tooldef_field (name : String) (obj : BTreeMap String Json) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "ToolDef: missing field: " name),
    }

/// The mirror of `ToolDef.serialize_json` -- reads the nested
/// `function` object rather than a flat name/description/parameters
/// triple.
pub def ToolDef.deserialize_json (j : Json) : Result String ToolDef :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj =>
            match Json.object_get "function" obj {
                Option.some fn_json =>
                    match Json.get_object fn_json {
                        Result.err e => Result.err e,
                        Result.ok fobj =>
                            match tooldef_field "name" fobj {
                                Result.err e => Result.err e,
                                Result.ok name_j =>
                                    match Json.get_str name_j {
                                        Result.err e => Result.err e,
                                        Result.ok name =>
                                            match tooldef_field "description" fobj {
                                                Result.err e => Result.err e,
                                                Result.ok desc_j =>
                                                    match Json.get_str desc_j {
                                                        Result.err e => Result.err e,
                                                        Result.ok description =>
                                                            match tooldef_field "parameters" fobj {
                                                                Result.err e => Result.err e,
                                                                Result.ok parameters => Result.ok (ToolDef.mk name description parameters),
                                                            },
                                                    },
                                            },
                                    },
                            },
                    },
                Option.none => Result.err "ToolDef: missing field: function",
            },
    }
