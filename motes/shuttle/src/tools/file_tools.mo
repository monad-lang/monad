/// `ReadTool`/`WriteTool`/`EditTool`'s `ToolSpec`/`ToolImpl` values --
/// split from `file.mo` for the same reason `message_types.mo` is
/// split from `message.mo`: a bare `{ field := val }` struct literal
/// at the top level of a file that ALSO has a `reflect_type_info!`
/// invocation (`file.mo` derives `ReadArgs`/`WriteArgs`/`EditArgs`)
/// fails macro-expansion's capture pass with "cannot infer the type
/// of `{ .. }`", even with an explicit `def x : T := { .. }`
/// annotation right there.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::tools::file {read_run, write_run, edit_run}
use json::json {Json}
use std::map {BTreeMap}

/// A JSON-Schema object for one string parameter. The three tools'
/// implementations deserialize their arguments via
/// `ReadArgs`/`WriteArgs`/`EditArgs` (`file_args.mo`), so the schema
/// must declare exactly those keys -- with `schema := Json.null` the
/// model has no contract to follow and guesses (live-verified against
/// Ollama: `file_path` instead of `path`).
pub def str_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "string") (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

/// `{"type":"object","properties":{...},"required":[...]}` for a
/// flat all-string-parameters tool.
pub def params_schema (params : List (Pair String Json)) : Json :=
    let props := Json.make_object (params_to_map params BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object") (Map.insert "properties" props (Map.insert "required" (Json.make_array (List.map pair_fst params)) BTreeMap.empty)))

#[partial]
def params_to_map (params : List (Pair String Json)) (acc : BTreeMap String Json) : BTreeMap String Json :=
    match params {
        List.empty => acc,
        List.cons p rest => match p { Pair.pair k v => params_to_map rest (Map.insert k v acc) },
    }

def pair_fst (p : Pair String Json) : Json := Json.make_str (match p { Pair.pair k _ => k })

def read_params : List (Pair String Json) :=
    [str_param "path" "Absolute path of the file to read"]

def write_params : List (Pair String Json) :=
    [str_param "path" "Absolute path of the file to write", str_param "content" "Full contents to write"]

def edit_params : List (Pair String Json) :=
    [
        str_param "path" "Absolute path of the file to edit",
        str_param "expected_content" "The file content as of your last read; the edit is rejected if the file changed since",
        str_param "new_content" "The new full contents to write",
    ]

pub def ReadTool.spec : ToolSpec :=
    { name := "read", description := "Read a file's contents with line numbers.", schema := params_schema read_params }

pub def ReadTool.impl : ToolImpl :=
    { spec := ReadTool.spec, cap := Capability.read, run := read_run }

pub def WriteTool.spec : ToolSpec :=
    { name := "write", description := "Write a file's full contents.", schema := params_schema write_params }

pub def WriteTool.impl : ToolImpl :=
    { spec := WriteTool.spec, cap := Capability.write, run := write_run }

pub def EditTool.spec : ToolSpec :=
    { name := "edit", description := "Replace a file's contents, failing if it changed since last read.", schema := params_schema edit_params }

pub def EditTool.impl : ToolImpl :=
    { spec := EditTool.spec, cap := Capability.write, run := edit_run }
