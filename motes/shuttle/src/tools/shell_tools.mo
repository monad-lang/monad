/// `ShellTool`'s `ToolSpec`/`ToolImpl` values -- split from `shell.mo` for
/// the same reason `file_tools.mo` is split from `file.mo`: a bare
/// `{ field := val }` struct literal at the top level of a file that ALSO
/// has a `reflect_type_info!` invocation (`shell.mo` derives `ShellArgs`)
/// fails macro-expansion's capture pass with "cannot infer the type of
/// `{ .. }`".
///
/// The schema helpers duplicate `file_tools.mo`'s rather than importing
/// them: they are package-private there (the mote has no shared
/// "schema_util" module, and adding one for three copies of a 5-line
/// helper is not worth a new module edge).
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::tools::shell {shell_run}
use json::json {Json}
use std::map {BTreeMap}

/// A JSON-Schema object for one string parameter. The implementation
/// deserializes its arguments via `ShellArgs` (`shell_args.mo`), so the
/// schema must declare exactly those keys -- with `schema := Json.null`
/// the model has no contract to follow and guesses (live-verified against
/// Ollama for the file tools: `file_path` instead of `path`).
def str_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "string") (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

/// `{"type":"object","properties":{...},"required":[...]}` for a flat
/// all-string-parameters tool.
def params_schema (params : List (Pair String Json)) : Json :=
    let props := Json.make_object (params_to_map params BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object") (Map.insert "properties" props (Map.insert "required" (Json.make_array (List.map pair_fst params)) BTreeMap.empty)))

#[partial]
def params_to_map (params : List (Pair String Json)) (acc : BTreeMap String Json) : BTreeMap String Json :=
    match params {
        List.empty => acc,
        List.cons p rest => match p { Pair.pair k v => params_to_map rest (Map.insert k v acc) },
    }

def pair_fst (p : Pair String Json) : Json := Json.make_str (match p { Pair.pair k _ => k })

def shell_params : List (Pair String Json) :=
    [str_param "command" "The shell command to execute. stdout and stderr are merged; output beyond 200 lines is truncated and the command killed."]

pub def ShellTool.spec : ToolSpec :=
    { name := "shell", description := "Run a shell command and return its merged output.", schema := params_schema shell_params }

pub def ShellTool.impl : ToolImpl :=
    { spec := ShellTool.spec, run := shell_run }
