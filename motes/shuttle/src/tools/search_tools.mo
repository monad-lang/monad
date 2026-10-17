/// `GrepTool`/`GlobTool`'s `ToolSpec`/`ToolImpl` values -- split from
/// `search.mo` for the same reason `file_tools.mo` is split from
/// `file.mo`.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::tools::search {grep_run, glob_run}
use shuttle::tools::file_tools {params_schema, str_param}
use json::json {Json}

/// Both tools declare their `{pattern, path}` arguments for real:
/// `schema := Json.null` sends `"parameters":null`, which lenient
/// servers tolerate but strict ones refuse -- Mistral's pydantic
/// validation (measured live 2026-10-18) requires `parameters` to be
/// a dict and 422s the whole request over a null one. The declared
/// keys are also the model's contract: with `Json.null` it guesses
/// argument names (live-verified against Ollama, see `file_tools.mo`).

def grep_params : List (Pair String Json) :=
    [str_param "pattern" "The text pattern to search for", str_param "path" "Absolute path of the file or directory to search"]

pub def GrepTool.spec : ToolSpec :=
    { name := "grep", description := "Search file contents recursively for a pattern.", schema := params_schema grep_params }

pub def GrepTool.impl : ToolImpl :=
    { spec := GrepTool.spec, cap := Capability.read, run := grep_run }

def glob_params : List (Pair String Json) :=
    [str_param "pattern" "Glob pattern for file names", str_param "path" "Absolute path of the directory to search"]

pub def GlobTool.spec : ToolSpec :=
    { name := "glob", description := "Find files by name pattern.", schema := params_schema glob_params }

pub def GlobTool.impl : ToolImpl :=
    { spec := GlobTool.spec, cap := Capability.read, run := glob_run }
