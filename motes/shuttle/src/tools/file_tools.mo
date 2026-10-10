/// `ReadTool`/`WriteTool`/`EditTool`'s `ToolSpec`/`ToolImpl` values --
/// split from `file.mo` for the same reason `message_types.mo` is
/// split from `message.mo`: a bare `{ field := val }` struct literal
/// at the top level of a file that ALSO has a `reflect_type_info!`
/// invocation (`file.mo` derives `ReadArgs`/`WriteArgs`/`EditArgs`)
/// fails macro-expansion's capture pass with "cannot infer the type
/// of `{ .. }`", even with an explicit `def x : T := { .. }`
/// annotation right there.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::tools::file {read_run, write_run, edit_run}
use json::json {Json}

pub def ReadTool.spec : ToolSpec :=
    { name := "read", description := "Read a file's contents with line numbers.", schema := Json.null }

pub def ReadTool.impl : ToolImpl :=
    { spec := ReadTool.spec, run := read_run "read" }

pub def WriteTool.spec : ToolSpec :=
    { name := "write", description := "Write a file's full contents.", schema := Json.null }

pub def WriteTool.impl : ToolImpl :=
    { spec := WriteTool.spec, run := write_run "write" }

pub def EditTool.spec : ToolSpec :=
    { name := "edit", description := "Replace a file's contents, failing if it changed since last read.", schema := Json.null }

pub def EditTool.impl : ToolImpl :=
    { spec := EditTool.spec, run := edit_run "edit" }
