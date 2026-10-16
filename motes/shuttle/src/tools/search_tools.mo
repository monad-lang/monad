/// `GrepTool`/`GlobTool`'s `ToolSpec`/`ToolImpl` values -- split from
/// `search.mo` for the same reason `file_tools.mo` is split from
/// `file.mo`.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::tools::search {grep_run, glob_run}
use json::json {Json}

pub def GrepTool.spec : ToolSpec :=
    { name := "grep", description := "Search file contents recursively for a pattern.", schema := Json.null }

pub def GrepTool.impl : ToolImpl :=
    { spec := GrepTool.spec, cap := Capability.read, run := grep_run }

pub def GlobTool.spec : ToolSpec :=
    { name := "glob", description := "Find files by name pattern.", schema := Json.null }

pub def GlobTool.impl : ToolImpl :=
    { spec := GlobTool.spec, cap := Capability.read, run := glob_run }
