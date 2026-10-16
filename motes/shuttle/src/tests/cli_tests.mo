/// Pure tests for the CLI surface in `src/main.mo`: argument parsing,
/// plan validation (the resume/task rules, provider/model overrides)
/// and the MCP collision walk. Everything here is value-level -- the
/// IO paths (mount, run, resume) are covered by the mock e2e file.
use shuttle::main {parse_args, plan_of, collision_walk, RunPlan}
use mcp_client::protocol {McpTool}
use json::json {Json}

def plan_of_args (args : List String) : Result String RunPlan :=
    plan_of (parse_args args)

/// `--resume` with no new task is a legitimate "keep going": the plan
/// validates with the resume path set and an empty task.
#[test]
def test_resume_without_task_is_a_valid_plan : Bool :=
    match plan_of_args ["--resume", "s.json"] {
        Result.err _ => false,
        Result.ok p => p.resume == "s.json" && String.is_empty p.task,
    }

/// Without `--resume` a missing task is the usage error, not a run.
#[test]
def test_fresh_run_without_task_is_an_error : Bool :=
    match plan_of_args [] {
        Result.err e => String.contains e "usage:",
        Result.ok _ => false,
    }

/// An explicit `--provider` reaches the plan (and the config it
/// resolves to), with the provider's own model default applied.
#[test]
def test_explicit_provider_overrides_the_default : Bool :=
    match plan_of_args ["--provider", "mistral", "do something"] {
        Result.err _ => false,
        Result.ok p => p.provider == "mistral" && p.cfg.model == "mistral-large-latest",
    }

/// A `--`-token nothing consumed is an unknown flag, named as such --
/// not "unexpected extra argument" pointing at the wrong token.
#[test]
def test_unknown_flag_is_named : Bool :=
    match plan_of_args ["--strream"] {
        Result.err e => String.contains e "unknown flag: --strream",
        Result.ok _ => false,
    }

/// Every extra positional is reported, comma-separated -- one error
/// line naming them all, not just the first.
#[test]
def test_all_extras_are_named : Bool :=
    match plan_of_args ["the task", "x1", "x2"] {
        Result.err e =>
            String.contains e "unexpected extra argument: x1" && String.contains e "x2",
        Result.ok _ => false,
    }

/// The collision walk flags a mount tool whose name is already taken,
/// and in mount order. A duplicate WITHIN one catalogue is flagged too
/// (each tool joins the taken set as the walk passes it).
def mcp_tool (name : String) : McpTool :=
    { name := name, description := "test", schema := Json.make_null }

#[test]
def test_collision_walk_flags_taken_and_intra_mount_names : Bool :=
    match collision_walk ["read"] [mcp_tool "grep", mcp_tool "read", mcp_tool "grep"] {
        List.empty => false,
        List.cons h t => h == "read" && match t {
            List.empty => false,
            List.cons h2 _ => h2 == "grep",
        },
    }
