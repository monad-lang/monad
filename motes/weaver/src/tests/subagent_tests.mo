/// The `task` subagent's surface: its spec, its read-only registry, and
/// the read-only gate it installs on the child loop.
use weaver::subagent {Subagent.spec, Subagent.system_prompt, Subagent.read_registry, Subagent.task_tool}
use shuttle::gate {Gate, Gate.read_only, Pick, Capability, Approval}
use shuttle::registry {ToolRegistry}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::message {Message, Turn}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::context {usage_zero}
use shuttle::agent {silent_stop}
use init::transformers {ResultT}
use json::json {
    Json, Json.to_string, Json.make_object, Json.make_str, Json.make_num_int, Json.make_array,
}
use std::map {Map, BTreeMap}
use std::io {IO.write_file}
use std::path {Path}
use std::process {process_id, exec_cmd}

def pick (name : String) (cap : Capability) : Pick :=
    { name := name, cap := cap, input := Json.null }

def has (name : String) : Bool :=
    match ToolRegistry.lookup name Subagent.read_registry {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_task_spec_names_the_tool : Bool :=
    let spec := Subagent.spec in
    spec.name == "task" && Bool.not (String.is_empty spec.description)

#[test]
def test_system_prompt_is_read_only : Bool :=
    String.contains Subagent.system_prompt "read-only"

#[test]
def test_read_registry_is_the_read_side : Bool :=
    has "read" && has "grep" && has "glob"
        && Bool.not (has "write") && Bool.not (has "edit") && Bool.not (has "shell") && Bool.not (has "task")

#[test]
def test_read_only_precheck_denies_writes : IO Bool := do {
    let g := Gate.read_only;
    let wr <- g.precheck (pick "write" Capability.write);
    let rd <- g.precheck (pick "read" Capability.read);
    return ((match wr { Option.some _ => true, Option.none => false })
        && (match rd { Option.none => true, Option.some _ => false }))
}

#[test]
def test_read_only_ask_denies_non_reads : IO Bool := do {
    let g := Gate.read_only;
    let ap <- g.ask (pick "shell" Capability.exec);
    return (match ap { Approval.deny _ => true, _ => false })
}


// ── a child loop against the scripted wire ─────────────────────────────

def mock_cfg : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock, thinking := false }

def script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat (I64.to_string process_id) ".json")

def child_turn : Turn :=
    { message := { role := Role.assistant, content := [Content.text "CHILD PLAN"] }, usage := usage_zero, stop := StopReason.end_turn }

def task_input : Json :=
    Json.make_object (Map.insert "prompt" (Json.make_str "plan it")
        (Map.insert "max_turns" (Json.make_num_int 4) BTreeMap.empty))

/// The child's history starts at zero assistant messages, so the mock's
/// first scripted turn is its plan.
#[test]
def test_task_tool_runs_a_child_loop : IO Bool := do {
    let _ <- IO.write_file (Path.path script_path) (Json.to_string (Json.make_array [Turn.serialize_json child_turn]));
    let tool := Subagent.task_tool mock_cfg Option.none Option.none silent_stop;
    let r <- ResultT.run (tool.run "c1" task_input);
    let _ <- exec_cmd "rm" ["-f", script_path];
    match r {
        Result.err _ => IO.pure false,
        Result.ok c =>
            let content : Content := c in
            match content {
                Content.tool_result _ out is_err =>
                    IO.pure (Bool.not is_err && String.contains out "CHILD PLAN"
                        && String.contains out "[subagent turns=1"),
                _ => IO.pure false,
            },
    }
}
