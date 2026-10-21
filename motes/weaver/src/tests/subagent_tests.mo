/// The `task` subagent's surface: its spec, its read-only registry, and
/// the read-only gate it installs on the child loop.
use weaver::subagent {Subagent.spec, Subagent.system_prompt, Subagent.read_registry}
use shuttle::gate {Gate, Gate.read_only, Pick, Capability, Approval}
use shuttle::registry {ToolRegistry}
use json::json {Json}

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
