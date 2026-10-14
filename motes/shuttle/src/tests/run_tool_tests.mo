/// Pins review B1: the tool_result a dispatched tool returns must echo
/// the MODEL's `tool_use` id, not the tool's registration name -- both
/// wires map `Content.tool_result`'s id straight to the wire's
/// `tool_use_id`/`tool_call_id`, and both APIs validate the pairing
/// against the assistant turn, so a hardcoded "shell" is a 400 on the
/// next request. `ToolImpl.run` taking the id first (and the impls
/// being registered eta-reduced) is what makes the echo reach the wire.
///
/// Imports `shuttle::loop`, so this file inherits the Rust-host
/// lowering gap (`loop.mo`'s KNOWN GAP header) and runs self-hosted
/// only -- the same containment the presets/e2e test files practice.
use shuttle::loop {run_tool}
use shuttle::tool {ToolImpl}
use shuttle::tools::shell_tools {ShellTool.impl}
use shuttle::tools::shell_args {ShellArgs}
use shuttle::message_types {Content}
use init::transformers {ResultT}

#[test]
def test_run_tool_echoes_the_tool_use_id : IO Bool := do {
    let args : ShellArgs := { command := "echo id-echo" };
    let r <- ResultT.run (run_tool "toolu_123" ShellTool.impl (ShellArgs.serialize_json args));
    return (match r {
        Result.err _ => false,
        Result.ok c =>
            match c {
                Content.tool_result id _ _ => String.beq id "toolu_123",
                _ => false,
            },
    })
}
