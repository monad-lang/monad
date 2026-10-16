/// The approval-gate seam -- weaver.md Phase 1: the capability
/// vocabulary a tool is tagged with, the payload one gate consultation
/// sees, and the gate itself. The loop (`loop.mo`) consults the gate
/// before every `impl.run`; Weaver implements the interactive gate, and
/// `Gate.auto` is the headless default that keeps shuttle's CLI and
/// tests ungated.
///
/// Lives in its own file for the same reason `message_types.mo` is
/// split from `message.mo` and `registry.mo` from `tool.mo`:
/// `tool.mo` carries the `derive_json_*` (`reflect_type_info!`)
/// invocations for `ToolSpec`, and a top-level function in the same
/// file as a `reflect_type_info!` invocation that references one of
/// that file's OWN constructors fails macro-expansion's capture pass
/// with `unbound variable` -- `Gate.auto`, answering `Approval.once`,
/// is exactly that shape. `tool.mo` imports `Capability` from here.
use json::json {Json}

/// What a tool may do -- the axis every approval policy decides on.
/// `read` is inspection (file read, grep, glob); `write` is mutation of
/// the workspace (file write, edit); `exec` is arbitrary code (shell,
/// an MCP proxy -- a server's catalogue is arbitrary code, so `exec`
/// is the conservative tag); `net` is reserved for a future
/// network-restricted tool family.
pub type Capability {
    read,
    write,
    exec,
    net
}

/// Structural equality. The prelude ships no generic `Eq` over user
/// sum types, and the loop's always-cache membership test needs it.
pub def Capability.eq (a : Capability) (b : Capability) : Bool :=
    match a {
        Capability.read => match b { Capability.read => true, _ => false },
        Capability.write => match b { Capability.write => true, _ => false },
        Capability.exec => match b { Capability.exec => true, _ => false },
        Capability.net => match b { Capability.net => true, _ => false },
    }

/// The payload one gate consultation sees. Named `Pick` -- one pass of
/// the shuttle -- because `ToolCall` already exists
/// (`motes/openai/src/tool.mo`), and whole-program type-name collisions
/// are a recorded shuttle Phase 2 lesson (`Usage` vs `ApiUsage`).
pub struct Pick {
    name : String,
    cap : Capability,
    input : Json,
}

/// The gate's answer: `once` runs this pick, `always` runs this pick
/// and every later pick of the same capability, `deny` runs nothing
/// and tells the model why.
pub type Approval {
    once,
    always,
    deny (reason : String),
}

/// The gate: one approval decision per tool pick. `IO` because the
/// interactive implementation prints and reads; the loop consults it
/// before `impl.run` and never after.
pub struct Gate {
    ask : Pick -> IO Approval,
}

/// The headless default: every pick proceeds, nothing is cached.
/// shuttle's own CLI and tests pass this, so their behavior is
/// byte-identical to the pre-gate loop.
pub def Gate.auto : Gate :=
    { ask := fn (_ : Pick) => IO.pure Approval.once }
