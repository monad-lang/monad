/// The tool-use loop -- agent-skills.md Phase 2: build request, send,
/// decode, and on `tool_use_stop` dispatch every `tool_use` and append
/// ALL `tool_result`s in one message before recursing (Design 3's
/// parallel-tool-call requirement: splitting them across messages is
/// accepted by providers and silently degrades parallel tool calling).
/// `ResultT` throughout -- real do-notation, not the continuation-chain
/// style `motes/moose/src/client.mo` uses by hand.
///
/// KNOWN GAP (Rust host only): `dispatch_all`/`Loop.run` `monad check`
/// clean (0 errors), but calling `dispatch_all` from any file outside
/// this one -- even the trivial empty-list base case, with no tool
/// actually dispatched -- fails at LOWERING on the RUST host with
/// `MatchTraversalMismatch { expected: [Monad], found: [mk] }`, the
/// same class of checker/lowering desync documented for `StateT.bind`
/// (`init/src/transformers_tests.mo`) and probed for `ResultT`/
/// `OptionT` (`plans/implementations/agent-skills.md`). Unlike those,
/// no split-`def`/rename mitigation found here closed it -- it
/// reproduces even with the dispatch target empty and every struct
/// literal bound through an annotated `let` first.
/// NARROWER THAN IT READS, in the other direction (probed 2026-10-14):
/// the mismatch is a property of IMPORTING these modules, not of any
/// cross-file CALL -- a test file whose whole body is
/// `String.beq (I64.to_string 3) "3"` fails identically with ONLY
/// `use shuttle::loop {Loop.run}` present, and the same trivial body
/// fails identically with ONLY `use shuttle::provider
/// {ProviderConfig}` present. So `provider.mo` carries its own
/// instance of the same desync, independent of this file, and every
/// test importing either module (presets_tests.mo, all three e2e
/// files) inherits the failure. The Rust host therefore cannot run
/// ANY of those files; the self-hosted compiled backend runs them all.
/// VERIFIED LIVE under the SELF-HOSTED compiled backend (2026-10-13,
/// `tests/ollama_e2e_tests.mo` with `MONAD_SHUTTLE_OLLAMA_TESTS=1`
/// against a real local Ollama, rung-1 `monad` binary): tool_use ->
/// `run_tool` read -> tool_result -> final answer containing the
/// fixture sentinel, 4 turns. The loop itself is correct; only the
/// Rust host's `lower_core_ir` path cannot compile a cross-file caller.
use init::transformers {ResultT}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Turn}
use shuttle::provider {ProviderConfig}
use shuttle::provider {Provider.send}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::registry {ToolRegistry}
use json::json {Json}

/// A tool failure (the implementation's own `ResultT` erring) becomes
/// an `is_error := true` tool_result, not a short-circuit of the whole
/// loop -- the model gets to see the failure and adapt, the same way
/// `agent-skills.md`'s "non-recoverable tool error" stop condition is
/// the EXCEPTION, not the default. `ResultT.run` + `IO`'s own `Monad`
/// instance un-wraps and re-wraps the inner `Result` by hand for
/// exactly that reason: this is the one place a tool error must NOT
/// propagate through `ResultT`'s own short-circuiting bind.
def run_tool (id : String) (impl : ToolImpl) (input : Json) : ResultT String IO Content :=
    match impl {
        ToolImpl.mk spec run =>
            ResultT.mk (do {
                let r <- ResultT.run (run input);
                return (Result.ok (match r {
                    Result.ok content => content,
                    Result.err msg => Content.tool_result id msg true,
                }))
            })
    }

def dispatch_content (reg : ToolRegistry) (c : Content) : ResultT String IO (Option Content) :=
    match c {
        Content.tool_use id name input =>
            match ToolRegistry.lookup name reg {
                Option.some impl =>
                    ResultT.mk (do {
                        let r <- ResultT.run (run_tool id impl input);
                        return (match r {
                            Result.ok content => Result.ok (Option.some content),
                            Result.err e => Result.err e,
                        })
                    }),
                Option.none =>
                    ResultT.mk (return (Result.ok (Option.some (Content.tool_result id (String.concat "unknown tool: " name) true)))),
            },
        _ => ResultT.mk (return (Result.ok Option.none)),
    }

#[partial]
pub def dispatch_all (reg : ToolRegistry) (cs : List Content) : ResultT String IO (List Content) :=
    match cs {
        List.empty => ResultT.mk (return (Result.ok List.empty)),
        List.cons c rest => do {
            let maybe_result <- dispatch_content reg c;
            let tail_results <- dispatch_all reg rest;
            ResultT.mk (return (Result.ok (match maybe_result {
                Option.some r => List.cons r tail_results,
                Option.none => tail_results,
            })))
        }
    }

#[terminating]
def continue_after_tools (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (asst_message : Message) (tool_content : List Content) : ResultT String IO (List Message) :=
    let tool_message : Message := { role := Role.tool, content := tool_content } in
    let next_history := List.append history (List.cons asst_message (List.cons tool_message List.empty)) in
    Loop.run cfg reg system next_history (turns_left - 1)

def finish (history : List Message) (asst_message : Message) : ResultT String IO (List Message) :=
    ResultT.mk (return (Result.ok (List.append history (List.cons asst_message List.empty))))

def handle_turn (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (turn : Turn) : ResultT String IO (List Message) :=
    match turn {
        Turn.mk asst_message usage stop =>
            match stop {
                StopReason.tool_use_stop => do {
                    let tool_content <- dispatch_all reg (turn_content asst_message);
                    continue_after_tools cfg reg system history turns_left asst_message tool_content
                },
                _ => finish history asst_message,
            }
    }

def turn_content (m : Message) : List Content :=
    match m { Message.mk role content => content }

#[terminating]
pub def Loop.run (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) : ResultT String IO (List Message) :=
    if turns_left < 1 then
        ResultT.mk (return (Result.err "turn cap reached"))
    else do {
        let specs : List ToolSpec := ToolRegistry.specs reg;
        let turn <- Provider.send cfg system specs history;
        handle_turn cfg reg system history turns_left turn
    }
