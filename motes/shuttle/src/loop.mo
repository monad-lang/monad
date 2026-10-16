/// The tool-use loop -- agent-skills.md Phases 2 and 5. Phase 2's shape
/// is unchanged (build request, send, decode, and on `tool_use_stop`
/// dispatch every `tool_use`, append ALL `tool_result`s in one message
/// before recursing -- Design 3's parallel-tool-call requirement), and
/// the sequencing is now the indexed `Agent` monad (`agent.mo`):
/// `Loop.send` is `Agent Idle Answered Turn`, dispatch is `Agent
/// Answered Executing`, so the phase order ask-then-dispatch is a
/// type-level fact, not a discipline. Phase 5 also threads the
/// accumulated `Usage` through the run (the session's `spent`), which
/// the old loop dropped on the floor.
///
/// A tool failure (the implementation's own `ResultT` erring) becomes
/// an `is_error := true` tool_result, not a short-circuit of the whole
/// loop -- the model gets to see the failure and adapt.
///
/// KNOWN GAP (Rust host only): these modules `monad check` clean, but
/// the Rust host's `lower_core_ir` path fails on files importing them
/// with `MatchTraversalMismatch { expected: [Monad], found: [mk] }` --
/// the same checker/lowering desync documented for `StateT.bind` in
/// `init/src/transformers_tests.mo`. The
/// self-hosted compiled backend runs everything; the Rust host is
/// bootstrap-only and not a verification surface for this mote.
/// VERIFIED LIVE under the SELF-HOSTED compiled backend (Phase 2:
/// `tests/ollama_e2e_tests.mo` against a real local Ollama; Phase 5:
/// `tests/mock_e2e_tests.mo`, the scripted offline loop).
use init::transformers {ResultT}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Turn, Usage}
use shuttle::provider {ProviderConfig}
use shuttle::provider {Provider.send}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use shuttle::agent {RunState, Agent, AgentIdle, AgentAnswered, AgentExecuting, AgentDone}
use shuttle::context {usage_zero, usage_add}
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
        { run, .. } =>
            ResultT.mk (do {
                let r <- ResultT.run (run id input);
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

def turn_content (m : Message) : List Content :=
    match m { { content, .. } => content }

// ── The indexed phase steps ────────────────────────────────────────────

/// Idle -> Answered: ask the model for one turn. Consumes one unit of
/// the turn budget and accumulates the turn's `Usage` into the
/// session's `spent` (Phase 5's accounting -- the old loop dropped it).
pub def Loop.send : Agent AgentIdle AgentAnswered Turn :=
    Agent.agent agent_send_step

/// The budget guard for DIRECT callers of the pub `Loop.send`: the
/// loop itself ends cleanly at a spent budget (`Loop.check_budget`
/// below) and never asks send to exceed one, so a caller driving the
/// steps by hand gets the refusal here, named.
def agent_send_step (s : RunState) : ResultT String IO (Pair RunState Turn) :=
    if s.turns_left < 1 then ResultT.mk (return (Result.err "turn cap reached"))
    else agent_send_run s

def agent_send_run (s : RunState) : ResultT String IO (Pair RunState Turn) := do {
    let specs : List ToolSpec := ToolRegistry.specs s.reg;
    let turn <- Provider.send s.session.config s.session.system_prompt specs s.session.history s.emit;
    let base : Session := s.session;
    let spent2 : Usage := usage_add s.session.spent turn.usage;
    let session2 : Session := { base with turns := s.session.turns + 1, spent := spent2 };
    let s2 : RunState := { s with session := session2, turns_left := s.turns_left - 1 };
    ResultT.mk (return (Result.ok (Pair.pair s2 turn)))
}

/// Answered -> Executing: run every `tool_use` the turn asked for.
pub def Loop.dispatch (turn : Turn) : Agent AgentAnswered AgentExecuting (List Content) :=
    Agent.agent (fn (s : RunState) => agent_dispatch_run turn s)

def agent_dispatch_run (turn : Turn) (s : RunState) : ResultT String IO (Pair RunState (List Content)) := do {
    let results <- dispatch_all s.reg (turn_content turn.message);
    ResultT.mk (return (Result.ok (Pair.pair s results)))
}

/// Executing -> Idle: append the assistant message and the one tool
/// message carrying all results, and hand control back to `send` for
/// the next model call. One tool message, never several -- Design 3.
pub def Loop.append_results (turn : Turn) (results : List Content) : Agent AgentExecuting AgentIdle Unit :=
    Agent.agent (fn (s : RunState) => agent_append_run turn results s)

def agent_append_run (turn : Turn) (results : List Content) (s : RunState) : ResultT String IO (Pair RunState Unit) := do {
    let tool_message : Message := { role := Role.tool, content := results };
    let history2 : List Message := List.append s.session.history [turn.message, tool_message];
    let base : Session := s.session;
    let session2 : Session := { base with history := history2 };
    let s2 : RunState := { s with session := session2 };
    ResultT.mk (return (Result.ok (Pair.pair s2 unit)))
}

/// Answered -> Done: append the final assistant message.
pub def Loop.finish (turn : Turn) : Agent AgentAnswered AgentDone Unit :=
    Agent.agent (fn (s : RunState) => agent_finish_run turn s)

def agent_finish_run (turn : Turn) (s : RunState) : ResultT String IO (Pair RunState Unit) := do {
    let history2 : List Message := List.append s.session.history [turn.message];
    let base : Session := s.session;
    let session2 : Session := { base with history := history2 };
    let s2 : RunState := { s with session := session2 };
    ResultT.mk (return (Result.ok (Pair.pair s2 unit)))
}

/// The value-level branch after one send: a tool turn dispatches,
/// appends every result in one message, and loops back to Idle; any
/// other stop reason appends the final assistant message and finishes.
/// The two arms agree on `Agent Answered Done Unit`, which is what
/// lets the branch live INSIDE one indexed program -- the tool arm
/// closes the recursion at the same indices it opened.
def loop_after_send (turn : Turn) : Agent AgentAnswered AgentDone Unit :=
    match turn.stop {
        StopReason.tool_use_stop =>
            Agent.bind (Loop.dispatch turn) (fn (results : List Content) => Agent.and_then (Loop.append_results turn results) Loop.iterate),
        _ => Loop.finish turn,
    }

/// Idle -> Idle: the budget check that starts every iteration.
/// `Option.some` means the budget is spent and the run must END here,
/// with the session it has.
pub def Loop.check_budget : Agent AgentIdle AgentIdle (Option Unit) :=
    Agent.agent agent_budget_step

def agent_budget_step (s : RunState) : ResultT String IO (Pair RunState (Option Unit)) :=
    if s.turns_left < 1
    then ResultT.mk (return (Result.ok (Pair.pair s (Option.some unit))))
    else ResultT.mk (return (Result.ok (Pair.pair s Option.none)))

/// Idle -> Done without a model call: the turn budget is spent. Ending
/// at the cap is a NORMAL completion -- the transcript built so far
/// (assistant turns, tool results, accumulated usage) is the run's
/// RESULT, never an error to discard, and a `--save` caller still gets
/// it. The phantom markers police the ask-then-dispatch order; this
/// hand-built `Agent.agent` step is the one phase transition the type
/// discipline does not grant to dispatch, only to the budget.
pub def Loop.cap_done : Agent AgentIdle AgentDone Unit :=
    Agent.agent (fn (s : RunState) => ResultT.mk (return (Result.ok (Pair.pair s unit))))

/// One full iteration: the budget first, then ask, then either
/// dispatch-and-loop or finish. A spent budget ends the run through
/// `cap_done` instead of erroring; the two ask-arms agree on
/// `Agent Answered Done Unit`, which is what lets the value-level
/// branch on the stop reason live INSIDE one indexed program -- the
/// tool arm loops back to Idle via `append_results`, so the recursion
/// closes at the same indices.
#[terminating]
pub def Loop.iterate : Agent AgentIdle AgentDone Unit :=
    Agent.bind Loop.check_budget (fn (capped : Option Unit) =>
        match capped {
            Option.some _ => Loop.cap_done,
            Option.none => Agent.bind Loop.send (fn (turn : Turn) => loop_after_send turn),
        })

// ── Entry points ───────────────────────────────────────────────────────

/// Build the initial run state: a fresh session over the given config
/// and history, zero turns taken, nothing spent, `emit` the live-text
/// sink every provider call streams through (`Provider.silent_emit`
/// for a caller that wants no live output).
pub def Loop.initial_state (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (emit : String -> IO Unit) : RunState :=
    let session : Session := { config := cfg, system_prompt := system, tools := ToolRegistry.specs reg, history := history, turns := 0, spent := usage_zero } in
    let st : RunState := { session := session, reg := reg, turns_left := turns_left, emit := emit } in
    st

def runstate_of_pair (p : Pair RunState Unit) : RunState :=
    match p { Pair.pair st _ => st }

/// Drive the loop from an explicit run state and return the FINAL
/// session -- transcript, accumulated usage and turn count all live
/// there, so this is both the result the caller reads and the value
/// `Session.save` checkpoints.
pub def Loop.run_state (st : RunState) : ResultT String IO Session := do {
    let p <- Agent.exec Loop.iterate st;
    let final : RunState := runstate_of_pair p;
    ResultT.mk (return (Result.ok final.session))
}

/// Drive the loop: fresh session, up to `turns_left` model calls.
pub def Loop.run (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (emit : String -> IO Unit) : ResultT String IO Session :=
    Loop.run_state (Loop.initial_state cfg reg system history turns_left emit)
