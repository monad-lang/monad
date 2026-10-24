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
/// loop -- the model gets to see the failure and adapt. A gate DENIAL
/// takes the same shape (`denied: <reason>`): the model gets to see
/// the refusal and adapt, the run never dies of an approval.
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
use shuttle::agent {RunState, Agent, AgentIdle, AgentAnswered, AgentExecuting, AgentDone, silent_sleep, silent_usage, silent_stop}
use shuttle::context {usage_zero, usage_add, Context.cap_text, Context.tool_output_max}
use shuttle::gate {Capability, Pick, Approval, Gate}
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

// ── The approval gate (weaver.md Phase 1) ───────────────────────────────
//
// Consulted before `impl.run` on every pick. A denial is an
// `is_error := true` tool_result the model can see and react to -- the
// same contract as a tool failure, deliberately NOT a loop-killing
// `Result.err`. An `Approval.always` answer is cached per capability in
// `RunState.always` (Elm state -- there is no `IORef`), so the gate is
// asked once per capability, never once per pick.

/// The pick the gate sees for one dispatch: the tool's name, its
/// capability tag, and the model's input.
def gate_pick (impl : ToolImpl) (input : Json) : Pick :=
    let p : Pick := { name := impl.spec.name, cap := impl.cap, input := input } in
    p

/// Membership in the always-cache: spelled out because `List.any`'s
/// implicit `A` does not unify in this position.
#[partial]
def cap_cached (cap : Capability) (cached : List Capability) : Bool :=
    match cached {
        List.empty => false,
        List.cons h rest => if Capability.eq cap h then true else cap_cached cap rest,
    }

/// `Approval.always` grows the cache by one capability; every other
/// answer leaves it alone.
def cache_answer (ap : Approval) (cap : Capability) (cached : List Capability) : List Capability :=
    match ap {
        Approval.always => List.cons cap cached,
        Approval.always_note _ => List.cons cap cached,
        _ => cached,
    }

/// A pick whose capability is already cached: proceeds as `once`
/// without disturbing the cache -- and without asking.
def consult_cached (cached : List Capability) : IO (Pair Approval (List Capability)) :=
    IO.pure (Pair.pair Approval.once cached)

def consult_ask (gate : Gate) (impl : ToolImpl) (input : Json) (cached : List Capability) : IO (Pair Approval (List Capability)) := do {
    let ap <- gate.ask (gate_pick impl input);
    return (Pair.pair ap (cache_answer ap impl.cap cached))
}

/// One gate consultation with the cache threaded: `Pair.pair` the
/// answer and the updated cache. The PRECHECK runs FIRST, even when the
/// capability is cached: approving `write` in manual mode must not let a
/// later switch to plan mode run writes without asking.
def consult_gate (gate : Gate) (impl : ToolImpl) (input : Json) (cached : List Capability) : IO (Pair Approval (List Capability)) := do {
    let pre <- gate.precheck (gate_pick impl input);
    match pre {
        Option.some ap => IO.pure (Pair.pair ap cached),
        Option.none =>
            if cap_cached impl.cap cached then consult_cached cached else consult_ask gate impl input cached,
    }
}

/// One gated dispatch. `run_tool`'s error contract is unchanged; the
/// gate only decides whether it is reached.
def run_gated (id : String) (impl : ToolImpl) (input : Json) (gate : Gate) (cached : List Capability) : ResultT String IO (Pair Content (List Capability)) := do {
    let pap <- ResultT.lift (consult_gate gate impl input cached);
    gate_decided id impl input pap
}

def gate_decided (id : String) (impl : ToolImpl) (input : Json) (pap : Pair Approval (List Capability)) : ResultT String IO (Pair Content (List Capability)) :=
    match pap {
        Pair.pair ap cached2 => apply_approval id impl input ap cached2,
    }

/// The denial answer: an `is_error` tool_result naming the reason, so
/// the model can react to the refusal in its next turn. `once` and
/// `always` (and a cache hit, reported as `once`) reach the impl.
def apply_approval (id : String) (impl : ToolImpl) (input : Json) (ap : Approval) (cached : List Capability) : ResultT String IO (Pair Content (List Capability)) :=
    match ap {
        Approval.deny reason =>
            ResultT.mk (return (Result.ok (Pair.pair (Content.tool_result id (String.concat "denied: " reason) true) cached))),
        Approval.once_note note => ResultT.mk (do {
            let r <- ResultT.run (run_with_cache id impl input cached);
            match r {
                Result.err e => IO.pure (Result.err e),
                Result.ok pr => match pr {
                    Pair.pair content cached2 =>
                        IO.pure (Result.ok (Pair.pair (with_note content note) cached2)),
                },
            }
        }),
        Approval.always_note note => ResultT.mk (do {
            let r <- ResultT.run (run_with_cache id impl input cached);
            match r {
                Result.err e => IO.pure (Result.err e),
                Result.ok pr => match pr {
                    Pair.pair content cached2 =>
                        IO.pure (Result.ok (Pair.pair (with_note content note) cached2)),
                },
            }
        }),
        _ => run_with_cache id impl input cached,
    }

/// Attach a human note to a tool result: the model and the transcript
/// both see it, without inventing a second message.
def with_note (c : Content) (note : String) : Content :=
    match c {
        Content.tool_result id output is_error =>
            Content.tool_result id (String.concat output (String.concat "\nnote: " note)) is_error,
        _ => c,
    }

def run_with_cache (id : String) (impl : ToolImpl) (input : Json) (cached : List Capability) : ResultT String IO (Pair Content (List Capability)) := do {
    let c <- run_tool id impl input;
    ResultT.mk (return (Result.ok (Pair.pair c cached)))
}

// ── Dispatch ────────────────────────────────────────────────────────────

def unknown_tool_result (id : String) (name : String) : Content :=
    Content.tool_result id (String.concat "unknown tool: " name) true

def content_of (p : Pair Content (List Capability)) : Content :=
    match p { Pair.pair c _ => c }

def cache_of (p : Pair Content (List Capability)) : List Capability :=
    match p { Pair.pair _ cached => cached }

def result_of (p : Pair (Option Content) (List Capability)) : Option Content :=
    match p { Pair.pair oc _ => oc }

def cache_result_of (p : Pair (Option Content) (List Capability)) : List Capability :=
    match p { Pair.pair _ cached => cached }

def dispatch_fold (r : Result String (Pair Content (List Capability))) : Result String (Pair (Option Content) (List Capability)) :=
    match r {
        Result.err e => Result.err e,
        Result.ok pc => Result.ok (Pair.pair (Option.some (content_of pc)) (cache_of pc)),
    }

def dispatch_known (id : String) (impl : ToolImpl) (input : Json) (gate : Gate) (cached : List Capability) : ResultT String IO (Pair (Option Content) (List Capability)) :=
    ResultT.mk (do {
        let r <- ResultT.run (run_gated id impl input gate cached);
        return (dispatch_fold r)
    })

def dispatch_content (reg : ToolRegistry) (gate : Gate) (cached : List Capability) (c : Content) : ResultT String IO (Pair (Option Content) (List Capability)) :=
    match c {
        Content.tool_use id name input =>
            match ToolRegistry.lookup name reg {
                Option.some impl => dispatch_known id impl input gate cached,
                Option.none =>
                    ResultT.mk (return (Result.ok (Pair.pair (Option.some (unknown_tool_result id name)) cached))),
            },
        _ => ResultT.mk (return (Result.ok (Pair.pair Option.none cached))),
    }

def cons_opt (oc : Option Content) (rest : List Content) : List Content :=
    match oc {
        Option.some c => List.cons c rest,
        Option.none => rest,
    }

def results_of (p : Pair (List Content) (List Capability)) : List Content :=
    match p { Pair.pair rs _ => rs }

def allcache_of (p : Pair (List Content) (List Capability)) : List Capability :=
    match p { Pair.pair _ cached => cached }

/// The recursion is structural in `rest` but threads the ever-growing
/// cache, so the termination checker cannot see it -- `#[terminating]`
/// for the same reason `Loop.iterate` carries it.
#[terminating]
def dispatch_tail (p : Pair (Option Content) (List Capability)) (reg : ToolRegistry) (gate : Gate) (rest : List Content) : ResultT String IO (Pair (List Content) (List Capability)) := do {
    let pt <- dispatch_all reg gate (cache_result_of p) rest;
    ResultT.mk (return (Result.ok (Pair.pair (cons_opt (result_of p) (results_of pt)) (allcache_of pt))))
}

/// Dispatch every `tool_use` in `cs`, threading the always-cache through
/// the walk (a pick's `always` answer covers a LATER pick in the same
/// turn) and returning the updated cache alongside the results.
#[partial]
pub def dispatch_all (reg : ToolRegistry) (gate : Gate) (cached : List Capability) (cs : List Content) : ResultT String IO (Pair (List Content) (List Capability)) :=
    match cs {
        List.empty => ResultT.mk (return (Result.ok (Pair.pair List.empty cached))),
        List.cons c rest => do {
            let p <- dispatch_content reg gate cached c;
            dispatch_tail p reg gate rest
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

/// The wire call, retried through the RunState's policy: `retries`
/// TOTAL attempts (1 = byte-identical to the pre-retry loop), sleeping
/// `sleep_ms` between attempts through the sleep seam, each retry
/// announced through `emit` so an interactive UI shows the wait. The
/// classification: a 4xx-status error is NOT retried (a malformed
/// request or an unknown key fails identically on every resend) except
/// 429 -- rate limiting is exactly what waiting is for; anything
/// without an `HTTP 4` marker is treated as transient.
def agent_send_run (s : RunState) : ResultT String IO (Pair RunState Turn) := do {
    let specs : List ToolSpec := ToolRegistry.specs s.reg;
    let turn <- Loop.retry_send
        (fn (_ : Unit) => Provider.send s.session.config s.session.system_prompt specs s.session.history s.emit)
        s.sleep_ms
        (if s.retries < 1 then 1 else s.retries)
        1
        2000
        s.emit;
    let base : Session := s.session;
    let spent2 : Usage := usage_add s.session.spent turn.usage;
    let session2 : Session := { base with turns := s.session.turns + 1, spent := spent2 };
    let s2 : RunState := { s with session := session2, turns_left := s.turns_left - 1 };
    // The usage hook is IO, so it runs inside the ResultT wrapper's own
    // do block (an `IO` bind in the ResultT do would not typecheck, and
    // `ResultT.lift` in a do block is the recorded compiled-backend trap).
    ResultT.mk (do {
        let _ <- s.on_usage spent2;
        return (Result.ok (Pair.pair s2 turn))
    })
}

/// The retry loop. `send` is a `Unit ->` SEAM (the eagerness lesson:
/// a naked `ResultT ... IO` value is evaluated at the call site, so a
/// retried send must be rebuilt per attempt). `retries` is the total
/// attempt budget, `attempt` the attempt being made (1-based), `delay`
/// the first sleep in ms growing by 2000 per retry. The
/// unwrap-and-rewrap shape (`ResultT.run` inside a `do`, never
/// `ResultT.lift` -- the lift-in-a-do-block shape crashes the compiled
/// backend) matches `run_tool`'s above.
#[terminating]
pub def Loop.retry_send
    (send : Unit -> ResultT String IO Turn)
    (sleep_ms : I64 -> IO Unit)
    (retries : I64)
    (attempt : I64)
    (delay : I64)
    (emit : String -> IO Unit)
    : ResultT String IO Turn :=
    ResultT.mk (do {
        let res <- ResultT.run (send unit);
        match res {
            Result.ok turn => return (Result.ok turn),
            Result.err e =>
                if Bool.not (attempt < retries) || Bool.not (retry_worth_error e)
                then return (Result.err e)
                else do {
                    let _ <- sleep_ms delay;
                    let _ <- emit (String.concat "retrying ("
                        (String.concat (I64.to_string (attempt + 1))
                        (String.concat "/" (String.concat (I64.to_string retries)
                        (String.concat "): " (String.concat e "\n"))))));
                    let res2 <- ResultT.run (Loop.retry_send send sleep_ms retries (attempt + 1) (delay + 2000) emit);
                    return res2
                }
        }
    })

/// Whether a wire error is worth a resend: the clients surface the HTTP
/// status in their error text (`openai: HTTP 429: ...`). A `4`xx is a
/// request error and fails identically on every resend -- EXCEPT 429,
/// rate limiting, which is exactly what waiting is for. Anything
/// without an `HTTP 4` marker is treated as transient. The scan is
/// bounded to the status MARKER's own neighborhood (the first bytes):
/// a 5xx whose body happens to mention "HTTP 4" or a 4xx whose body
/// mentions "429" must not flip the classification, and an
/// unbounded scan over a large gateway body is its own pathology.
#[terminating]
def retry_worth_error (e : String) : Bool :=
    let head : String := String.slice e 0 24 in
    if Bool.and (retry_contains head 0 "HTTP 4") (Bool.not (retry_contains head 0 "429"))
    then false
    else true

/// The bounded contains: at most scan_to_scan... `i` runs to
/// `String.length head` only, so this is linear in the marker's
/// neighborhood, not in the error body.
#[terminating]
def retry_contains (s : String) (i : I64) (needle : String) : Bool :=
    if String.starts_with needle (String.drop i s)
    then true
    else if i < String.length s then retry_contains s (i + 1) needle
    else false

/// Answered -> Executing: run every `tool_use` the turn asked for.
pub def Loop.dispatch (turn : Turn) : Agent AgentAnswered AgentExecuting (List Content) :=
    Agent.agent (fn (s : RunState) => agent_dispatch_run turn s)

/// Out-of-band activity lines ride the provider's `emit` sink with this
/// prefix. The leading control byte means model text can never forge
/// one; the UIs filter the prefix out of the transcript and route it to
/// their own live-status surface.
pub def activity_prefix : String := "\u{1}activity\u{2}"

pub def activity_start (name : String) : String :=
    String.concat activity_prefix (String.concat "start\u{2}" name)

pub def activity_end (name : String) : String :=
    String.concat activity_prefix (String.concat "end\u{2}" name)

/// The `tool_use` names in order, skipping non-tool content.
#[partial]
def tool_names (cs : List Content) : List String :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                Content.tool_use _ name _ => List.cons name (tool_names rest),
                _ => tool_names rest,
            },
    }

/// Clamp one tool result's text to the shared cap, so any tool (read,
/// grep, glob, an MCP proxy) can contribute at most one bounded result
/// to the history.
def cap_content (c : Content) : Content :=
    match c {
        Content.tool_result id output is_error => Content.tool_result id (Context.cap_text output Context.tool_output_max) is_error,
        _ => c,
    }

#[partial]
def cap_contents (cs : List Content) : List Content :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.cons (cap_content c) (cap_contents rest),
    }

#[partial]
def emit_each (emit : String -> IO Unit) (lines : List String) : IO Unit :=
    match lines {
        List.empty => IO.pure unit,
        List.cons l rest => do {
            let _ <- emit l;
            emit_each emit rest
        },
    }

/// One start line per call, the whole dispatch (the gate may prompt in
/// the middle), then one end line per call. IO and ResultT stay in
/// separate do blocks: an `IO` bind inside a ResultT do does not
/// typecheck, and `ResultT.lift` there is a recorded compiled-backend
/// trap.
def agent_dispatch_run (turn : Turn) (s : RunState) : ResultT String IO (Pair RunState (List Content)) :=
    ResultT.mk (do {
        let names : List String := tool_names (turn_content turn.message);
        let starts : List String := List.map (fn (n : String) => activity_start n) names;
        let _ <- emit_each s.emit starts;
        let r <- ResultT.run (dispatch_all s.reg s.gate s.always (turn_content turn.message));
        match r {
            Result.err e => return (Result.err e),
            Result.ok p => do {
                let ends : List String := List.map (fn (n : String) => activity_end n) names;
                let _ <- emit_each s.emit ends;
                let capped : List Content := cap_contents (results_of p);
                return (Result.ok (Pair.pair (state_with_always s (allcache_of p)) capped))
            }
        }
    })

def state_with_always (s : RunState) (cached : List Capability) : RunState :=
    let s2 : RunState := { s with always := cached } in
    s2

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

// ── cooperative stop ───────────────────────────────────────────────────
//
// The UI can request a stop between steps. It is a NORMAL partial
// completion (`stopped := true`, Result.ok), never an error: the
// session built so far is the result. The check runs before every model
// call and after one, before any tool dispatches -- a stop never runs a
// tool, and a tool_use turn gets one synthetic error result per call so
// the appended history stays protocol-valid.

def mark_stopped (s : RunState) : RunState :=
    let s2 : RunState := { s with stopped := true } in
    s2

/// One synthetic error result per `tool_use`, in order, skipping
/// non-tool content.
#[partial]
def stop_tool_results (cs : List Content) : List Content :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                Content.tool_use id _ _ => List.cons (Content.tool_result id "stopped by user" true) (stop_tool_results rest),
                _ => stop_tool_results rest,
            },
    }

/// The synthetic results a stop needs: only a tool_use turn that asked
/// for at least one tool gets a results message.
#[partial]
def stop_results (turn : Turn) : Option (List Content) :=
    match turn.stop {
        StopReason.tool_use_stop =>
            let rs : List Content := stop_tool_results (turn_content turn.message) in
            match rs {
                List.empty => Option.none,
                List.cons _ _ => Option.some rs,
            },
        _ => Option.none,
    }

/// The partial session a stopped turn keeps: the assistant message, plus
/// the synthetic results message when tools were preempted.
def stopped_session (s : RunState) (turn : Turn) (results : Option (List Content)) : Session :=
    let base : Session := s.session in
    match results {
        Option.none =>
            let history2 : List Message := List.append base.history [turn.message] in
            let out : Session := { base with history := history2 } in
            out,
        Option.some rs =>
            let tool_message : Message := { role := Role.tool, content := rs } in
            let history2 : List Message := List.append base.history [turn.message, tool_message] in
            let out : Session := { base with history := history2 } in
            out,
    }

def agent_stop_step (s : RunState) : ResultT String IO (Pair RunState (Option Unit)) :=
    ResultT.mk (do {
        let stop <- s.should_stop unit;
        let out : Pair RunState (Option Unit) :=
            if stop then Pair.pair (mark_stopped s) (Option.some unit) else Pair.pair s Option.none;
        return (Result.ok out);
    })

def agent_stop_after_run (turn : Turn) (s : RunState) : ResultT String IO (Pair RunState Unit) :=
    let session2 : Session := stopped_session s turn (stop_results turn) in
    let s1 : RunState := mark_stopped s in
    let s2 : RunState := { s1 with session := session2 } in
    ResultT.mk (return (Result.ok (Pair.pair s2 unit)))

/// Idle -> Idle: the stop check that precedes every model call. It
/// consumes no budget.
pub def Loop.check_stop : Agent AgentIdle AgentIdle (Option Unit) :=
    Agent.agent agent_stop_step

/// Idle -> Done without a model call: stop was requested before the send.
pub def Loop.stop_done : Agent AgentIdle AgentDone Unit :=
    Agent.agent (fn (s : RunState) => ResultT.mk (return (Result.ok (Pair.pair (mark_stopped s) unit))))

/// Answered -> Answered: the stop check after a send, before dispatch.
pub def Loop.check_stop_answered : Agent AgentAnswered AgentAnswered (Option Unit) :=
    Agent.agent agent_stop_step

/// Answered -> Done: keep the assistant message, synthesize an error
/// result for every preempted tool, and end normally with `stopped`.
pub def Loop.stop_after_send (turn : Turn) : Agent AgentAnswered AgentDone Unit :=
    Agent.agent (fn (s : RunState) => agent_stop_after_run turn s)

/// The existing dispatch-or-finish branch, extracted so the stop match
/// stays one level deep (the self-hosted parser's nested-match rule).
#[terminating]
def loop_dispatch_or_finish (turn : Turn) : Agent AgentAnswered AgentDone Unit :=
    match turn.stop {
        StopReason.tool_use_stop =>
            Agent.bind (Loop.dispatch turn) (fn (results : List Content) => Agent.and_then (Loop.append_results turn results) Loop.iterate),
        _ => Loop.finish turn,
    }

/// The value-level branch after one send: the stop check first, then the
/// usual dispatch-or-finish.
#[terminating]
def loop_after_send (turn : Turn) : Agent AgentAnswered AgentDone Unit :=
    Agent.bind Loop.check_stop_answered (fn (stopping : Option Unit) =>
        match stopping {
            Option.some _ => Loop.stop_after_send turn,
            Option.none => loop_dispatch_or_finish turn,
        })

/// The budget's clear path: the stop check, then the send.
#[terminating]
def loop_uncapped : Agent AgentIdle AgentDone Unit :=
    Agent.bind Loop.check_stop (fn (stopping : Option Unit) =>
        match stopping {
            Option.some _ => Loop.stop_done,
            Option.none => Agent.bind Loop.send (fn (turn : Turn) => loop_after_send turn),
        })

/// One full iteration: the budget first, then ask, then either
/// dispatch-and-loop or finish. A spent budget ends the run through
/// `cap_done` instead of erroring; the two ask-arms agree on
/// `Agent Answered Done Unit`, which is what lets the value-level
/// branch on the stop reason live INSIDE one indexed program -- the
/// tool arm loops back to Idle via `append_results`, so the recursion
/// closes at the same indices. The stop checks sit at the same
/// boundaries; both end normally with the partial session.
#[terminating]
pub def Loop.iterate : Agent AgentIdle AgentDone Unit :=
    Agent.bind Loop.check_budget (fn (capped : Option Unit) =>
        match capped {
            Option.some _ => Loop.cap_done,
            Option.none => loop_uncapped,
        })

// ── Entry points ───────────────────────────────────────────────────────

/// Build the initial run state: a fresh session over the given config
/// and history, zero turns taken, nothing spent, `emit` the live-text
/// sink every provider call streams through (`Provider.silent_emit`
/// for a caller that wants no live output), and `gate` the approval
/// seam consulted before every tool run (`Gate.auto` for a caller
/// that wants no gate -- shuttle's own CLI and tests).
pub def Loop.initial_state (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (emit : String -> IO Unit) (gate : Gate) : RunState :=
    let session : Session := { config := cfg, system_prompt := system, tools := ToolRegistry.specs reg, history := history, turns := 0, spent := usage_zero } in
    let st : RunState := { session := session, reg := reg, turns_left := turns_left, emit := emit, gate := gate, always := List.empty, retries := 1, sleep_ms := silent_sleep, on_usage := silent_usage, should_stop := silent_stop, stopped := false } in
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
pub def Loop.run (cfg : ProviderConfig) (reg : ToolRegistry) (system : String) (history : List Message) (turns_left : I64) (emit : String -> IO Unit) (gate : Gate) : ResultT String IO Session :=
    Loop.run_state (Loop.initial_state cfg reg system history turns_left emit gate)
