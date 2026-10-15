/// The indexed agent monad -- agent-skills.md Design 7 (Phase 5). The
/// loop's phases are phantom type markers (`AgentIdle` etc.), and the
/// phase transitions are typed steps: `Loop.send` is `Agent Idle
/// Answered Turn`, dispatch is `Agent Answered Executing _`, so
/// "dispatch tools without having asked the model" does not type-check.
///
/// Four non-optional workarounds, all proven by
/// `examples/indexed_monads.mo` and plugin-framework.md's Current
/// Verified State D, are baked in: (1) the phase indices are phantom
/// TYPE MARKERS, not an enum -- a `LoomState`-style enum is a kind
/// error; (2) the full `IndexedMonad` class is instantiated with all
/// five methods; (3) do-notation at equal indices needs a HAND-WRITTEN
/// `Monad (Agent I I)` instance because the prelude's generic bridge
/// has a variable head and never dispatches; (4) every do-block lives
/// in its own def.
///
/// `Agent` wraps `RunState -> ResultT String IO (Pair RunState A)`: an
/// indexed state monad over the loop's own error type, so a provider
/// or tool failure propagates exactly the way the Phase 2 `ResultT`
/// loop's did. `RunState` (not `Session`) is the state because the
/// registry is closures and never serializes; the session inside it
/// is the checkpointable half.
use init::transformers {ResultT}
use shuttle::session {Session}
use shuttle::registry {ToolRegistry}

// The protocol's phantom phase markers.
type AgentIdle {}
type AgentAnswered {}
type AgentExecuting {}
type AgentDone {}

/// Everything a running loop carries: the serializable `Session`, the
/// tool registry, the remaining turn budget, and the live-text sink.
/// Registry and `emit` are closures -- checkpoint the session, never
/// this -- and `emit` is never read by the loop's own logic, only
/// handed to the provider, so the session codec is untouched.
pub struct RunState {
    session : Session,
    reg : ToolRegistry,
    turns_left : I64,
    emit : String -> IO Unit,
}

/// One agent step from phase `I` to phase `J` producing `A`.
pub type Agent (I : Type) (J : Type) (A : Type) {
    agent (run : RunState -> ResultT String IO (Pair RunState A))
}

/// Run one step against a state -- the only way to observe an `Agent`.
pub def Agent.exec (a : Agent I J A) (s : RunState) : ResultT String IO (Pair RunState A) :=
    match a { agent run => run s }

pub def Agent.pure {I : Type} {A : Type} (a : A) : Agent I I A :=
    Agent.agent (fn (s : RunState) => ResultT.mk (return (Result.ok (Pair.pair s a))))

def agent_apply {J : Type} {K : Type} {A : Type} {B : Type} (f : A -> Agent J K B) (p : Pair RunState A) : ResultT String IO (Pair RunState B) :=
    match p {
        Pair.pair st v => Agent.exec (f v) st,
    }

/// Each do-block in its own def (workaround 4): the only bind in this
/// file runs over `ResultT`, a concrete head the checker dispatches
/// reliably -- the shape `loop.mo`'s own bodies already use.
def agent_bind_run {I : Type} {J : Type} {K : Type} {A : Type} {B : Type} (ma : Agent I J A) (f : A -> Agent J K B) (s : RunState) : ResultT String IO (Pair RunState B) := do {
    let p <- Agent.exec ma s;
    agent_apply f p
}

pub def Agent.bind {I : Type} {J : Type} {K : Type} {A : Type} {B : Type} (ma : Agent I J A) (f : A -> Agent J K B) : Agent I K B :=
    Agent.agent (fn (s : RunState) => agent_bind_run ma f s)

pub def Agent.map {I : Type} {J : Type} {A : Type} {B : Type} (f : A -> B) (ma : Agent I J A) : Agent I J B :=
    Agent.bind ma (fn (a : A) => Agent.pure (f a))

pub def Agent.and_then {I : Type} {J : Type} {K : Type} {A : Type} {B : Type} (first : Agent I J A) (second : Agent J K B) : Agent I K B :=
    Agent.bind first (fn (_ : A) => second)

pub instance IndexedMonad Agent {
    def pure (a : A) : Agent I I A := Agent.pure a
    def bind (ma : Agent I J A) (f : A -> Agent J K B) : Agent I K B := Agent.bind ma f
    def map (f : A -> B) (ma : Agent I J A) : Agent I J B := Agent.map f ma
    def and_then (first : Agent I J A) (second : Agent J K B) : Agent I K B := Agent.and_then first second
    def lift (a : A) : Agent I I A := Agent.pure a
}

/// Do-notation over `Agent` at EQUAL indices. The prelude's generic
/// bridge instance never dispatches (variable head); this concrete one
/// is what `KnownInstances` actually finds -- see
/// `examples/indexed_monads.mo`'s own `Monad (Protocol I I)`.
instance Monad (Agent I I) {
    def pure (a : A) : Agent I I A := Agent.pure a
    def bind (ma : Agent I I A) (f : A -> Agent I I B) : Agent I I B := Agent.bind ma f
}
