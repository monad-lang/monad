/// The slash-command table tests -- weaver.md Phase 6, re-pinned for
/// Phase 9: every command through the one public seam,
/// `Commands.dispatch`, which now speaks `Result WeaverError Effect` --
/// a FAILED command is the `Result.err` (typed, no state attached, so
/// the caller's stands), a successful one is the Effect's whole payload
/// (the advanced state AND the exact output line), because the output
/// is part of the contract: the user reads it, and the loop prints
/// nothing else.
use init::transformers {ResultT}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::gate {Capability, Gate}
use shuttle::message_types {Content}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use shuttle::tool {ToolSpec, ToolImpl}
use weaver::commands {WeaverState, Effect, Commands.dispatch}
use weaver::error {WeaverError}
use weaver::policy {Mode}
use json::json {Json}
use std::process {process_id}

// ── The offline state (main.mo's shape, per-command parameterized) ──────

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

/// The `stamp` tool of the e2e tests: write-cap, side-effect-free. Its
/// point here is the capability tag `/tools` prints.
def stamp_spec : ToolSpec := { name := "stamp", description := "stamps its input", schema := Json.make_null }

def stamp_run (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (return (Result.ok (Content.tool_result id "STAMPED" false)))

def stamp_impl : ToolImpl := { spec := stamp_spec, cap := Capability.write, run := stamp_run }

def stamp_registry : ToolRegistry := ToolRegistry.register stamp_impl ToolRegistry.empty

def budget : I64 := 6

/// The state each dispatch starts from: mode and `mcps` are the two
/// knobs the commands under test actually read.
def state_of (mode : Mode) (mcps : List String) : WeaverState := {
    run := run_of,
    mode := mode,
    provider := "mock",
    budget := budget,
    mcps := mcps,
    quit := false,
}

def run_of : RunState := {
    session := session_of,
    reg := stamp_registry,
    turns_left := budget,
    emit := fn (_ : String) => IO.pure unit,
    gate := Gate.auto,
    always := List.empty,
}

def session_of : Session := {
    config := mock_config,
    system_prompt := "You are a test harness.",
    tools := ToolRegistry.specs stamp_registry,
    history := List.empty,
    turns := 0,
    spent := usage_zero,
}

/// A session that has already taken `n` turns -- what `/save` writes.
def with_turns (st : WeaverState) (n : I64) : WeaverState :=
    let s2 : Session := { (st.run.session) with turns := n } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : WeaverState := { st with run := run2 } in
    st2

// ── Equality pins ──────────────────────────────────────────────────────

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

/// One dispatch's whole SUCCESS outcome: it is a `Result.ok` (a failed
/// command is the `Result.err`, never an Effect), it landed on `m`, it
/// printed exactly `out`, and it did not quit.
def effect_is (r : Result WeaverError Effect) (m : Mode) (out : String) : Bool :=
    match r {
        Result.ok e => mode_eq e.state.mode m && e.output == out && Bool.not e.state.quit,
        Result.err _ => false,
    }

// ── /mode ──────────────────────────────────────────────────────────────

#[test]
def test_mode_shows_current : IO Bool := do {
    let r <- Commands.dispatch "/mode" (state_of Mode.manual []);
    return (effect_is r Mode.manual "mode: manual")
}

#[test]
def test_mode_sets_plan : IO Bool := do {
    let r <- Commands.dispatch "/mode plan" (state_of Mode.manual []);
    return (effect_is r Mode.plan "mode: plan")
}

#[test]
def test_mode_rejects_unknown_name : IO Bool := do {
    let r <- Commands.dispatch "/mode fast" (state_of Mode.manual []);
    return (effect_is r Mode.manual "unknown mode: fast (manual | plan | allow_edit | auto)")
}

// ── /plan ───────────────────────────────────────────────────────────────

#[test]
def test_plan_status_in_plan_mode : IO Bool := do {
    let r <- Commands.dispatch "/plan" (state_of Mode.plan []);
    return (effect_is r Mode.plan "plan mode: only read tools run; produce the plan, then /plan approve [manual|allow_edit]")
}

#[test]
def test_plan_status_outside_plan_mode : IO Bool := do {
    let r <- Commands.dispatch "/plan" (state_of Mode.manual []);
    return (effect_is r Mode.manual "not in plan mode (mode: manual); switch with /mode plan")
}

#[test]
def test_plan_approve_defaults_to_manual : IO Bool := do {
    let r <- Commands.dispatch "/plan approve" (state_of Mode.plan []);
    return (effect_is r Mode.manual "plan approved -- mode: manual")
}

#[test]
def test_plan_approve_lands_on_allow_edit : IO Bool := do {
    let r <- Commands.dispatch "/plan approve allow_edit" (state_of Mode.plan []);
    return (effect_is r Mode.allow_edit "plan approved -- mode: allow_edit")
}

/// `/plan approve auto` is a one-word trust escalation; the command
/// refuses it and the session stays in plan mode.
#[test]
def test_plan_approve_auto_is_refused : IO Bool := do {
    let r <- Commands.dispatch "/plan approve auto" (state_of Mode.plan []);
    return (effect_is r Mode.plan "plan approval drops to manual or allow_edit")
}

#[test]
def test_plan_approve_outside_plan_mode_is_noop : IO Bool := do {
    let r <- Commands.dispatch "/plan approve manual" (state_of Mode.manual []);
    return (effect_is r Mode.manual "no plan to approve -- mode: manual")
}

// ── /mcp and /tools ─────────────────────────────────────────────────────

#[test]
def test_mcp_none_mounted : IO Bool := do {
    let r <- Commands.dispatch "/mcp" (state_of Mode.manual []);
    return (effect_is r Mode.manual "mcp: none mounted (--mcp <executable>, repeatable)")
}

#[test]
def test_mcp_lists_mounted_servers : IO Bool := do {
    let r <- Commands.dispatch "/mcp" (state_of Mode.manual ["srv-a", "srv-b"]);
    return (effect_is r Mode.manual "mcp: srv-a, srv-b")
}

#[test]
def test_tools_lists_capability_tags : IO Bool := do {
    let r <- Commands.dispatch "/tools" (state_of Mode.manual []);
    return (effect_is r Mode.manual "tools: stamp (write)")
}

// ── Unknown commands ───────────────────────────────────────────────────

#[test]
def test_unknown_command_gets_help_hint : IO Bool := do {
    let r <- Commands.dispatch "/nope" (state_of Mode.manual []);
    return (effect_is r Mode.manual "unknown command: /nope (try /help)")
}

// ── /save and /resume: the budget spans both halves ────────────────────

def session_path : String :=
    String.concat "/tmp/weaver_session_" (String.concat (I64.to_string process_id) ".json")

/// A session four turns in, saved to disk; a FRESH state (turns 0,
/// full budget) resumes it -- and lands with `turns_left = 2`: the
/// budget spans both halves, exactly shuttle's own semantics.
#[test]
def test_save_resume_budget_spans_halves : IO Bool := do {
    let r1 <- Commands.dispatch (String.concat "/save " session_path) (with_turns (state_of Mode.manual []) 4);
    let r2 <- Commands.dispatch (String.concat "/resume " session_path) (state_of Mode.manual []);
    return (effect_is r1 Mode.manual (String.concat "saved " session_path)
        && effect_is r2 Mode.manual (String.concat "resumed " session_path)
        && resumed_turns r2 == 4
        && resumed_left r2 == 2)
}

/// The resumed session's turn count -- the value the budget recomputes
/// against. `-1` on a failed dispatch so a `Result.err` can never
/// masquerade as a successful resume at count 0.
def resumed_turns (r : Result WeaverError Effect) : I64 :=
    match r { Result.ok e => e.state.run.session.turns, Result.err _ => 0 - 1 }

def resumed_left (r : Result WeaverError Effect) : I64 :=
    match r { Result.ok e => e.state.run.turns_left, Result.err _ => 0 - 1 }

// ── Failed commands: the typed errors, session intact ──────────────────

/// A `Result.err` carries no Effect -- the caller's state IS the
/// outcome, which is what "session intact" means: nothing to rebuild,
/// nothing lost. What the error IS is the contract; the helpers pin
/// the tag, the dispatch test pins the shape.
def is_io (e : WeaverError) : Bool :=
    match e { WeaverError.io _ => true, _ => false }

def is_config (e : WeaverError) : Bool :=
    match e { WeaverError.config _ => true, _ => false }

/// A failed `/resume` is a typed `io` error (the file the user named
/// could not be read), not an output line that starts with
/// `resume failed:`.
#[test]
def test_resume_missing_file_is_io_error : IO Bool := do {
    let r <- Commands.dispatch "/resume /tmp/weaver_session_no_such_file.json" (state_of Mode.manual []);
    return (match r {
        Result.err e => is_io e,
        Result.ok _ => false,
    })
}

/// An unknown provider name is a `config` error -- the run's
/// configuration is wrong, not its files or its wire.
#[test]
def test_unknown_provider_is_config_error : IO Bool := do {
    let r <- Commands.dispatch "/provider bogus" (state_of Mode.manual []);
    return (match r {
        Result.err e => is_config e,
        Result.ok _ => false,
    })
}
