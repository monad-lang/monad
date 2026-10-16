/// The slash-command table tests -- weaver.md Phase 6: every command
/// pinned through the one public seam, `Commands.dispatch`, exactly as
/// the dumb loop sees them (the `cmd_*` handlers stay package-private).
/// The assertions are on the Effect's whole payload -- the advanced
/// state AND the exact output line -- because the output is part of the
/// contract: the user reads it, and the loop prints nothing else.
use init::transformers {ResultT}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::gate {Capability, Gate}
use shuttle::message_types {Content}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use shuttle::tool {ToolSpec, ToolImpl}
use weaver::commands {State, Effect, Commands.dispatch}
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
def state_of (mode : Mode) (mcps : List String) : State := {
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
def with_turns (st : State) (n : I64) : State :=
    let s2 : Session := { (st.run.session) with turns := n } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : State := { st with run := run2 } in
    st2

// ── Equality pins ──────────────────────────────────────────────────────

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

/// One dispatch's whole outcome: the mode it landed on, the output it
/// printed, and whether it quit.
def effect_is (e : Effect) (m : Mode) (out : String) : Bool :=
    mode_eq e.state.mode m && e.output == out && Bool.not e.state.quit

// ── /mode ──────────────────────────────────────────────────────────────

#[test]
def test_mode_shows_current : IO Bool := do {
    let e <- Commands.dispatch "/mode" (state_of Mode.manual []);
    return (effect_is e Mode.manual "mode: manual")
}

#[test]
def test_mode_sets_plan : IO Bool := do {
    let e <- Commands.dispatch "/mode plan" (state_of Mode.manual []);
    return (effect_is e Mode.plan "mode: plan")
}

#[test]
def test_mode_rejects_unknown_name : IO Bool := do {
    let e <- Commands.dispatch "/mode fast" (state_of Mode.manual []);
    return (effect_is e Mode.manual "unknown mode: fast (manual | plan | allow_edit | auto)")
}

// ── /plan ───────────────────────────────────────────────────────────────

#[test]
def test_plan_status_in_plan_mode : IO Bool := do {
    let e <- Commands.dispatch "/plan" (state_of Mode.plan []);
    return (effect_is e Mode.plan "plan mode: only read tools run; produce the plan, then /plan approve [manual|allow_edit]")
}

#[test]
def test_plan_status_outside_plan_mode : IO Bool := do {
    let e <- Commands.dispatch "/plan" (state_of Mode.manual []);
    return (effect_is e Mode.manual "not in plan mode (mode: manual); switch with /mode plan")
}

#[test]
def test_plan_approve_defaults_to_manual : IO Bool := do {
    let e <- Commands.dispatch "/plan approve" (state_of Mode.plan []);
    return (effect_is e Mode.manual "plan approved -- mode: manual")
}

#[test]
def test_plan_approve_lands_on_allow_edit : IO Bool := do {
    let e <- Commands.dispatch "/plan approve allow_edit" (state_of Mode.plan []);
    return (effect_is e Mode.allow_edit "plan approved -- mode: allow_edit")
}

/// `/plan approve auto` is a one-word trust escalation; the command
/// refuses it and the session stays in plan mode.
#[test]
def test_plan_approve_auto_is_refused : IO Bool := do {
    let e <- Commands.dispatch "/plan approve auto" (state_of Mode.plan []);
    return (effect_is e Mode.plan "plan approval drops to manual or allow_edit")
}

#[test]
def test_plan_approve_outside_plan_mode_is_noop : IO Bool := do {
    let e <- Commands.dispatch "/plan approve manual" (state_of Mode.manual []);
    return (effect_is e Mode.manual "no plan to approve -- mode: manual")
}

// ── /mcp and /tools ─────────────────────────────────────────────────────

#[test]
def test_mcp_none_mounted : IO Bool := do {
    let e <- Commands.dispatch "/mcp" (state_of Mode.manual []);
    return (effect_is e Mode.manual "mcp: none mounted (--mcp <executable>, repeatable)")
}

#[test]
def test_mcp_lists_mounted_servers : IO Bool := do {
    let e <- Commands.dispatch "/mcp" (state_of Mode.manual ["srv-a", "srv-b"]);
    return (effect_is e Mode.manual "mcp: srv-a, srv-b")
}

#[test]
def test_tools_lists_capability_tags : IO Bool := do {
    let e <- Commands.dispatch "/tools" (state_of Mode.manual []);
    return (effect_is e Mode.manual "tools: stamp (write)")
}

// ── Unknown commands ───────────────────────────────────────────────────

#[test]
def test_unknown_command_gets_help_hint : IO Bool := do {
    let e <- Commands.dispatch "/nope" (state_of Mode.manual []);
    return (effect_is e Mode.manual "unknown command: /nope (try /help)")
}

// ── /save and /resume: the budget spans both halves ────────────────────

def session_path : String :=
    String.concat "/tmp/weaver_session_" (String.concat (I64.to_string process_id) ".json")

/// A session four turns in, saved to disk; a FRESH state (turns 0,
/// full budget) resumes it -- and lands with `turns_left = 2`: the
/// budget spans both halves, exactly shuttle's own semantics.
#[test]
def test_save_resume_budget_spans_halves : IO Bool := do {
    let e1 <- Commands.dispatch (String.concat "/save " session_path) (with_turns (state_of Mode.manual []) 4);
    let e2 <- Commands.dispatch (String.concat "/resume " session_path) (state_of Mode.manual []);
    return (e1.output == String.concat "saved " session_path
        && e2.output == String.concat "resumed " session_path
        && e2.state.run.session.turns == 4
        && e2.state.run.turns_left == 2)
}
