/// The slash-command table tests -- weaver.md Phase 6, re-pinned for
/// Phase 9: every command through the one public seam,
/// `Commands.dispatch`, which now speaks `Result WeaverError Effect` --
/// a FAILED command is the `Result.err` (typed, no state attached, so
/// the caller's stands), a successful one is the Effect's whole payload
/// (the advanced state AND the exact output line), because the output
/// is part of the contract: the user reads it, and the loop prints
/// nothing else.
use init::transformers {ResultT}
use shuttle::agent {RunState, silent_sleep}
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
use weaver::store {StoreState, TLine, TLine.user_line, Store.new_session, Store.append_transcript}
use std::path {Path, Path.of, Path.to_string}
use std::process {exec_cmd}
use json::json {Json}
use std::map {BTreeMap}
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
    keys := BTreeMap.empty,
    quit := false,
    fatal := Option.none,
    colors := true,
    store := Option.none,
}

def run_of : RunState := {
    session := session_of,
    reg := stamp_registry,
    turns_left := budget,
    emit := fn (_ : String) => IO.pure unit,
    gate := Gate.auto,
    always := List.empty,
    retries := 1,
    sleep_ms := silent_sleep,
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

/// An unknown provider name is a session-local refusal: command output
/// names it, state untouched, session alive. An argument typo must not
/// end an otherwise healthy run (the STARTUP path keeps its own fatal
/// shape for the same misspelling).
#[test]
def test_unknown_provider_refuses_in_session : IO Bool := do {
    let st0 : WeaverState := state_of Mode.manual [];
    let r <- Commands.dispatch "/provider bogus" st0;
    return (match r {
        Result.err _ => false,
        Result.ok e =>
            Bool.not e.state.quit
                && e.state.provider == st0.provider
                && String.contains e.output "unknown provider",
    })
}

/// Phase 10: `/provider` re-resolves the NEW provider's key from the
/// loaded settings -- the merged `[api_keys]` entry lands in the config
/// as the direct key (which then beats the env at send time).
#[test]
def test_provider_swap_lands_the_settings_key : IO Bool := do {
    let r <- Commands.dispatch "/provider mistral" state_with_keys;
    return (match r {
        Result.err _ => false,
        Result.ok e => match e.state.run.session.config.api_key {
            Option.some k => k == "sk-file-mistral",
            Option.none => false,
        },
    })
}

/// A provider the settings files did not speak for stays env-only: the
/// swap lands `none`, and the env name remains the resolution.
#[test]
def test_provider_swap_without_settings_key_is_env_only : IO Bool := do {
    let r <- Commands.dispatch "/provider mistral" (state_of Mode.manual []);
    return (match r {
        Result.err _ => false,
        Result.ok e => match e.state.run.session.config.api_key {
            Option.some _ => false,
            Option.none => true,
        },
    })
}

/// The state the key tests swap from: the merged settings' key table
/// carries a mistral entry.
def state_with_keys : WeaverState := {
    (state_of Mode.manual []) with keys := Map.insert "mistral" "sk-file-mistral" BTreeMap.empty,
}

def prov_is (e : Effect) (p : String) : Bool :=
    let got : String := e.state.provider in
    got == p

def model_is (e : Effect) (m : String) : Bool :=
    let got : String := e.state.run.session.config.model in
    got == m

def quit_of (e : Effect) : Bool :=
    let q : Bool := e.state.quit in
    q

/// A state whose provider/model pair is caller-chosen (the old provider's
/// model is exactly what must NOT survive a `/provider` switch).
def state_provider (provider : String) (model : String) : WeaverState :=
    let cfg : ProviderConfig := { mock_config with model := model } in
    let sess : Session := { session_of with config := cfg } in
    let run2 : RunState := { run_of with session := sess } in
    { (state_of Mode.manual []) with run := run2, provider := provider }

/// `/provider mistral` after an ollama model: the new provider's DEFAULT
/// model, never the old one (`Invalid model` was the live failure).
#[test]
def test_provider_switch_resets_to_the_new_default_model : IO Bool := do {
    let r <- Commands.dispatch "/provider mistral" (state_provider "ollama" "qwen2.5-coder");
    return (match r {
        Result.err _ => false,
        Result.ok e => prov_is e "mistral" && model_is e "mistral-large-latest",
    })
}

#[test]
def test_provider_switch_accepts_an_explicit_model : IO Bool := do {
    let r <- Commands.dispatch "/provider mistral mistral-small-latest" (state_provider "ollama" "qwen2.5-coder");
    return (match r {
        Result.err _ => false,
        Result.ok e => prov_is e "mistral" && model_is e "mistral-small-latest",
    })
}

/// A model the new provider does not serve is refused before the config
/// changes, so a typo cannot leave an invalid pair in the session.
#[test]
def test_provider_switch_refuses_a_foreign_model : IO Bool := do {
    let r <- Commands.dispatch "/provider mistral zai-glm-5-3" (state_provider "ollama" "qwen2.5-coder");
    return (match r {
        Result.err _ => false,
        Result.ok e => prov_is e "ollama"
            && model_is e "qwen2.5-coder"
            && String.contains e.output "does not accept model",
    })
}

#[test]
def test_model_change_is_validated_per_provider : IO Bool := do {
    let st : WeaverState := state_provider "mistral" "mistral-large-latest";
    let bad <- Commands.dispatch "/model qwen2.5-coder" st;
    let good <- Commands.dispatch "/model mistral-small-latest" st;
    return (match bad {
        Result.err _ => false,
        Result.ok e => model_is e "mistral-large-latest"
            && String.contains e.output "model unchanged",
    }) && (match good {
        Result.err _ => false,
        Result.ok e => model_is e "mistral-small-latest",
    })
}

// ── aliases ────────────────────────────────────────────────────────────

#[test]
def test_h_is_help : IO Bool := do {
    let r <- Commands.dispatch "/h" (state_of Mode.manual []);
    return (match r {
        Result.err _ => false,
        Result.ok e => String.contains e.output "/provider" && Bool.not (quit_of e),
    })
}

#[test]
def test_q_is_quit : IO Bool := do {
    let r <- Commands.dispatch "/q" (state_of Mode.manual []);
    return (match r {
        Result.err _ => false,
        Result.ok e => quit_of e,
    })
}

// ── session directories: /clear and /resume (Phase 4) ──────────────────

def test_root (name : String) : Path :=
    match Path.of (String.concat "/tmp/weaver_cmd_store_" (String.concat (I64.to_string process_id) (String.concat "_" name))) {
        Result.err _ => Path.path "/tmp/weaver_cmd_store_fallback",
        Result.ok p => p,
    }

def clean_dir (p : Path) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", Path.to_string p];
    return unit
}

def with_store (st : WeaverState) (s : StoreState) : WeaverState :=
    let st2 : WeaverState := { st with store := Option.some s } in
    st2

def effect_state (r : Result WeaverError Effect) : Option WeaverState :=
    match r {
        Result.err _ => Option.none,
        Result.ok e => Option.some e.state,
    }

def store_dir (st : WeaverState) : String :=
    match st.store {
        Option.none => "",
        Option.some s => Path.to_string s.dir,
    }

#[test]
def test_clear_rotates_the_session_directory : IO Bool := do {
    let root : Path := test_root "clear";
    clean_dir root;
    let base : WeaverState := state_of Mode.manual [];
    let r <- Store.new_session root base.run.session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok s0 => check_clear_rotation base s0,
    }
}

def check_clear_rotation (base : WeaverState) (s0 : StoreState) : IO Bool := do {
    let st : WeaverState := with_store base s0;
    let r <- Commands.dispatch "/clear" st;
    match effect_state r {
        Option.none => IO.pure false,
        Option.some st2 =>
            let before : String := Path.to_string s0.dir in
            let after : String := store_dir st2 in
            IO.pure (Bool.not (after == before) && Bool.not (String.is_empty after)),
    }
}

#[test]
def test_resume_without_a_store_says_unavailable : IO Bool := do {
    let r <- Commands.dispatch "/resume" (state_of Mode.manual []);
    match r {
        Result.err _ => IO.pure false,
        Result.ok e => IO.pure (String.contains e.output "persistence unavailable"),
    }
}

#[test]
def test_resume_by_directory_loads_history : IO Bool := do {
    let root : Path := test_root "resume";
    clean_dir root;
    let base : WeaverState := state_of Mode.manual [];
    let r <- Store.new_session root base.run.session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok s0 => check_resume_dir base s0 root,
    }
}

def check_resume_dir (base : WeaverState) (s0 : StoreState) (root : Path) : IO Bool := do {
    let _ <- Store.append_transcript s0.dir 0 [TLine.user_line "x"] ;
    let r <- Commands.dispatch (String.concat "/resume " (Path.to_string s0.dir)) (with_store base s0);
    match effect_state r {
        Option.none => IO.pure false,
        Option.some st2 => IO.pure (match st2.store {
            Option.none => false,
            Option.some s2 => Path.to_string s2.dir == Path.to_string s0.dir,
        }),
    }
}
