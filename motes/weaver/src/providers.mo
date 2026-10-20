/// Weaver's provider presets -- shuttle's four live presets plus the
/// offline `mock` wire, and the default model each provider falls back
/// to. One resolution point shared by the entry (`--provider`) and
/// `/provider`, so the two cannot disagree.
use shuttle::provider {ProviderConfig, Wire}
use shuttle::session {Session}
use shuttle::presets {
    ProviderConfig.ollama, ProviderConfig.mistral,
    ProviderConfig.openrouter, ProviderConfig.anthropic,
}
use std::map {BTreeMap}

/// The scripted wire (`shuttle::wire::mock`) as a preset: offline runs
/// and the e2e tests. `base_url` is decorative -- the mock wire reads
/// its script file -- and the key env names a var nothing sets.
pub def Weaver.mock_config (model : String) : ProviderConfig :=
    { base_url := "mock", model := model, api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 512, wire := Wire.mock }

/// The default model per provider when none is given. OpenRouter has
/// none: its model names are vendor-qualified (`mistralai/...`), so a
/// default would be a guess.
pub def Weaver.default_model (provider : String) : Result String String :=
    if provider == "ollama" then Result.ok "qwen2.5-coder"
    else if provider == "mistral" then Result.ok "mistral-large-latest"
    else if provider == "anthropic" then Result.ok "claude-opus-5"
    else if provider == "openrouter" then Result.err "openrouter needs a --model (vendor-qualified, e.g. mistralai/mistral-large)"
    else if provider == "mock" then Result.ok "mock"
    else Result.err (String.concat "unknown provider: " (String.concat provider " (ollama | mistral | openrouter | anthropic | mock)"))

/// Resolve a provider name to a config, keeping the model name given
/// ("" falls back to the provider's default). `keys` is the merged
/// `[api_keys]` table: the chosen provider's entry (when present)
/// lands in the config as the DIRECT key, which then beats the env var
/// at send time -- one resolution point for the entry, `/provider` and
/// everything that swaps providers later (weaver.md Phase 10).
pub def Weaver.preset (provider : String) (model : String) (keys : BTreeMap String String) : Result String ProviderConfig :=
    if Bool.not (String.is_empty model) then preset_named provider model keys
    else match Weaver.default_model provider {
        Result.err e => Result.err e,
        Result.ok m => preset_named provider m keys,
    }

// ── model validation ──────────────────────────────────────────────────
//
// A model belongs to a provider. The settings file stores both
// independently, so a stale model can be paired with a new provider
// (`provider = "mistral"` + an ollama tag) and the server answers with an
// opaque Invalid model. These checks run wherever a provider or model is
// chosen: startup, `/provider`, `/model`, and a resumed session.

#[terminating]
def starts_any (prefixes : List String) (s : String) : Bool :=
    match prefixes {
        List.empty => false,
        List.cons p rest => Bool.or (String.starts_with p s) (starts_any rest s),
    }

def mistral_family (m : String) : Bool :=
    starts_any ["mistral-", "codestral-", "ministral-", "pixtral-", "devstral-", "magistral-", "voxtral-", "open-mistral-", "open-mixtral-", "open-codestral-"] m

/// Whether `model` is plausible for `provider`. Ollama and mock cannot be
/// checked (local tags / a scripted wire); the hosted presets have stable
/// family names. OpenRouter's names are vendor-qualified.
pub def Weaver.model_matches (provider : String) (model : String) : Bool :=
    if provider == "mock" then true
    else if provider == "ollama" then Bool.not (String.is_empty model)
    else if provider == "mistral" then mistral_family model
    else if provider == "openrouter" then String.contains model "/"
    else if provider == "anthropic" then String.starts_with "claude" model
    else false

/// `none` when the model belongs to the provider (or is empty: "use the
/// default"); a human-readable refusal otherwise.
pub def Weaver.model_error (provider : String) (model : String) : Option String :=
    if String.is_empty model then Option.none
    else if Weaver.model_matches provider model then Option.none
    else match Weaver.default_model provider {
        Result.err _ => Option.some (String.concat provider (String.concat " does not accept model " model)),
        Result.ok d =>
            let msg : String := String.concat provider (String.concat " does not accept model " (String.concat model (String.concat " (try " (String.concat d ")")))) in
            Option.some msg,
    }

pub def Weaver.validated_model (provider : String) (model : String) : Result String String :=
    match Weaver.model_error provider model {
        Option.none => Result.ok model,
        Option.some e => Result.err e,
    }

/// A restored session's config may have been saved under a different
/// provider: repair its model to the CURRENT provider's default, with the
/// one-line reason it had to.
pub def Weaver.repair_session_model (provider : String) (s : Session) : Pair Session (Option String) :=
    match Weaver.model_error provider s.config.model {
        Option.none => Pair.pair s Option.none,
        Option.some e => match Weaver.default_model provider {
            Result.err _ => Pair.pair s (Option.some e),
            Result.ok d =>
                let cfg0 : ProviderConfig := s.config in
                let cfg : ProviderConfig := { cfg0 with model := d } in
                let s2 : Session := { s with config := cfg } in
                Pair.pair s2 (Option.some (String.concat e (String.concat "; using " d))),
        },
    }

def preset_named (provider : String) (model : String) (keys : BTreeMap String String) : Result String ProviderConfig :=
    if provider == "ollama" then Result.ok (with_key keys provider (ProviderConfig.ollama model))
    else if provider == "mistral" then Result.ok (with_key keys provider (ProviderConfig.mistral model))
    else if provider == "openrouter" then Result.ok (with_key keys provider (ProviderConfig.openrouter model))
    else if provider == "anthropic" then Result.ok (with_key keys provider (ProviderConfig.anthropic model))
    else if provider == "mock" then Result.ok (Weaver.mock_config model)
    else Result.err (String.concat "unknown provider: " provider)

/// The settings-stored key, when the files spoke for this provider,
/// rides the config directly; `none` (the common case) leaves the env
/// name as the whole resolution, byte-identical to before.
def with_key (keys : BTreeMap String String) (provider : String) (cfg : ProviderConfig) : ProviderConfig :=
    let keyed : ProviderConfig := { cfg with api_key := Map.lookup provider keys } in
    keyed
