/// Weaver's provider presets -- shuttle's four live presets plus the
/// offline `mock` wire, and the default model each provider falls back
/// to. One resolution point shared by the entry (`--provider`) and
/// `/provider`, so the two cannot disagree.
use shuttle::provider {ProviderConfig, Wire}
use shuttle::presets {
    ProviderConfig.ollama, ProviderConfig.mistral,
    ProviderConfig.openrouter, ProviderConfig.anthropic,
}

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
/// ("" falls back to the provider's default).
pub def Weaver.preset (provider : String) (model : String) : Result String ProviderConfig :=
    if Bool.not (String.is_empty model) then preset_named provider model
    else match Weaver.default_model provider {
        Result.err e => Result.err e,
        Result.ok m => preset_named provider m,
    }

def preset_named (provider : String) (model : String) : Result String ProviderConfig :=
    if provider == "ollama" then Result.ok (ProviderConfig.ollama model)
    else if provider == "mistral" then Result.ok (ProviderConfig.mistral model)
    else if provider == "openrouter" then Result.ok (ProviderConfig.openrouter model)
    else if provider == "anthropic" then Result.ok (ProviderConfig.anthropic model)
    else if provider == "mock" then Result.ok (Weaver.mock_config model)
    else Result.err (String.concat "unknown provider: " provider)
