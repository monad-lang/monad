/// Weaver's provider presets -- shuttle's four live presets plus the
/// offline `mock` wire, and the default model each provider falls back
/// to. One resolution point shared by the entry (`--provider`) and
/// `/provider`, so the two cannot disagree.
use shuttle::provider {ProviderConfig, Wire}
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
