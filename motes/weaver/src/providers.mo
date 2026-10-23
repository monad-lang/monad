/// Weaver's provider presets -- shuttle's four live presets plus the
/// offline `mock` wire, a preferred default model per provider, and the
/// catalogue-driven choice `/provider` makes. One resolution point
/// shared by the entry (`--provider`) and `/provider`, so the two cannot
/// disagree.
///
/// Model AVAILABILITY lives nowhere in this file: it comes from the
/// provider's own `/v1/models` (`catalog.mo`). `preferred_model` is only
/// a name to try when the settings name none.
use shuttle::provider {ProviderConfig, Wire}
use shuttle::presets {
    ProviderConfig.ollama, ProviderConfig.mistral,
    ProviderConfig.openrouter, ProviderConfig.anthropic,
}
use std::map {Map, BTreeMap}
use weaver::catalog {Catalog.contains}

/// The scripted wire (`shuttle::wire::mock`) as a preset: offline runs
/// and the e2e tests. `base_url` is decorative -- the mock wire reads
/// its script file -- and the key env names a var nothing sets.
pub def Weaver.mock_config (model : String) : ProviderConfig :=
    { base_url := "mock", model := model, api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 512, wire := Wire.mock }

/// The name to TRY when none is configured -- not an availability
/// claim. OpenRouter has none: its names are vendor-qualified, so the
/// API list (or an explicit model) decides.
pub def Weaver.preferred_model (provider : String) : Result String String :=
    if provider == "ollama" then Result.ok "qwen2.5-coder"
    else if provider == "mistral" then Result.ok "mistral-large-latest"
    else if provider == "anthropic" then Result.ok "claude-opus-5"
    else if provider == "openrouter" then Result.err "openrouter needs a --model (vendor-qualified, e.g. mistralai/mistral-large)"
    else if provider == "mock" then Result.ok "mock"
    else Result.err (String.concat "unknown provider: " (String.concat provider " (ollama | mistral | openrouter | anthropic | mock)"))

/// Resolve a provider name to a config, keeping the model name given
/// ("" falls back to the preferred name). `keys` is the merged
/// `[api_keys]` table: the chosen provider's entry (when present)
/// lands in the config as the DIRECT key, which then beats the env var
/// at send time.
pub def Weaver.preset (provider : String) (model : String) (keys : BTreeMap String String) : Result String ProviderConfig :=
    if Bool.not (String.is_empty model) then Weaver.config_for provider model keys
    else match Weaver.preferred_model provider {
        Result.err e => Result.err e,
        Result.ok m => Weaver.config_for provider m keys,
    }

/// A config for an explicit model name, with NO default substitution --
/// the shape `/provider` and `/models` need before a model is chosen.
pub def Weaver.config_for (provider : String) (model : String) (keys : BTreeMap String String) : Result String ProviderConfig :=
    if provider == "ollama" then Result.ok (with_key keys provider (ProviderConfig.ollama model))
    else if provider == "mistral" then Result.ok (with_key keys provider (ProviderConfig.mistral model))
    else if provider == "openrouter" then Result.ok (with_key keys provider (ProviderConfig.openrouter model))
    else if provider == "anthropic" then Result.ok (with_key keys provider (ProviderConfig.anthropic model))
    else if provider == "mock" then Result.ok (Weaver.mock_config model)
    else Result.err (String.concat "unknown provider: " provider)

/// The provider a config belongs to, matched on the preset `base_url`.
/// A resumed session keeps the saved vendor's config while this run's
/// CLI names its own provider; the session's wire -- not the flag -- is
/// what answers requests, so it decides the label, the catalogue's
/// owner and the key it resolves. `fallback` answers a config this
/// file did not build.
pub def Weaver.provider_of (fallback : String) (cfg : ProviderConfig) : String :=
  if String.beq cfg.base_url "http://localhost:11434" then "ollama"
  else if String.beq cfg.base_url "https://api.mistral.ai" then "mistral"
  else if String.beq cfg.base_url "https://openrouter.ai/api" then "openrouter"
  else if String.beq cfg.base_url "https://api.anthropic.com" then "anthropic"
  else if String.beq cfg.base_url "mock" then "mock"
  else fallback

/// The model a fetched catalogue implies: the preferred name when it is
/// listed, else the first listed name, else the preference (an empty
/// list cannot choose).
pub def Weaver.model_for (provider : String) (models : List String) : Result String String :=
    match Weaver.preferred_model provider {
        Result.ok p =>
            if Catalog.contains p models
            then Result.ok p
            else Result.ok (first_listed p models),
        Result.err e =>
            if provider_list_empty models
            then Result.err e
            else Result.ok (first_listed "" models),
    }

def first_listed (fallback : String) (models : List String) : String :=
    match models {
        List.empty => fallback,
        List.cons m _ => m,
    }

def provider_list_empty (models : List String) : Bool :=
    match models {
        List.empty => true,
        List.cons _ _ => false,
    }

/// The settings-stored key, when the files spoke for this provider,
/// rides the config directly; `none` (the common case) leaves the env
/// name as the whole resolution, byte-identical to before.
def with_key (keys : BTreeMap String String) (provider : String) (cfg : ProviderConfig) : ProviderConfig :=
    let keyed : ProviderConfig := { cfg with api_key := Map.lookup provider keys } in
    keyed
