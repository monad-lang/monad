/// Named provider presets -- the "connect to Mistral AI or OpenRouter
/// easily" half of the provider seam. `ProviderConfig` is already
/// fully parameterized (`base_url`/`api_key_env`/`wire`), so a preset
/// is nothing but a struct literal with the right constants; what it
/// buys is not having to know them -- which host, which env var, and
/// which wire each provider speaks.
///
/// Mistral and OpenRouter speak the OpenAI wire (`Wire.openai`):
/// Mistral's `https://api.mistral.ai` and OpenRouter's
/// `https://openrouter.ai/api` are both OpenAI-compatible chat
/// completions endpoints, so `motes/openai` + `wire/openai.mo` cover
/// them and no new wire adapter is involved. Anthropic is the one live
/// preset on `Wire.anthropic` (`motes/anthropic` + `wire/anthropic.mo`).
///
/// HTTPS for all three live presets rides `motes/tls` (landed
/// 2026-10-08): `moose` opens a TLS stream for any `https` base_url, so
/// the presets are reachable, not placeholders.
///
/// A MISSING API KEY IS NOT REJECTED HERE, deliberately: the openai
/// wire path treats an absent key as an unauthenticated local server
/// (that is how Ollama works at all -- see `send_openai` in
/// `provider.mo`), and a preset that demanded a key would break that
/// asymmetry at the wrong layer. A mistral/openrouter call with no key
/// therefore fails at the SERVER, with a 401, rather than locally --
/// legible enough, and it keeps `ProviderConfig` one shape for every
/// provider. (The anthropic wire is the exception that DOES require its
/// key, named, at send time -- see `anthropic_send_step`.)
use shuttle::provider {ProviderConfig, Wire}

/// A local Ollama daemon -- no key by default. `api_key_env` names a
/// var nothing sets (`OLLAMA_API_KEY`); if someone does set it, the
/// bearer header goes along, which is Ollama's own optional-auth
/// behaviour.
pub def ProviderConfig.ollama (model : String) : ProviderConfig :=
    { base_url := "http://localhost:11434", model := model, api_key_env := "OLLAMA_API_KEY", max_tokens := 512, wire := Wire.openai, thinking := false }

/// Mistral AI's hosted API -- OpenAI-compatible, key in
/// `MISTRAL_API_KEY` (their own convention). `model` stays a
/// parameter because model names churn faster than this file; the
/// e2e default is `mistral-large-latest`.
pub def ProviderConfig.mistral (model : String) : ProviderConfig :=
    { base_url := "https://api.mistral.ai", model := model, api_key_env := "MISTRAL_API_KEY", max_tokens := 512, wire := Wire.openai, thinking := false }

/// OpenRouter -- one OpenAI-compatible gateway over many vendors, key
/// in `OPENROUTER_API_KEY` (their own convention), and model names are
/// VENDOR-QUALIFIED (`vendor/model`, e.g. `mistralai/mistral-large`),
/// which is why `model` must be a parameter: no single default could
/// be right. `base_url` ends at `/api` because `OpenAI.complete`
/// appends `/v1/chat/completions` itself.
pub def ProviderConfig.openrouter (model : String) : ProviderConfig :=
    { base_url := "https://openrouter.ai/api", model := model, api_key_env := "OPENROUTER_API_KEY", max_tokens := 512, wire := Wire.openai, thinking := false }

/// Anthropic's hosted Messages API -- the one live preset on
/// `Wire.anthropic`. Key in `ANTHROPIC_API_KEY` (their convention, and
/// required at send time). `model` is a parameter because model names
/// churn; the CLI's default is `claude-opus-5`, the wire adapter's own
/// documented default.
pub def ProviderConfig.anthropic (model : String) : ProviderConfig :=
    { base_url := "https://api.anthropic.com", model := model, api_key_env := "ANTHROPIC_API_KEY", max_tokens := 512, wire := Wire.anthropic, thinking := false }
