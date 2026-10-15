/// Tests for `motes/shuttle/src/presets.mo` -- pure field assertions,
/// no network. The live halves are in
/// `openai_compat_e2e_tests.mo`, gated like the Ollama/Anthropic e2e
/// files and equally blocked on TLS.
///
/// RUST-HOST-ONLY lowering failure, inherited, not caused here: this
/// file imports `shuttle::provider` (for the `ProviderConfig` type),
/// and importing that module alone trips the checker/lowering
/// `MatchTraversalMismatch { expected: [Monad], found: [mk] }` that
/// `loop.mo`'s own header documents -- probed 2026-10-14 with a test
/// body of just `String.beq (I64.to_string 3) "3"`. Passes 8/8 under
/// the self-hosted compiled backend, which is the gate that matters.
use shuttle::presets {ProviderConfig.mistral, ProviderConfig.openrouter, ProviderConfig.ollama, ProviderConfig.anthropic}
use shuttle::provider {ProviderConfig, Wire}

/// Every field read goes through a bound local rather than
/// `(preset "model").field`: dot access is only supported on a chain
/// of bare identifiers starting from a local binding, not on a
/// parenthesized application.
#[test]
def test_mistral_preset_points_at_mistral_ai : Bool :=
    let c := ProviderConfig.mistral "mistral-large-latest" in
    String.beq c.base_url "https://api.mistral.ai"

#[test]
def test_mistral_preset_reads_mistral_api_key : Bool :=
    let c := ProviderConfig.mistral "m" in
    String.beq c.api_key_env "MISTRAL_API_KEY"

#[test]
def test_mistral_preset_uses_the_openai_wire : Bool :=
    let c := ProviderConfig.mistral "m" in
    let w := c.wire in
    match w {
        Wire.openai => true,
        _ => false,
    }

#[test]
def test_openrouter_preset_points_at_openrouter : Bool :=
    let c := ProviderConfig.openrouter "mistralai/mistral-large" in
    String.beq c.base_url "https://openrouter.ai/api"

#[test]
def test_openrouter_preset_reads_openrouter_api_key : Bool :=
    let c := ProviderConfig.openrouter "m" in
    String.beq c.api_key_env "OPENROUTER_API_KEY"

#[test]
def test_openrouter_preset_uses_the_openai_wire : Bool :=
    let c := ProviderConfig.openrouter "m" in
    let w := c.wire in
    match w {
        Wire.openai => true,
        _ => false,
    }

#[test]
def test_ollama_preset_points_at_localhost : Bool :=
    let c := ProviderConfig.ollama "m" in
    String.beq c.base_url "http://localhost:11434"

#[test]
def test_ollama_preset_uses_the_openai_wire : Bool :=
    let c := ProviderConfig.ollama "m" in
    let w := c.wire in
    match w {
        Wire.openai => true,
        _ => false,
    }

#[test]
def test_anthropic_preset_points_at_anthropic : Bool :=
    let c := ProviderConfig.anthropic "claude-opus-5" in
    c.base_url == "https://api.anthropic.com"

#[test]
def test_anthropic_preset_reads_anthropic_api_key : Bool :=
    let c := ProviderConfig.anthropic "m" in
    c.api_key_env == "ANTHROPIC_API_KEY"

#[test]
def test_anthropic_preset_uses_the_anthropic_wire : Bool :=
    let c := ProviderConfig.anthropic "m" in
    let w := c.wire in
    match w {
        Wire.anthropic => true,
        _ => false,
    }
