/// Provider/model pair validation: the check that keeps a settings file's
/// stale model from being sent to a provider that does not serve it.
use weaver::providers {
    Weaver.model_matches, Weaver.model_error, Weaver.default_model,
    Weaver.repair_session_model,
}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::message {Usage}

def cfg (model : String) : ProviderConfig :=
    { base_url := "mock", model := model, api_key_env := "K", max_tokens := 8, wire := Wire.mock }

def usage : Usage := { input_tokens := 0, output_tokens := 0, cached_tokens := 0 }

def session_with (model : String) : Session :=
    { config := cfg model, system_prompt := "", tools := List.empty, history := List.empty, turns := 0, spent := usage }

#[test]
def test_mistral_family_matches : Bool :=
    Weaver.model_matches "mistral" "mistral-large-latest"
        && Weaver.model_matches "mistral" "codestral-latest"
        && Weaver.model_matches "mistral" "ministral-8b-latest"
        && Weaver.model_matches "mistral" "open-mistral-nemo"

#[test]
def test_foreign_model_does_not_match_mistral : Bool :=
    Bool.not (Weaver.model_matches "mistral" "zai-glm-5-3")
        && Bool.not (Weaver.model_matches "mistral" "qwen2.5-coder")

#[test]
def test_openrouter_requires_a_vendor_prefix : Bool :=
    Weaver.model_matches "openrouter" "mistralai/mistral-large"
        && Bool.not (Weaver.model_matches "openrouter" "mistral-large-latest")

#[test]
def test_anthropic_requires_claude : Bool :=
    Weaver.model_matches "anthropic" "claude-opus-5"
        && Bool.not (Weaver.model_matches "anthropic" "gpt-4")

#[test]
def test_ollama_and_mock_are_permissive : Bool :=
    Weaver.model_matches "ollama" "qwen3:8b"
        && Weaver.model_matches "mock" "anything"

#[test]
def test_empty_model_is_left_to_the_default : Bool :=
    match Weaver.model_error "mistral" "" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_model_error_names_the_mismatch : Bool :=
    match Weaver.model_error "mistral" "zai-glm-5-3" {
        Option.none => false,
        Option.some e => String.contains e "does not accept model" && String.contains e "mistral-large-latest",
    }

#[test]
def test_repair_replaces_a_foreign_model : Bool :=
    match Weaver.repair_session_model "mistral" (session_with "zai-glm-5-3") {
        Pair.pair fixed note =>
            let model : String := fixed.config.model in
            model == "mistral-large-latest"
                && (match note { Option.some _ => true, Option.none => false }),
    }

#[test]
def test_repair_leaves_a_valid_model_alone : Bool :=
    match Weaver.repair_session_model "mistral" (session_with "mistral-small-latest") {
        Pair.pair fixed note =>
            let model : String := fixed.config.model in
            model == "mistral-small-latest"
                && (match note { Option.some _ => false, Option.none => true }),
    }

#[test]
def test_default_models_are_valid_for_their_providers : Bool :=
    match Weaver.default_model "mistral" {
        Result.err _ => false,
        Result.ok m => Weaver.model_matches "mistral" m,
    }
        && (match Weaver.default_model "anthropic" {
            Result.err _ => false,
            Result.ok m => Weaver.model_matches "anthropic" m,
        })
