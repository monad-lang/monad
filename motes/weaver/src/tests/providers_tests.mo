/// Provider presets, preferred defaults, and the catalogue-driven model
/// choice: the API list is the authority, so the only pinned names are
/// the PREFERENCES used when no list is available.
use weaver::providers {
    Weaver.preferred_model, Weaver.config_for, Weaver.model_for, Weaver.provider_of,
    Weaver.default_max_tokens, Weaver.default_max_turns, Weaver.default_window,
}
use weaver::catalog {Catalog.contains, Catalog.note, Catalog.render, Catalog.max_shown}
use shuttle::provider {ProviderConfig, Wire}
use std::map {BTreeMap}

#[test]
def test_preferred_defaults_are_the_documented_names : Bool :=
    (match Weaver.preferred_model "mistral" {
        Result.ok m => String.beq m "mistral-large-latest",
        Result.err _ => false,
    })
        && (match Weaver.preferred_model "anthropic" {
            Result.ok m => String.beq m "claude-opus-5",
            Result.err _ => false,
        })
        && (match Weaver.preferred_model "ollama" {
            Result.ok m => String.beq m "qwen2.5-coder",
            Result.err _ => false,
        })

#[test]
def test_provider_of_follows_the_config_not_the_flag : Bool :=
    // A session resumed under the wrong flag still talks to the vendor
    // its saved config names -- and the catalogue must be keyed by it.
    match Weaver.config_for "mistral" "mistral-large-latest" BTreeMap.empty {
        Result.err _ => false,
        Result.ok cfg => String.beq (Weaver.provider_of "ollama" cfg) "mistral",
    }

#[test]
def test_provider_of_keeps_an_unknown_config_name : Bool :=
    let cfg : ProviderConfig := { base_url := "https://example.test", model := "m", api_key_env := "K", max_tokens := 8, wire := Wire.openai, thinking := false } in
    String.beq (Weaver.provider_of "ollama" cfg) "ollama"

#[test]
def test_openrouter_has_no_preferred_name : Bool :=
    match Weaver.preferred_model "openrouter" {
        Result.err _ => true,
        Result.ok _ => false,
    }

#[test]
def test_model_for_prefers_the_listed_default : Bool :=
    match Weaver.model_for "mistral" ["mistral-small-latest", "mistral-large-latest"] {
        Result.ok m => String.beq m "mistral-large-latest",
        Result.err _ => false,
    }

#[test]
def test_model_for_falls_back_to_the_first_listed : Bool :=
    match Weaver.model_for "mistral" ["codestral-latest", "mistral-small-latest"] {
        Result.ok m => String.beq m "codestral-latest",
        Result.err _ => false,
    }

#[test]
def test_model_for_uses_the_preference_for_an_empty_list : Bool :=
    match Weaver.model_for "mistral" [] {
        Result.ok m => String.beq m "mistral-large-latest",
        Result.err _ => false,
    }

/// OpenRouter's no-preference error only applies when the API answered
/// with nothing; a fetched list supplies the choice.
#[test]
def test_model_for_openrouter_takes_the_first_listed : Bool :=
    match Weaver.model_for "openrouter" ["mistralai/mistral-large", "openai/gpt-5"] {
        Result.ok m => String.beq m "mistralai/mistral-large",
        Result.err _ => false,
    }

#[test]
def test_model_for_openrouter_without_a_list_still_errors : Bool :=
    match Weaver.model_for "openrouter" [] {
        Result.err _ => true,
        Result.ok _ => false,
    }

#[test]
def test_config_for_leaves_the_model_alone : Bool :=
    match Weaver.config_for "openrouter" "vendor/model" BTreeMap.empty {
        Result.ok cfg => String.beq cfg.model "vendor/model"
            && (match cfg.wire { Wire.openai => true, _ => false }),
        Result.err _ => false,
    }

#[test]
def test_catalog_contains_and_note : Bool :=
    Catalog.contains "b" ["a", "b"]
        && Bool.not (Catalog.contains "c" ["a", "b"])
        && (match Catalog.note "mistral" ["a"] "z" {
            Option.some _ => true,
            Option.none => false,
        })
        && (match Catalog.note "mistral" ["z"] "z" {
            Option.some _ => false,
            Option.none => true,
        })

#[test]
def test_render_shows_the_list_and_the_absent_note : Bool :=
    let out : String := Catalog.render "mistral" ["mistral-large-latest", "codestral-latest"] "zai-glm-5-3" in
    String.contains out "model: zai-glm-5-3"
        && String.contains out "models (mistral): 2"
        && String.contains out "  mistral-large-latest"
        && String.contains out "is not in mistral's model list"

#[test]
def test_render_omits_the_note_for_a_listed_model : Bool :=
    let out : String := Catalog.render "mistral" ["mistral-large-latest"] "mistral-large-latest" in
    Bool.not (String.contains out "is not in")

#[partial]
def many_models (n : I64) (acc : List String) : List String :=
    if n < 1i64
    then acc
    else many_models (n - 1i64) (List.cons (String.concat "m" (I64.to_string (n - 1i64))) acc)

#[test]
def test_render_caps_a_long_list : Bool :=
    let models : List String := many_models (Catalog.max_shown + 5i64) List.empty in
    let out : String := Catalog.render "mistral" models "m0" in
    String.contains out "  ... and 5 more"
        && String.contains out "models (mistral): 205"
        && Bool.not (String.contains out "  m204")

// ── Weaver's own budget/window defaults ───────────────────────────────

/// The interactive agent floors the output budget well above shuttle's
/// 512 preset: a truncated tool call or compaction summary is a failure,
/// not a saving.
#[test]
def test_default_output_budget_is_interactive : Bool :=
    Weaver.default_max_tokens == 4096i64

/// A turn is one model call; 40 was only a handful of user inputs.
#[test]
def test_default_turn_budget_is_interactive : Bool :=
    Weaver.default_max_turns == 100i64

/// Ollama serves smaller windows than the hosted vendors; a too-large
/// default means autocompact never fires before the provider truncates.
#[test]
def test_default_window_is_provider_aware : Bool :=
    Weaver.default_window "ollama" == 32768i64
        && Weaver.default_window "anthropic" == 200000i64
        && Weaver.default_window "mistral" == 128000i64
        && Weaver.default_window "openrouter" == 128000i64
        && Weaver.default_window "mock" == 128000i64
        && Weaver.default_window "unknown" == 128000i64
