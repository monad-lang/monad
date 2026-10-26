/// The settings tests -- weaver.md Phase 6: `parse_settings` from TOML
/// text (every knob plus the caps table, and the best-effort contract --
/// a bad value drops its entry, never the file), `Settings.merge`'s
/// resolution order (the project file wins per field, the capability
/// tables union key by key), the capability vocabulary, and
/// `Settings.load_of_path` against real files. The file tests write
/// under /tmp, PID-qualified -- never `.weaver/config.toml` in the repo,
/// which would leak into every later manual run's resolution.
use std::test {Test.write_fixture}
use weaver::settings {
    Settings, Settings.empty, Settings.merge, Settings.load_of_path,
    Settings.cap_of, Settings.key_of, Loaded, parse_settings, parse_warned, parse_cap,
    SettingsUpdate, Settings.render_update, Settings.validate,
}
use weaver::error {WeaverError, WeaverError.show}
use weaver::policy {Mode}
use shuttle::gate {Capability}
use std::map {Map, BTreeMap}
use std::process {process_id}

// ── Option equality, field by field ─────────────────────────────────────

def opt_str_eq (a : Option String) (b : Option String) : Bool :=
    match a {
        Option.some x => match b { Option.some y => x == y, Option.none => false },
        Option.none => match b { Option.some _ => false, Option.none => true },
    }

def opt_i64_eq (a : Option I64) (b : Option I64) : Bool :=
    match a {
        Option.some x => match b { Option.some y => x == y, Option.none => false },
        Option.none => match b { Option.some _ => false, Option.none => true },
    }

def opt_bool_eq (a : Option Bool) (b : Option Bool) : Bool :=
    match a {
        Option.some x => match b { Option.some y => x == y, Option.none => false },
        Option.none => match b { Option.some _ => false, Option.none => true },
    }

def opt_mode_eq (a : Option Mode) (b : Option Mode) : Bool :=
    match a {
        Option.some x => match b { Option.some y => mode_eq x y, Option.none => false },
        Option.none => match b { Option.some _ => false, Option.none => true },
    }

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

def opt_cap_eq (a : Option Capability) (b : Option Capability) : Bool :=
    match a {
        Option.some x => match b { Option.some y => cap_eq x y, Option.none => false },
        Option.none => match b { Option.some _ => false, Option.none => true },
    }

def cap_eq (a : Capability) (b : Capability) : Bool :=
    match a {
        Capability.read => match b { Capability.read => true, _ => false },
        Capability.write => match b { Capability.write => true, _ => false },
        Capability.exec => match b { Capability.exec => true, _ => false },
        Capability.net => match b { Capability.net => true, _ => false },
    }

// ── parse_settings ─────────────────────────────────────────────────────

/// A file exercising every knob at once.
def full_toml : String :=
    "mode = \"plan\"\nprovider = \"ollama\"\nmodel = \"qwen3:8b\"\nmax_turns = 20\nthinking = true\nmax_tokens = 8192\n\n[mcp_caps]\nmcp-server-filesystem = \"read\"\nmy-server = \"net\"\n"

/// Every key of the file, parsed and pinned.
#[test]
def test_parse_settings_full_file : Bool :=
    let s : Settings := parse_settings full_toml in
    opt_mode_eq s.mode (Option.some Mode.plan)
        && opt_str_eq s.provider (Option.some "ollama")
        && opt_str_eq s.model (Option.some "qwen3:8b")
        && opt_i64_eq s.max_turns (Option.some 20)
        && opt_bool_eq s.thinking (Option.some true)
        && opt_i64_eq s.max_tokens (Option.some 8192)
        && opt_cap_eq (Settings.cap_of "mcp-server-filesystem" s) (Option.some Capability.read)
        && opt_cap_eq (Settings.cap_of "my-server" s) (Option.some Capability.net)

/// A file with only one key contributes only that key.
#[test]
def test_parse_settings_partial_file : Bool :=
    let s : Settings := parse_settings "model = \"custom-model\"\n" in
    opt_mode_eq s.mode Option.none
        && opt_str_eq s.provider Option.none
        && opt_str_eq s.model (Option.some "custom-model")
        && opt_i64_eq s.max_turns Option.none
        && opt_bool_eq s.thinking Option.none
        && opt_i64_eq s.max_tokens Option.none
        && opt_cap_eq (Settings.cap_of "anything" s) Option.none

/// A parse failure is the empty settings, not a refused start.
#[test]
def test_parse_settings_unparsable_is_empty : Bool :=
    let s : Settings := parse_settings "mode =" in
    opt_mode_eq s.mode Option.none
        && opt_str_eq s.provider Option.none
        && opt_str_eq s.model Option.none
        && opt_i64_eq s.max_turns Option.none
        && opt_bool_eq s.thinking Option.none
        && opt_i64_eq s.max_tokens Option.none
        && opt_cap_eq (Settings.cap_of "anything" s) Option.none

// ── parse_warned: the same behavior, now visible (Phase 9) ──────────────

/// The one warning an unparsable file contributes: `settings`-tagged
/// (recoverable -- startup continues), naming the file it came from.
def is_settings (e : WeaverError) : Bool :=
    match e { WeaverError.settings _ => true, _ => false }

def single_settings_warning (path : String) (ws : List WeaverError) : Bool :=
    match ws {
        List.empty => false,
        List.cons w rest =>
            is_settings w && String.contains (WeaverError.show w) path && no_more rest,
    }

def no_more (xs : List WeaverError) : Bool :=
    match xs { List.empty => true, _ => false }

/// The BEHAVIOR contract stands (empty settings on a parse failure)
/// and the silence does not: exactly one warning, settings-tagged,
/// naming the file.
#[test]
def test_parse_warned_unparsable_warns_once_naming_the_file : Bool :=
    let l : Loaded := parse_warned "/tmp/weaver/config.toml" "mode =" in
    let s : Settings := l.settings in
    opt_mode_eq s.mode Option.none
        && opt_str_eq s.provider Option.none
        && single_settings_warning "/tmp/weaver/config.toml" l.warnings

/// A good file contributes its keys and no warnings at all.
#[test]
def test_parse_warned_good_file_is_silent : Bool :=
    let l : Loaded := parse_warned "/tmp/weaver/config.toml" "provider = \"mistral\"\n" in
    opt_str_eq l.settings.provider (Option.some "mistral") && no_more l.warnings

/// Unknown top-level keys are ignored by the parser but reported, with
/// a near-miss hint -- `[api_key]` (the real-world typo) must point at
/// `[api_keys]`.
#[test]
def test_parse_warned_unknown_table_warns_with_a_hint : Bool :=
    let l : Loaded := parse_warned "/tmp/weaver/config.toml" "[api_key]\nmistral = \"x\"\n" in
    match l.warnings {
        List.cons w rest =>
            is_settings w
                && String.contains (WeaverError.show w) "unknown config key \"api_key\""
                && String.contains (WeaverError.show w) "did you mean \"api_keys\""
                && no_more rest,
        List.empty => false,
    }

/// A misspelled scalar is reported too, and the known table keys do not
/// warn just because their entries are arbitrary.
#[test]
def test_parse_warned_unknown_scalar_warns : Bool :=
    let l : Loaded := parse_warned "/tmp/c.toml" "max_turn = 5\nmodel = \"m\"\n\n[api_keys]\nmistral = \"k\"\n\n[mcp_caps]\nsrv = \"read\"\n" in
    match l.warnings {
        List.cons w rest =>
            String.contains (WeaverError.show w) "unknown config key \"max_turn\""
                && String.contains (WeaverError.show w) "max_turns"
                && no_more rest,
        List.empty => false,
    }

/// The best-effort contract: a wrong TYPE drops its scalar, a wrong
/// capability NAME drops its caps entry -- and every other entry of the
/// same file survives both.
#[test]
def test_parse_settings_drops_only_the_bad_entries : Bool :=
    let s : Settings := parse_settings "mode = \"fast\"\nprovider = 42\nmax_turns = 15\n\n[mcp_caps]\ngood = \"read\"\nbad = \"yolo\"\n" in
    opt_mode_eq s.mode Option.none
        && opt_str_eq s.provider Option.none
        && opt_i64_eq s.max_turns (Option.some 15)
        && opt_cap_eq (Settings.cap_of "good" s) (Option.some Capability.read)
        && opt_cap_eq (Settings.cap_of "bad" s) Option.none

// ── The capability vocabulary ───────────────────────────────────────────

/// `parse_cap` accepts exactly the four capability names.
#[test]
def test_parse_cap_vocabulary : Bool :=
    opt_cap_eq (parse_cap "read") (Option.some Capability.read)
        && opt_cap_eq (parse_cap "write") (Option.some Capability.write)
        && opt_cap_eq (parse_cap "exec") (Option.some Capability.exec)
        && opt_cap_eq (parse_cap "net") (Option.some Capability.net)
        && opt_cap_eq (parse_cap "sudo") Option.none
        && opt_cap_eq (parse_cap "") Option.none

// ── Settings.merge ──────────────────────────────────────────────────────

/// The global file's shape: a mode, a provider, a budget, and two
/// capability overrides.
def global_settings : Settings := {
    mode := Option.some Mode.plan,
    provider := Option.some "ollama",
    model := Option.none,
    max_turns := Option.some 20,
    thinking := Option.none,
    max_tokens := Option.none,
    context_window := Option.none,
    compact_at := Option.none,
    caps := Map.insert "srv" Capability.read (Map.insert "keep" Capability.net BTreeMap.empty),
    api_keys := Map.insert "mistral" "sk-global-mistral" (Map.insert "shared" "sk-global-shared" BTreeMap.empty),
}

/// The project file's shape: it overrides the provider and one server's
/// capability, and fills the model.
def project_settings : Settings := {
    mode := Option.none,
    provider := Option.some "mistral",
    model := Option.some "qwen3:8b",
    max_turns := Option.none,
    thinking := Option.none,
    max_tokens := Option.none,
    context_window := Option.none,
    compact_at := Option.none,
    caps := Map.insert "srv" Capability.exec BTreeMap.empty,
    api_keys := Map.insert "mistral" "sk-project-mistral" BTreeMap.empty,
}

/// The resolution order as one table: the project file wins per field
/// where it speaks, the global file's value stands where it does not,
/// and the capability tables union with the project's entries winning
/// per key -- `srv` flips, `keep` survives.
#[test]
def test_merge_project_wins_field_by_field : Bool :=
    let m : Settings := Settings.merge global_settings project_settings in
    opt_mode_eq m.mode (Option.some Mode.plan)
        && opt_str_eq m.provider (Option.some "mistral")
        && opt_str_eq m.model (Option.some "qwen3:8b")
        && opt_i64_eq m.max_turns (Option.some 20)
        && opt_cap_eq (Settings.cap_of "srv" m) (Option.some Capability.exec)
        && opt_cap_eq (Settings.cap_of "keep" m) (Option.some Capability.net)

/// Two empty files resolve to the empty settings -- the built-in floor.
#[test]
def test_merge_empty_is_empty : Bool :=
    let m : Settings := Settings.merge Settings.empty Settings.empty in
    opt_mode_eq m.mode Option.none
        && opt_str_eq m.provider Option.none
        && opt_str_eq m.model Option.none
        && opt_i64_eq m.max_turns Option.none
        && opt_cap_eq (Settings.cap_of "anything" m) Option.none

// ── Settings.load_of_path, against real files ──────────────────────────

def pid : String := I64.to_string process_id

/// A path no test writes: the absent-file contract (nothing, not a
/// failure) must hold for it.
def absent_path : String :=
    String.concat "/tmp/weaver_settings_absent_" (String.concat pid ".toml")

def present_path : String :=
    String.concat "/tmp/weaver_settings_present_" (String.concat pid ".toml")

def present_toml : String :=
    "provider = \"mistral\"\n\n[mcp_caps]\nsrv = \"read\"\n"

def write_present : IO Unit :=
    do { let _w <- Test.write_fixture (Path.path present_path) present_toml; return unit }

/// A missing file contributes nothing.
#[test]
def test_load_of_path_missing_file_is_empty : IO Bool := do {
    let s <- Settings.load_of_path absent_path;
    return (opt_mode_eq s.mode Option.none
        && opt_str_eq s.provider Option.none
        && opt_i64_eq s.max_turns Option.none)
}

/// A present file parses into exactly its keys.
#[test]
def test_load_of_path_present_file_parses : IO Bool := do {
    let _ <- write_present;
    let s <- Settings.load_of_path present_path;
    return (opt_str_eq s.provider (Option.some "mistral")
        && opt_mode_eq s.mode Option.none
        && opt_cap_eq (Settings.cap_of "srv" s) (Option.some Capability.read))
}

// ── [api_keys] (Phase 10 / Design 8) ────────────────────────────────────

/// The provider-key table parses like the caps table: string values
/// keyed by provider name, a wrong TYPE dropping its own entry -- never
/// the file -- and an absent provider simply having no key. An empty
/// value says nothing and stays unsaid: an empty bearer header is worse
/// than no key at all.
#[test]
def test_parse_settings_api_keys : Bool :=
    let s : Settings := parse_settings "provider = \"mistral\"\n\n[api_keys]\nmistral = \"sk-file-mistral\"\nopenrouter = \"sk-file-or\"\nbad = 42\nempty = \"\"\n" in
    opt_str_eq (Settings.key_of "mistral" s) (Option.some "sk-file-mistral")
        && opt_str_eq (Settings.key_of "openrouter" s) (Option.some "sk-file-or")
        && opt_str_eq (Settings.key_of "bad" s) Option.none
        && opt_str_eq (Settings.key_of "empty" s) Option.none
        && opt_str_eq (Settings.key_of "anthropic" s) Option.none

/// The key tables union like the caps: the project file's entry wins
/// per provider it speaks for, the global file's stands for the rest.
#[test]
def test_merge_api_keys_project_wins_per_key : Bool :=
    let m : Settings := Settings.merge global_settings project_settings in
    opt_str_eq (Settings.key_of "mistral" m) (Option.some "sk-project-mistral")
        && opt_str_eq (Settings.key_of "shared" m) (Option.some "sk-global-shared")
        && opt_str_eq (Settings.key_of "anthropic" m) Option.none

// ── Saving (the /settings dialog's explicit targets) ───────────────────

def sample_update : SettingsUpdate := {
    mode := Option.some "plan",
    provider := Option.none,
    model := Option.none,
    max_turns := Option.some 100,
    thinking := Option.some true,
    max_tokens := Option.some 4096,
    context_window := Option.none,
    compact_at := Option.none,
}

/// An absent file renders a fresh document with only the named keys.
#[test]
def test_render_update_from_scratch : Bool :=
    match Settings.render_update "" sample_update {
        Result.err _ => false,
        Result.ok out =>
            String.contains out "mode = \"plan\""
                && String.contains out "max_tokens = 4096"
                && String.contains out "max_turns = 100"
                && String.contains out "thinking = true",
    }

/// Re-rendering preserves unknown keys and other tables -- the save
/// never silently drops a user's config.
#[test]
def test_render_update_preserves_unknown_keys : Bool :=
    let existing := "custom_key = 7\n\n[mcp_caps]\nserver = \"read\"\n" in
    match Settings.render_update existing sample_update {
        Result.err _ => false,
        Result.ok out =>
            String.contains out "custom_key = 7"
                && String.contains out "[mcp_caps]"
                && String.contains out "mode = \"plan\"",
    }

/// A file that fails to parse is refused, never overwritten.
#[test]
def test_render_update_refuses_unparsable_input : Bool :=
    match Settings.render_update "this is not toml =" sample_update {
        Result.err _ => true,
        Result.ok _ => false,
    }

// ── range validation for the file-set numeric knobs ────────────────────

#[test]
def test_validate_accepts_the_defaults : Bool :=
    match Settings.validate Settings.empty {
        Result.ok _ => true,
        Result.err _ => false,
    }

/// The slash commands refuse these; a hand-edited file must not smuggle
/// them in (0 max_tokens is rejected by every provider, a negative
/// compact_at silently disables autocompact).
#[test]
def test_validate_refuses_out_of_range_knobs : Bool :=
    let e : Settings := Settings.empty in
    let tiny : Settings := { e with max_tokens := Option.some 0 } in
    let neg_compact : Settings := { e with compact_at := Option.some (0 - 5) } in
    let big_compact : Settings := { e with compact_at := Option.some 140 } in
    let neg_window : Settings := { e with context_window := Option.some (0 - 1) } in
    let off_window : Settings := { e with context_window := Option.some 0 } in
    (match Settings.validate tiny { Result.err _ => true, Result.ok _ => false })
        && (match Settings.validate neg_compact { Result.err _ => true, Result.ok _ => false })
        && (match Settings.validate big_compact { Result.err _ => true, Result.ok _ => false })
        && (match Settings.validate neg_window { Result.err _ => true, Result.ok _ => false })
        && (match Settings.validate off_window { Result.ok _ => true, Result.err _ => false })
