// The weaver mote's library root -- bare `use weaver` resolves here.
//
// Weaver's surface, re-exported by name (no `{*}` globs, the same
// discipline as `motes/json/src/lib.mo`): the policy engine and the
// mode vocabulary it decided on, the interactive gate built from a
// mode, the settings resolution, the slash-command table and the
// state it carries, the dumb loop that drives it all, the diff
// renderer behind write/edit approvals, and the provider presets.
// A consumer (a plugin, the Phase 4 TUI, a test harness) gets the
// whole mote through this one import.

pub use lib::policy {
    Mode, Decision, Policy.decide,
    Mode.parse, Mode.show, Mode.approve_plan, Mode.warns_auto,
}
pub use lib::gate {cap_name, Gate.weaver, gate_answer_prompt, gate_answer_feedback}
pub use lib::theme {LineClass, line_class, class_style, class_code, theme_line_style, theme_status_style, Theme.tint, theme_status_code}
pub use lib::error {WeaverError, WeaverError.show, WeaverError.recoverable, WeaverError.of_shuttle}
pub use lib::settings {
    Settings, Settings.empty, Settings.merge, Settings.load,
    Settings.load_of_path, Settings.load_warned_of, Settings.cap_of,
    Loaded, Loaded.empty, parse_settings, parse_warned, parse_cap,
}
pub use lib::commands {
    WeaverState, Effect, Effect.ok, SlashCommand, command_table, Commands.dispatch,
}
pub use lib::dumb {Dumb.run}
pub use lib::diff {Diff.lines, Diff.render, Diff.for_input}
pub use lib::providers {
    Weaver.preset, Weaver.preferred_model, Weaver.config_for,
    Weaver.model_for, Weaver.mock_config,
}
pub use lib::catalog {
    Catalog.fetch, Catalog.lookup, Catalog.remember, Catalog.contains,
    Catalog.note, Catalog.render, Catalog.max_shown,
}
