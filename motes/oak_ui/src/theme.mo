// Design tokens: a typed `Ui.Theme` record rendered to `--oak-*` CSS custom
// properties.
//
// Every value is a CSS string, so a theme can use any unit, colour syntax or
// font stack. The stylesheet (`lib::css`) reads ONLY these variables, which
// gives three ways to restyle, from coarse to fine:
//   1. render a different theme (`Ui.Theme.css_vars ":root" my_theme`);
//   2. override single variables in your own CSS (`--oak-primary: #7c3aed`);
//   3. add classes with the `Ui.cls` modifier and target them.
//
// Tones carry three tokens each: the colour itself (solid backgrounds,
// borders, links), `*_fg` (text on the solid colour) and `*_soft` (a tinted
// background for soft variants, alerts and badges).

use std::list {List.intercalate}

pub struct Ui.Theme {
    bg : String,
    surface : String,
    surface_alt : String,
    border : String,
    border_strong : String,
    text : String,
    muted : String,
    focus : String,
    backdrop : String,
    neutral : String,
    neutral_fg : String,
    neutral_soft : String,
    primary : String,
    primary_fg : String,
    primary_soft : String,
    success : String,
    success_fg : String,
    success_soft : String,
    warning : String,
    warning_fg : String,
    warning_soft : String,
    danger : String,
    danger_fg : String,
    danger_soft : String,
    info : String,
    info_fg : String,
    info_soft : String,
    radius_sm : String,
    radius_md : String,
    radius_lg : String,
    space_unit : String,
    font_sans : String,
    font_mono : String,
    font_size : String,
    line_height : String,
    shadow_sm : String,
    shadow_md : String,
    shadow_lg : String,
    duration : String
}

/// A theme is an immutable record of strings.
pub instance Copy Ui.Theme {
    def copy (t : Ui.Theme) : Pair Ui.Theme Ui.Theme := Pair.pair t t
}

def sans_stack : String :=
    "system-ui, -apple-system, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"

def mono_stack : String :=
    "ui-monospace, SFMono-Regular, \"SF Mono\", Menlo, Consolas, monospace"

/// The light preset.
pub def Ui.Theme.light : Ui.Theme :=
    { bg := "#f8fafc", surface := "#ffffff", surface_alt := "#f1f5f9",
        border := "#e2e8f0", border_strong := "#cbd5e1",
        text := "#0f172a", muted := "#64748b", focus := "#3b82f6",
        backdrop := "rgba(15, 23, 42, 0.5)",
        neutral := "#475569", neutral_fg := "#ffffff", neutral_soft := "#f1f5f9",
        primary := "#2563eb", primary_fg := "#ffffff", primary_soft := "#dbeafe",
        success := "#16a34a", success_fg := "#ffffff", success_soft := "#dcfce7",
        warning := "#d97706", warning_fg := "#ffffff", warning_soft := "#fef3c7",
        danger := "#dc2626", danger_fg := "#ffffff", danger_soft := "#fee2e2",
        info := "#0891b2", info_fg := "#ffffff", info_soft := "#cffafe",
        radius_sm := "4px", radius_md := "8px", radius_lg := "12px",
        space_unit := "4px",
        font_sans := sans_stack, font_mono := mono_stack,
        font_size := "16px", line_height := "1.5",
        shadow_sm := "0 1px 2px rgba(15, 23, 42, 0.06)",
        shadow_md := "0 4px 12px rgba(15, 23, 42, 0.10)",
        shadow_lg := "0 12px 32px rgba(15, 23, 42, 0.18)",
        duration := "150ms" }

/// The dark preset.
pub def Ui.Theme.dark : Ui.Theme :=
    { bg := "#0d1117", surface := "#161b22", surface_alt := "#1f2630",
        border := "#30363d", border_strong := "#484f58",
        text := "#e6edf3", muted := "#8b949e", focus := "#58a6ff",
        backdrop := "rgba(1, 4, 9, 0.7)",
        neutral := "#8b949e", neutral_fg := "#0d1117", neutral_soft := "#21262d",
        primary := "#58a6ff", primary_fg := "#0d1117", primary_soft := "#132a4a",
        success := "#3fb950", success_fg := "#0d1117", success_soft := "#12301c",
        warning := "#d29922", warning_fg := "#0d1117", warning_soft := "#3a2a0c",
        danger := "#f85149", danger_fg := "#0d1117", danger_soft := "#3d1517",
        info := "#39c5cf", info_fg := "#0d1117", info_soft := "#0f3036",
        radius_sm := "4px", radius_md := "8px", radius_lg := "12px",
        space_unit := "4px",
        font_sans := sans_stack, font_mono := mono_stack,
        font_size := "16px", line_height := "1.5",
        shadow_sm := "0 1px 2px rgba(1, 4, 9, 0.4)",
        shadow_md := "0 4px 12px rgba(1, 4, 9, 0.5)",
        shadow_lg := "0 12px 32px rgba(1, 4, 9, 0.6)",
        duration := "150ms" }

def tok (name : String) (value : String) : Pair String String := Pair.pair name value

/// Every token as `(variable name without --oak-, value)`, in a stable
/// order. The stylesheet may reference only these names (a test pins it).
pub def Ui.Theme.tokens (t : Ui.Theme) : List (Pair String String) :=
    [tok "bg" t.bg, tok "surface" t.surface, tok "surface-alt" t.surface_alt,
        tok "border" t.border, tok "border-strong" t.border_strong,
        tok "text" t.text, tok "muted" t.muted, tok "focus" t.focus,
        tok "backdrop" t.backdrop,
        tok "neutral" t.neutral, tok "neutral-fg" t.neutral_fg, tok "neutral-soft" t.neutral_soft,
        tok "primary" t.primary, tok "primary-fg" t.primary_fg, tok "primary-soft" t.primary_soft,
        tok "success" t.success, tok "success-fg" t.success_fg, tok "success-soft" t.success_soft,
        tok "warning" t.warning, tok "warning-fg" t.warning_fg, tok "warning-soft" t.warning_soft,
        tok "danger" t.danger, tok "danger-fg" t.danger_fg, tok "danger-soft" t.danger_soft,
        tok "info" t.info, tok "info-fg" t.info_fg, tok "info-soft" t.info_soft,
        tok "radius-sm" t.radius_sm, tok "radius-md" t.radius_md, tok "radius-lg" t.radius_lg,
        tok "space" t.space_unit,
        tok "font-sans" t.font_sans, tok "font-mono" t.font_mono,
        tok "font-size" t.font_size, tok "line-height" t.line_height,
        tok "shadow-sm" t.shadow_sm, tok "shadow-md" t.shadow_md, tok "shadow-lg" t.shadow_lg,
        tok "duration" t.duration]

def declaration (p : Pair String String) : String :=
    match p { Pair.pair name value => String.concat_list ["--oak-", name, ": ", value, ";"] }

#[terminating]
def declarations (ps : List (Pair String String)) : List String :=
    match ps {
        List.empty => List.empty,
        List.cons p rest => List.cons (declaration p) (declarations rest),
    }

/// The declarations alone (`--oak-bg: …; --oak-surface: …;`), for embedding
/// in a rule you write yourself.
pub def Ui.Theme.declarations (t : Ui.Theme) : String :=
    List.intercalate " " (declarations (Ui.Theme.tokens t))

/// One rule: `selector { --oak-…: …; … }`.
pub def Ui.Theme.css_vars (selector : String) (t : Ui.Theme) : String :=
    String.concat_list [selector, " { ", Ui.Theme.declarations t, " }\n"]

/// Light by default, dark when the OS prefers it, and explicit
/// `data-theme="light"`/`"dark"` on any element to force one (on `<html>`
/// for the whole page, or on a subtree to theme just that part).
pub def Ui.Theme.css_auto (light : Ui.Theme) (dark : Ui.Theme) : String :=
    String.concat_list
        [Ui.Theme.css_vars ":root, [data-theme=\"light\"]" light,
            "@media (prefers-color-scheme: dark) {\n  ",
            Ui.Theme.css_vars ":root:not([data-theme=\"light\"])" dark,
            "}\n",
            Ui.Theme.css_vars "[data-theme=\"dark\"]" dark]
