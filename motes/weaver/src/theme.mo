/// The palette -- weaver.md Phase 11: the colors both UIs share.
/// TUI side: `TextStyle` per line class (the render contracts one style
/// per row); dumb side: SGR wraps by line-prefix classification,
/// suppressed when the session's colors flag is off (`NO_COLOR`; there
/// is deliberately no auto tty probe -- a piped consumer should set
/// NO_COLOR, the informal standard). `Diff.render` stays uncolored:
/// classification is by the `- `/`+ ` prefix, so any line that
/// carries one is colored wherever it surfaces.
use tui::types {TextStyle}
use tui::core {style_default}
use std::ansi {Color}
use weaver::policy {Mode}

pub struct Theme {
    you : TextStyle,
    assistant : TextStyle,
    running : TextStyle,
    error : TextStyle,
    diff_plus : TextStyle,
    diff_minus : TextStyle,
    status : TextStyle,
    hint : TextStyle,
}

pub def theme_default : Theme :=
    {
        you := { style_default with dim := true },
        assistant := style_default,
        running := { style_default with dim := true, fg := some Color.cyan },
        error := { style_default with fg := some Color.red },
        diff_plus := { style_default with fg := some Color.green },
        diff_minus := { style_default with fg := some Color.red },
        status := { style_default with dim := true },
        hint := { style_default with dim := true },
    }

/// A transcript/overlay line's style, by prefix: diff marks, error
/// entries, running-tool rows, the Ctrl+C hint -- everything else is
/// the assistant's (plain) voice.
pub def theme_line_style (line : String) : TextStyle :=
    let theme := theme_default in
    if String.starts_with "+ " line then theme.diff_plus
    else if String.starts_with "- " line then theme.diff_minus
    else if String.starts_with "error: " line then theme.error
    else if String.starts_with "denied: " line then theme.error
    else if String.starts_with "[approve] " line then theme.running
    else if String.starts_with "[running " line then theme.running
    else if String.starts_with "press Ctrl+C" line then theme.hint
    else if String.starts_with "you: " line then theme.you
    else theme.assistant

/// The status bar's style per mode: `auto` is the red trust warning,
/// `plan` cyan, every other mode dim.
pub def theme_status_style (mode : Mode) : TextStyle :=
    match mode {
        Mode.auto => { style_default with dim := true, fg := some Color.red, bold := true },
        Mode.plan => { style_default with dim := true, fg := some Color.cyan },
        _ => { style_default with dim := true },
    }

// ── the dumb side: SGR string wraps, prefix-classified ────────────────

def theme_code_red : String := "\u{1b}[31m"
def theme_code_green : String := "\u{1b}[32m"
def theme_code_cyan_dim : String := "\u{1b}[36;2m"
def theme_code_dim : String := "\u{1b}[2m"

/// The dumb line's SGR code by the same classification, "" = plain.
#[terminating]
def theme_line_code (line : String) : String :=
    if String.starts_with "+ " line then theme_code_green
    else if String.starts_with "- " line then theme_code_red
    else if String.starts_with "error: " line then theme_code_red
    else if String.starts_with "denied: " line then theme_code_red
    else if String.starts_with "[approve] " line then theme_code_cyan_dim
    else if String.starts_with "[running " line then theme_code_cyan_dim
    else if String.starts_with "press Ctrl+C" line then theme_code_dim
    else if String.starts_with "you: " line then theme_code_dim
    else ""

/// Wrap one dumb line in its SGR code (plain when off or unclassified).
pub def Theme.tint (colors : Bool) (line : String) : String :=
    if Bool.not colors
    then line
    else
        let code := theme_line_code line in
        if code == "" then line else String.concat code (String.concat line "\u{1b}[0m")

/// The dumb status line's code, by mode (the same color the TUI chip
/// carries).
pub def theme_status_code (mode : Mode) : String :=
    match mode {
        Mode.auto => "\u{1b}[31;2;1m",
        Mode.plan => "\u{1b}[36;2m",
        _ => theme_code_dim,
    }