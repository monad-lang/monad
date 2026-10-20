/// The palette -- weaver.md Phase 11: the colors both UIs share.
/// ONE classification, TWO renderers: `line_class` names a line's role
/// by prefix, and the TUI renders it as a `TextStyle` while dumb mode
/// renders the matching SGR code -- one enum each side renders from,
/// so the two palettes cannot drift. Dumb side suppressed when the
/// session's colors flag is off (`NO_COLOR`; there is deliberately no
/// auto tty probe -- a piped consumer should set NO_COLOR, the
/// informal standard). `Diff.render` stays uncolored: classification
/// is by the `- `/`+ ` prefix, so any line that carries one is colored
/// wherever it surfaces. `Theme.tint` maps over LINES (a multi-line
/// write is not one class just because its first line is).
use tui::types {TextStyle}
use tui::core {style_default}
use std::ansi {Color}
use weaver::policy {Mode}

pub type LineClass {
    user,
    assistant,
    running,
    error,
    diff_plus,
    diff_minus,
    hint,
    plain,
}

/// The role of a line, by prefix: diff marks, error/denial entries,
/// running rows, the Ctrl+C hint -- everything else is the assistant's
/// voice. The user's own role is data (`TLine.user`), not a prefix.
#[terminating]
pub def line_class (line : String) : LineClass :=
    if String.starts_with "+ " line then LineClass.diff_plus
    else if String.starts_with "- " line then LineClass.diff_minus
    else if String.starts_with "error: " line then LineClass.error
    else if String.starts_with "denied: " line then LineClass.error
    else if String.starts_with "refused: " line then LineClass.error
    else if String.starts_with "[approve] " line then LineClass.running
    else if String.starts_with "[running " line then LineClass.running
    else if String.starts_with "press Ctrl+C" line then LineClass.hint
    else LineClass.assistant

/// The TUI side: a class's `TextStyle`.
pub def class_style (c : LineClass) : TextStyle :=
    match c {
        LineClass.user => { style_default with fg := some Color.cyan },
        LineClass.assistant => style_default,
        LineClass.running => { style_default with dim := true, fg := some Color.cyan },
        LineClass.error => { style_default with fg := some Color.red },
        LineClass.diff_plus => { style_default with fg := some Color.green },
        LineClass.diff_minus => { style_default with fg := some Color.red },
        LineClass.hint => { style_default with dim := true },
        LineClass.plain => style_default,
    }

pub def theme_line_style (line : String) : TextStyle :=
    class_style (line_class line)

/// Color-aware selectors: off returns the plain style -- the `--no-color`
/// path through the TUI (dumb mode already gates its own SGR codes).
pub def theme_line_style_with (colors : Bool) (line : String) : TextStyle :=
    if colors then theme_line_style line else style_default

/// A transcript line's style: the role flag wins (a user line stays cyan
/// even when its text starts with `error:`), everything else keeps the
/// semantic prefix classification.
pub def theme_tline_style_with (colors : Bool) (user : Bool) (line : String) : TextStyle :=
    if user
    then (if colors then class_style LineClass.user else style_default)
    else theme_line_style_with colors line

pub def theme_status_style_with (colors : Bool) (mode : Mode) : TextStyle :=
    if colors then theme_status_style mode else style_default

pub def theme_border_style_with (colors : Bool) : TextStyle :=
    if colors then theme_border_style else style_default

/// The startup banner's parts (theme.mo owns the palette, so the banner's
/// colors live beside every other one).
pub type BannerPart {
    frame,
    warp,
    shuttle,
    word_cyan,
    word_blue,
    word_magenta,
    tagline,
}

pub def theme_banner_style_with (colors : Bool) (part : BannerPart) : TextStyle :=
    if colors
    then match part {
        BannerPart.frame => { style_default with fg := some Color.blue },
        BannerPart.warp => { style_default with fg := some Color.blue, dim := true },
        BannerPart.shuttle => { style_default with fg := some Color.cyan, bold := true },
        BannerPart.word_cyan => { style_default with fg := some Color.cyan, bold := true },
        BannerPart.word_blue => { style_default with fg := some Color.blue, bold := true },
        BannerPart.word_magenta => { style_default with fg := some Color.magenta, bold := true },
        BannerPart.tagline => { style_default with fg := some Color.yellow, dim := true },
    }
    else style_default

/// The transcript/overlay border's style: dim -- structure should read
/// quieter than any live text (the border chars inherit the ambient
/// style, so the BORDER wraps in this, not the rows).
pub def theme_border_style : TextStyle :=
    { style_default with dim := true }

/// The dumb side: a class's SGR code (colors first, then attributes --
/// the same order `tui::core::style_to_ansi` builds them in).
pub def class_code (c : LineClass) : String :=
    match c {
        LineClass.user => "\u{1b}[36m",
        LineClass.assistant => "",
        LineClass.running => "\u{1b}[36;2m",
        LineClass.error => "\u{1b}[31m",
        LineClass.diff_plus => "\u{1b}[32m",
        LineClass.diff_minus => "\u{1b}[31m",
        LineClass.hint => "\u{1b}[2m",
        LineClass.plain => "",
    }

/// The dumb line's tint: EVERY line of the write classified and
/// wrapped ALONE (a multi-line write used to take its first line's
/// class for the whole block -- the diff's `-`/`+` rows never
/// colored), plain when off or unclassified.
pub def Theme.tint (colors : Bool) (text : String) : String :=
    if Bool.not colors
    then text
    else if String.is_empty text
    then text
    else theme_tint_text (theme_split_lines text)

/// One line per `\n`; a trailing newline keeps its empty last line so
/// the join reproduces the text's own shape.
#[partial]
pub def theme_split_lines (s : String) : List String :=
    if String.is_empty s then List.empty else split_go s 0 0

#[terminating]
def split_go (s : String) (i : I64) (line_start : I64) : List String :=
    if Bool.not (i < String.length s)
    then List.cons (String.drop line_start s) List.empty
    else if String.slice s i 1 == "\n"
    then List.cons (String.slice s line_start (i - line_start)) (split_go s (i + 1) (i + 1))
    else split_go s (i + 1) line_start

/// Join the per-line tints back, `"\n"`-separated, in order.
#[terminating]
def theme_tint_text (lines : List String) : String :=
    match lines {
        List.empty => "",
        List.cons l rest =>
            match rest {
                List.empty => theme_wrap l,
                _ => String.concat (theme_wrap l) (String.concat "\n" (theme_tint_text rest)),
            },
    }

/// A single line's wrap: class -> SGR code around it; a blank line and
/// an unclassified line pass through bare.
#[terminating]
def theme_wrap (line : String) : String :=
    let code := class_code (line_class line) in
    if code == "" then line else String.concat code (String.concat line "\u{1b}[0m")

/// The status bar's code, by mode (the same color the TUI chip
/// carries): dim yellow -- the Claude-Code-like statusbar -- plan GREEN
/// (read-only is the one mode that is always safe), and the `auto`
/// trust warning red.
pub def theme_status_code (mode : Mode) : String :=
    match mode {
        Mode.auto => "\u{1b}[31;2;1m",
        Mode.plan => "\u{1b}[32;2m",
        Mode.manual => "\u{1b}[90;2m",
        _ => "\u{1b}[33;2m",
    }

/// The TUI status bar's style per mode: dim GRAY for manual (the
/// statusbar's own voice), dim yellow for `allow_edit` (its edit-enabled
/// warning tint), plan green, and the `auto` warning red -- the WARNING:
/// prefix the status text already carries is what turns red.
pub def theme_status_style (mode : Mode) : TextStyle :=
    match mode {
        Mode.auto => { style_default with dim := true, fg := some Color.red, bold := true },
        Mode.plan => { style_default with dim := true, fg := some Color.green },
        Mode.manual => { style_default with dim := true, fg := some Color.bright_black },
        _ => { style_default with dim := true, fg := some Color.yellow },
    }