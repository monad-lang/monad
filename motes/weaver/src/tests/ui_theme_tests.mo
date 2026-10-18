/// The theme's classification and tint -- pure pins for the palette.
/// (Housed apart from the scroll tests: certain adjacent defs broke
/// whole-file parse on the current nightly even though each def parses
/// alone -- see the note in ui_tests.mo.)
use tui::core {style_default}
use tui::types {TextStyle}
use std::ansi {Color}
use weaver::policy {Mode}
use weaver::theme {theme_line_style, Theme.tint, theme_status_style, theme_default, Theme}

#[test]
def test_theme_diff_plus_is_green : Bool :=
    theme_line_style "+ added" == ({ style_default with fg := some Color.green } : TextStyle)

#[test]
def test_theme_diff_minus_is_red : Bool :=
    theme_line_style "- removed" == ({ style_default with fg := some Color.red } : TextStyle)

#[test]
def test_theme_error_is_red : Bool :=
    theme_line_style "error: provider: x" == ({ style_default with fg := some Color.red } : TextStyle)

#[test]
def test_theme_running_is_dim_cyan : Bool :=
    theme_line_style "[running read]" == ({ style_default with dim := true, fg := some Color.cyan } : TextStyle)

#[test]
def test_theme_plain_reply_is_default : Bool :=
    theme_line_style "reply" == ({ fg := none, bg := none, bold := false, dim := false, italic := false, underline := false, strikethrough := false, reverse := false } : TextStyle)

#[test]
def test_theme_status_style_by_mode : Bool :=
    theme_status_style Mode.auto == ({ style_default with dim := true, fg := some Color.red, bold := true } : TextStyle)
        && theme_status_style Mode.plan == ({ style_default with dim := true, fg := some Color.cyan } : TextStyle)

#[test]
def test_theme_tint_off_is_plain : Bool :=
    Theme.tint false "error: x" == "error: x"

#[test]
def test_theme_tint_classes : Bool :=
    Theme.tint true "error: x" == "\u{1b}[31merror: x\u{1b}[0m"
        && Theme.tint true "+ added" == "\u{1b}[32m+ added\u{1b}[0m"
        && Theme.tint true "plain reply" == "plain reply"

#[test]
def test_theme_defaults_no_gaps : Bool :=
    let t : Theme := theme_default in
    t.assistant == ({ fg := none, bg := none, bold := false, dim := false, italic := false, underline := false, strikethrough := false, reverse := false } : TextStyle)