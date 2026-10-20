/// The theme's classification and tint -- pure pins for the palette.
/// One classifier, two renderers (TextStyle per class + SGR codes),
/// so the two UIs' palettes cannot drift. (Housed apart from the
/// scroll tests: certain adjacent defs broke whole-file parse on the
/// current nightly even though each def parses alone -- see the note
/// in ui_tests.mo.)
use tui::core {style_default}
use tui::types {TextStyle}
use std::ansi {Color}
use weaver::policy {Mode}
use weaver::theme {LineClass, line_class, class_style, class_code, theme_line_style, theme_status_style, Theme.tint, theme_status_code, theme_line_style_with, theme_tline_style_with, theme_status_style_with, theme_border_style_with}

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
def test_theme_user_is_cyan : Bool :=
    theme_tline_style_with true true "hi" == ({ style_default with fg := some Color.cyan } : TextStyle)

/// The role flag wins over a prefix the user happened to type.
#[test]
def test_theme_user_line_keeps_its_voice : Bool :=
    theme_tline_style_with true true "error: hi" == ({ style_default with fg := some Color.cyan } : TextStyle)

#[test]
def test_theme_assistant_line_uses_the_prefix_classifier : Bool :=
    theme_tline_style_with true false "error: x" == ({ style_default with fg := some Color.red } : TextStyle)

#[test]
def test_theme_plain_reply_is_default : Bool :=
    theme_line_style "reply" == ({ fg := none, bg := none, bold := false, dim := false, italic := false, underline := false, strikethrough := false, reverse := false } : TextStyle)

// One enum, two renderers: every class maps on both sides.
#[test]
def test_class_style_and_code_agree_on_the_enum : Bool :=
    class_style LineClass.assistant == ({ fg := none, bg := none, bold := false, dim := false, italic := false, underline := false, strikethrough := false, reverse := false } : TextStyle)
        && class_code LineClass.plain == ""

#[test]
def test_theme_status_style_manual_gray : Bool :=
    theme_status_style Mode.manual == ({ style_default with dim := true, fg := some Color.bright_black } : TextStyle)
        && theme_status_style Mode.allow_edit == ({ style_default with dim := true, fg := some Color.yellow } : TextStyle)
        && theme_status_style Mode.auto == ({ style_default with dim := true, fg := some Color.red, bold := true } : TextStyle)

#[test]
def test_theme_status_style_plan_green : Bool :=
    theme_status_style Mode.plan == ({ style_default with dim := true, fg := some Color.green } : TextStyle)

#[test]
def test_theme_status_code_manual_gray : Bool :=
    theme_status_code Mode.manual == "\u{1b}[90;2m"
        && theme_status_code Mode.allow_edit == "\u{1b}[33;2m"
        && theme_status_code Mode.plan == "\u{1b}[32;2m"
        && theme_status_code Mode.auto == "\u{1b}[31;2;1m"

#[test]
def test_theme_tint_off_is_plain : Bool :=
    Theme.tint false "error: x" == "error: x"

// The diff coloring bug: a MULTI-line write takes each line's own
// class, red for the `-` row, green for the `+` row.
#[test]
def test_theme_tint_per_line : Bool :=
    Theme.tint true "error: a\n+ b\nplain" == "\u{1b}[31merror: a\u{1b}[0m\n\u{1b}[32m+ b\u{1b}[0m\nplain"

#[test]
def test_theme_tint_trailing_newline_kept : Bool :=
    Theme.tint true "error: x\n" == "\u{1b}[31merror: x\u{1b}[0m\n"
#[test]
def test_theme_off_is_the_plain_style : Bool :=
    theme_tline_style_with false true "hi" == style_default
        && theme_status_style_with false Mode.auto == style_default
        && theme_border_style_with false == style_default

#[test]
def test_theme_on_matches_the_palette : Bool :=
    theme_tline_style_with true true "hi" == ({ style_default with fg := some Color.cyan } : TextStyle)
        && theme_status_style_with true Mode.plan == theme_status_style Mode.plan
