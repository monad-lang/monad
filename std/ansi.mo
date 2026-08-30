// Standard library: ANSI terminal color and style codes.
//
// `colors_enabled` only checks NO_COLOR / FORCE_COLOR / TERM via IO.get_env —
// there is no isatty/TTY check, so piped output is not auto-disabled unless
// NO_COLOR is set. This is a deliberate scope cut (see
// implementations/ansi-colors.md in the plans repo), not an oversight.

use io {IO}
open IO {get_env}

type Color {
    black, red, green, yellow, blue, magenta, cyan, white,
    bright_black, bright_red, bright_green, bright_yellow,
    bright_blue, bright_magenta, bright_cyan, bright_white,
    color256 (code : U8),
    true_color (r : U8) (g : U8) (b : U8)
}

type Style {
    bold, dim, italic, underline, blink, reverse, hidden, strikethrough
}

type Modifier {
    fg (color : Color),
    bg (color : Color),
    style (s : Style),
    reset
}

def color_fg_code (c : Color) : String :=
    match c {
        black => "30", red => "31", green => "32", yellow => "33",
        blue => "34", magenta => "35", cyan => "36", white => "37",
        bright_black => "90", bright_red => "91", bright_green => "92", bright_yellow => "93",
        bright_blue => "94", bright_magenta => "95", bright_cyan => "96", bright_white => "97",
        color256 code => "38;5;" ++ U8.to_string code,
        true_color r g b => "38;2;" ++ U8.to_string r ++ ";" ++ U8.to_string g ++ ";" ++ U8.to_string b
    }

def color_bg_code (c : Color) : String :=
    match c {
        black => "40", red => "41", green => "42", yellow => "43",
        blue => "44", magenta => "45", cyan => "46", white => "47",
        bright_black => "100", bright_red => "101", bright_green => "102", bright_yellow => "103",
        bright_blue => "104", bright_magenta => "105", bright_cyan => "106", bright_white => "107",
        color256 code => "48;5;" ++ U8.to_string code,
        true_color r g b => "48;2;" ++ U8.to_string r ++ ";" ++ U8.to_string g ++ ";" ++ U8.to_string b
    }

def style_code (s : Style) : String :=
    match s {
        bold => "1", dim => "2", italic => "3", underline => "4",
        blink => "5", reverse => "7", hidden => "8", strikethrough => "9"
    }

/// Constructs an ANSI escape sequence for a single modifier.
def escape (m : Modifier) : String :=
    match m {
        fg c => "\u{1b}[" ++ color_fg_code c ++ "m",
        bg c => "\u{1b}[" ++ color_bg_code c ++ "m",
        style s => "\u{1b}[" ++ style_code s ++ "m",
        reset => "\u{1b}[0m"
    }

def red (s : String) : String :=
    escape (Modifier.fg Color.red) ++ s ++ escape Modifier.reset

def green (s : String) : String :=
    escape (Modifier.fg Color.green) ++ s ++ escape Modifier.reset

def yellow (s : String) : String :=
    escape (Modifier.fg Color.yellow) ++ s ++ escape Modifier.reset

def bold (s : String) : String :=
    escape (Modifier.style Style.bold) ++ s ++ escape Modifier.reset

def dim (s : String) : String :=
    escape (Modifier.style Style.dim) ++ s ++ escape Modifier.reset

/// Bold red — for failure output.
def fail (s : String) : String :=
    bold (red s)

/// Bold green — for success output.
def pass (s : String) : String :=
    bold (green s)

/// Yellow — for warning output.
pub def warn (s : String) : String :=
    escape (Modifier.fg Color.yellow) ++ s ++ escape Modifier.reset

def env_flag_set (v : Option String) : Bool :=
    match v {
        some _ => true,
        none => false
    }

def term_is_dumb (v : Option String) : Bool :=
    match v {
        some t => t == "dumb",
        none => false
    }

/// Whether ANSI colors should be used, per NO_COLOR / FORCE_COLOR / TERM.
/// NO_COLOR (https://no-color.org) always wins; FORCE_COLOR forces colors on
/// unless NO_COLOR is set; otherwise colors are on unless TERM=dumb.
def colors_enabled : IO Bool :=
    get_env "NO_COLOR" >>= fn (no_color : Option String) =>
    if env_flag_set no_color then Monad.pure false
    else
        get_env "FORCE_COLOR" >>= fn (force_color : Option String) =>
        if env_flag_set force_color then Monad.pure true
        else
            get_env "TERM" >>= fn (term : Option String) =>
            Monad.pure (Bool.not (term_is_dumb term))

/// Wraps `s` in `color` if colors are enabled, otherwise returns `s` unchanged.
pub def colored (s : String) (color : Color) : IO String :=
    colors_enabled >>= fn (enabled : Bool) =>
    if enabled then Monad.pure (escape (Modifier.fg color) ++ s ++ escape Modifier.reset)
    else Monad.pure s

// ---------- Tests ----------


#[test]
def test_escape_reset : Bool :=
    escape Modifier.reset == "\u{1b}[0m"

#[test]
def test_escape_fg_red : Bool :=
    escape (Modifier.fg Color.red) == "\u{1b}[31m"

#[test]
def test_escape_bg_blue : Bool :=
    escape (Modifier.bg Color.blue) == "\u{1b}[44m"

#[test]
def test_escape_style_bold : Bool :=
    escape (Modifier.style Style.bold) == "\u{1b}[1m"

#[test]
def test_escape_color256 : Bool :=
    escape (Modifier.fg (Color.color256 42u8)) == "\u{1b}[38;5;42m"

#[test]
def test_escape_true_color : Bool :=
    escape (Modifier.fg (Color.true_color 1u8 2u8 3u8)) == "\u{1b}[38;2;1;2;3m"

#[test]
def test_red_wraps_and_resets : Bool :=
    red "x" == "\u{1b}[31mx\u{1b}[0m"

#[test]
def test_green_wraps_and_resets : Bool :=
    green "x" == "\u{1b}[32mx\u{1b}[0m"

#[test]
def test_bold_wraps_and_resets : Bool :=
    bold "x" == "\u{1b}[1mx\u{1b}[0m"

#[test]
def test_fail_is_bold_red : Bool :=
    fail "x" == bold (red "x")

#[test]
def test_pass_is_bold_green : Bool :=
    pass "x" == bold (green "x")

#[test]
def test_env_flag_set_some : Bool :=
    env_flag_set (Option.some "1")

#[test]
def test_env_flag_set_none : Bool :=
    Bool.not (env_flag_set Option.none)

#[test]
def test_term_is_dumb_true : Bool :=
    term_is_dumb (Option.some "dumb")

#[test]
def test_term_is_dumb_false_for_other_term : Bool :=
    Bool.not (term_is_dumb (Option.some "xterm-256color"))

#[test]
def test_term_is_dumb_false_when_unset : Bool :=
    Bool.not (term_is_dumb Option.none)
