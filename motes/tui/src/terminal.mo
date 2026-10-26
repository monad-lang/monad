// Terminal UI Library - Terminal Control
//
// Exactly one native backs this whole module: `term_ctl`, an
// I64-in/I64-out dispatch on the terminal (the `proc_read`/`proc_wait`
// merge pattern -- one entry point, one flag argument). Everything else
// here is pure ANSI string building on top of `IO.write_stdout`, so a
// compiled program's terminal behavior is inspectable by reading this
// file.
//
// The RawIO/IO split AGENTS.md documents: the native is declared at the
// `RawIO` level and the `Terminal.*` wrappers below build the
// user-facing `IO` type with `IO.mk`, keeping the C/Rust side a raw
// payload producer.

/// The one terminal-control native. `op`:
///   0 -- enter cbreak mode on stdin (1 on success; 0 when stdin is not
///        a tty, degrading instead of failing so tests never need a pty)
///   1 -- restore the terminal mode op 0 replaced (same result encoding)
///   2 -- the terminal size packed as `rows * 65536 + cols`; ioctl
///        TIOCGWINSZ on stdin then stdout, then the `COLUMNS`/`LINES`
///        environment variables, then 24x80
///   3 -- wait for stdin to become readable for up to `arg`
///        milliseconds (1 readable, 0 timed out, -1 error; readable at
///        EOF too -- pair with a read that returns "" to detect
///        closure; a NEGATIVE `arg` blocks indefinitely, poll(2)'s own
///        convention, which is how an app opts out of ticks). This is
///        the tick source: an app asks for input with a timeout, and
///        the timeout is the frame clock.
/// Any other op yields -1. `arg` is ignored by ops 0-2.
#[native "term_ctl"]
priv def term_ctl (op : I64) (arg : I64) : RawIO I64

/// Enter cbreak mode: ICANON and ECHO off, so key presses arrive one at
/// a time unechoed. Deliberately NOT full raw mode: ISIG is OFF (an
/// app that wants to handle Ctrl-C gets the `\u{3}` byte as
/// `Key.ctrl "c"` -- the double-press exit -- instead of the kernel
/// killing it; while a turn blocks inside `Cmd.perform` a queued
/// Ctrl-C byte waits, so a truly hung tool still needs /quit once the
/// turn ends), and OPOST stays on (a plain `"\n"` still prints).
/// `false` when stdin is not a tty -- nothing is changed then.
pub def Terminal.enter_raw_mode : IO Bool := do {
    let rc <- IO.mk (term_ctl 0 0);
    return (rc == 1)
}

/// Restore the terminal mode `enter_raw_mode` replaced. `false` when
/// stdin is not a tty or no mode was saved.
pub def Terminal.leave_raw_mode : IO Bool := do {
    let rc <- IO.mk (term_ctl 1 0);
    return (rc == 1)
}

/// Split a `term_ctl`-packed size into `(rows, cols)`. Separate so the
/// packing is testable without a terminal: `rows * 65536 + cols` with
/// both dimensions well under 65536.
pub def Terminal.unpack_size (packed : I64) : Pair I64 I64 :=
    let rows := packed / 65536 in
    Pair.pair rows (packed - rows * 65536)

/// The terminal size as `(rows, cols)`. Never fails: away from a tty
/// this is the `COLUMNS`/`LINES` environment variables, then 24x80.
pub def Terminal.size : IO (Pair I64 I64) := do {
    let packed <- IO.mk (term_ctl 2 0);
    return (Terminal.unpack_size packed)
}

/// Wait for stdin to be readable. `false` on timeout, `true` when a
/// read will not block -- including at EOF, where the read itself
/// returns "". A 0 timeout is a non-blocking check; a NEGATIVE
/// timeout blocks indefinitely (poll(2)'s own convention), which is
/// how an app that wants no ticks opts out of the frame clock.
pub def Terminal.poll (timeout_ms : I64) : IO Bool := do {
    let rc <- IO.mk (term_ctl 3 timeout_ms);
    return (rc == 1)
}

// ==================== ANSI string builders ====================
//
// Pure `*_code` defs (assertable in tests) plus one `IO.write_stdout`
// wrapper each. Coordinates are 0-based, the mote's convention
// everywhere; the ANSI sequences themselves are 1-based on the wire, so
// every builder that takes a position adds 1.

/// Move the cursor to a 0-based `(row, col)`.
pub def Terminal.cursor_move_code (row : I64) (col : I64) : String :=
    "\u{1b}[" ++ I64.to_string (row + 1) ++ ";" ++ I64.to_string (col + 1) ++ "H"

/// Make the cursor visible again.
pub def Terminal.cursor_show_code : String := "\u{1b}[?25h"

/// Hide the cursor (a TUI repaints the whole frame; a blinking cursor
/// inside it is noise).
pub def Terminal.cursor_hide_code : String := "\u{1b}[?25l"

/// Clear the whole screen. Does NOT move the cursor -- pair with
/// `cursor_move 0 0` for a "clear and go home".
/// Reset before erasing: the erase fills with the CURRENT attributes, so
/// a screen left in a colored SGR state clears into that color, and the
/// next unstyled write inherits it.
pub def Terminal.clear_screen_code : String := "\u{1b}[0m\u{1b}[2J"

/// The SGR reset on its own -- the exit path uses it so the shell never
/// inherits a mode tint (plan mode's status bar is green).
pub def Terminal.reset_style_code : String := "\u{1b}[0m"

/// Restrict scrolling (and cursor-movement clamping) to the 0-based
/// inclusive `[top, bottom]` rows.
pub def Terminal.set_scroll_region_code (top : I64) (bottom : I64) : String :=
    "\u{1b}[" ++ I64.to_string (top + 1) ++ ";" ++ I64.to_string (bottom + 1) ++ "r"

/// Drop the scroll region, restoring whole-screen scrolling.
pub def Terminal.reset_scroll_region_code : String := "\u{1b}[r"

/// Switch to the alternate screen buffer, leaving the user's scrollback
/// untouched. `leave_alt_screen` is the required pair -- an app that
/// enters and crashes without leaving strands the user there.
pub def Terminal.enter_alt_screen_code : String := "\u{1b}[?1049h"

/// Switch back to the primary screen buffer (and its scrollback).
pub def Terminal.leave_alt_screen_code : String := "\u{1b}[?1049l"

/// Enable mouse-button press/release reporting in SGR encoding
/// (`?1006` -- decimal, unambiguous coordinates; the legacy encodings
/// are ambiguous with arrow keys). Phase 6's input decoder consumes this.
/// Bracketed paste (DECSET 2004): the terminal wraps paste content in
/// `ESC[200~ … ESC[201~`, so the input layer can keep it literal.
pub def Terminal.enable_bracketed_paste_code : String := "\u{1b}[?2004h"
pub def Terminal.disable_bracketed_paste_code : String := "\u{1b}[?2004l"

/// `1002` = button-event tracking (press, release, and motion while a
/// button is held -- what drag-selection needs; `1000` reports no motion),
/// `1006` = SGR coordinates. Mouse reporting takes the terminal's own
/// selection away; most terminals restore it with Shift+drag.
pub def Terminal.enable_mouse_code : String := "\u{1b}[?1002h\u{1b}[?1006h"

/// Disable mouse reporting.
pub def Terminal.disable_mouse_code : String := "\u{1b}[?1002l\u{1b}[?1006l"

// ==================== IO wrappers ====================

pub def Terminal.cursor_move (row : I64) (col : I64) : IO Unit :=
    IO.write_stdout (Terminal.cursor_move_code row col)

pub def Terminal.cursor_show : IO Unit :=
    IO.write_stdout Terminal.cursor_show_code

pub def Terminal.cursor_hide : IO Unit :=
    IO.write_stdout Terminal.cursor_hide_code

pub def Terminal.clear_screen : IO Unit :=
    IO.write_stdout Terminal.clear_screen_code

pub def Terminal.reset_style : IO Unit :=
    IO.write_stdout Terminal.reset_style_code

pub def Terminal.set_scroll_region (top : I64) (bottom : I64) : IO Unit :=
    IO.write_stdout (Terminal.set_scroll_region_code top bottom)

pub def Terminal.reset_scroll_region : IO Unit :=
    IO.write_stdout Terminal.reset_scroll_region_code

pub def Terminal.enter_alt_screen : IO Unit :=
    IO.write_stdout Terminal.enter_alt_screen_code

pub def Terminal.leave_alt_screen : IO Unit :=
    IO.write_stdout Terminal.leave_alt_screen_code

pub def Terminal.enable_mouse : IO Unit :=
    IO.write_stdout Terminal.enable_mouse_code

pub def Terminal.disable_mouse : IO Unit :=
    IO.write_stdout Terminal.disable_mouse_code

pub def Terminal.enable_bracketed_paste : IO Unit :=
    IO.write_stdout Terminal.enable_bracketed_paste_code

pub def Terminal.disable_bracketed_paste : IO Unit :=
    IO.write_stdout Terminal.disable_bracketed_paste_code

// ==================== Tests ====================
//
// The `*_code` builders and `unpack_size` are pure, so these assert the
// exact wire strings without a terminal. The native itself is exercised
// end-to-end by a compiled run (see the plan's verification), not here:
// `#[test]` defs are pure `Bool`, and away from a tty the mode ops'
// results are environment-dependent anyway.

#[test]
def test_cursor_move_origin : Bool :=
    Terminal.cursor_move_code 0 0 == "\u{1b}[1;1H"

#[test]
def test_cursor_move_offset_is_one_based_on_wire : Bool :=
    Terminal.cursor_move_code 2 4 == "\u{1b}[3;5H"

#[test]
def test_cursor_show_hide_codes : Bool :=
    Terminal.cursor_show_code == "\u{1b}[?25h"
    && Terminal.cursor_hide_code == "\u{1b}[?25l"

#[test]
def test_clear_screen_code : Bool :=
    Terminal.clear_screen_code == "\u{1b}[0m\u{1b}[2J"
        && Terminal.reset_style_code == "\u{1b}[0m"

#[test]
def test_scroll_region_codes : Bool :=
    Terminal.set_scroll_region_code 0 23 == "\u{1b}[1;24r"
    && Terminal.reset_scroll_region_code == "\u{1b}[r"

#[test]
def test_alt_screen_codes : Bool :=
    Terminal.enter_alt_screen_code == "\u{1b}[?1049h"
    && Terminal.leave_alt_screen_code == "\u{1b}[?1049l"

#[test]
def test_mouse_mode_codes : Bool :=
    Terminal.enable_mouse_code == "\u{1b}[?1002h\u{1b}[?1006h"
    && Terminal.disable_mouse_code == "\u{1b}[?1002l\u{1b}[?1006l"

#[test]
def test_unpack_size_roundtrip : Bool :=
    match Terminal.unpack_size (24 * 65536 + 80) {
        Pair.pair rows cols => rows == 24 && cols == 80
    }

#[test]
def test_unpack_size_one_by_one : Bool :=
    match Terminal.unpack_size (65536 + 1) {
        Pair.pair rows cols => rows == 1 && cols == 1
    }

#[test]
def test_unpack_size_zero : Bool :=
    match Terminal.unpack_size 0 {
        Pair.pair rows cols => rows == 0 && cols == 0
    }
