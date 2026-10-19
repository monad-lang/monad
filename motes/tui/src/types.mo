// Terminal UI Library - Value Types
//
// The mote's type declarations, and nothing else: every `BEq` instance
// except `Screen`'s is `#[derive BEq]` here, and `Rect`/`TextStyle` also
// derive their field lenses. Keeping the derives in a module with no
// function bodies is load-bearing for the Rust host: expanding a derive
// re-checks the whole derive-bearing file (plus its use-closure) in the
// meta-capture path, and that path loses def-signature expected types --
// a file mixing derives with ordinary defs fails it on every struct
// literal and dot access (`cannot infer the type of { .. }`).
// `types.mo` has neither, so the capture is clean on both compilers.
//
// `Screen` is the exception: it compares `List (List Cell)` and generic
// `BEq (List A)` dispatch through a custom element type's instance is
// unreliable at runtime, so its `BEq` is hand-rolled in `core.mo` next to
// the `cell_list_beq` helper it needs.

// The derive backend. The compiler's unused-import analysis does not see
// macro-name dispatch as a reference, so these read as unused -- they are
// not; removing them makes every derive below fail with
// "macro `derive_beq` not found".
use std::derive {derive_beq, derive_lens}
use std::ansi { Color }
// `Lens` (the type) and `lens` (its builder) are referenced by name inside
// the defs `#[derive Lens]` generates.
use init::optics { Lens, lens }

/// A rectangular area of the terminal
#[derive BEq Lens]
pub struct Rect {
    x: I64,
    y: I64,
    width: I64,
    height: I64
}

/// A composable text style: colors plus attribute flags. Unlike
/// `ansi.Modifier` (which represents a single fg/bg/style/reset code), a
/// `TextStyle` can express e.g. bold *and* a foreground color at the same time.
#[derive BEq Lens]
pub struct TextStyle {
    fg: Option Color := none,
    bg: Option Color := none,
    bold: Bool := false,
    dim: Bool := false,
    italic: Bool := false,
    underline: Bool := false,
    strikethrough: Bool := false,
    reverse: Bool := false
}

/// A single character cell with styling
#[derive BEq]
pub struct Cell {
    char: String,
    style: TextStyle
}

/// Layout size constraints for flexible sizing
#[derive BEq]
pub type LayoutSize {
    /// Fixed size in units
    fixed (n : I64),
    /// Fill available space, optionally with a weight
    fill (weight : I64),
    /// Minimum size
    min (n : I64),
    /// Maximum size
    max (n : I64)
}

/// Mouse buttons
#[derive BEq]
pub type MouseButton {
    left,
    right,
    middle,
    scroll_up,
    scroll_down
}

/// Keyboard keys
#[derive BEq]
pub type Key {
    /// A regular character key
    char (c : String),
    /// Enter/Return key
    enter,
    /// Tab key
    tab,
    /// Backspace key
    backspace,
    /// Escape key
    escape,
    /// Arrow keys
    up,
    down,
    left,
    right,
    /// Navigation keys
    home,
    end,
    page_up,
    page_down,
    /// Edit keys
    delete,
    insert,
    /// Function keys (F1-F12). Spelled out rather than `f`: a one-letter
    /// constructor in a whole-program namespace shadows same-named locals
    /// everywhere, and this one used to break `init/src/io.mo`'s
    /// `Monad IO`.bind (`match a { io a => f a }`) into a constructor
    /// application -- silently stopping every `do` block in any program
    /// that loaded this module. Fixed in the compiler
    /// (`try_compile_constructor_app_db`, pinned by
    /// `slow_tests/src/codegen_ctor_shadows_param_tests.mo`), so the name
    /// is now a choice rather than a workaround -- but it keeps this mote
    /// usable on a toolchain that predates the fix.
    function_key (n : I64),
    /// Control + character
    ctrl (c : String),
    /// Alt + character
    alt (c : String)
}

/// Mouse events
#[derive BEq]
pub type MouseEvent {
    /// Mouse button pressed at position
    press (button : MouseButton) (row : I64) (col : I64),
    /// Mouse button released at position
    release (button : MouseButton) (row : I64) (col : I64),
    /// Mouse drag (button held down and moved)
    drag (button : MouseButton) (row : I64) (col : I64),
    /// Mouse wheel scroll up
    scroll_up (row : I64) (col : I64),
    /// Mouse wheel scroll down
    scroll_down (row : I64) (col : I64)
}

/// Terminal events
#[derive BEq]
pub type Event {
    /// Key press event
    key (k : Key),
    /// Mouse event
    mouse (m : MouseEvent),
    /// Terminal resize event
    resize (rows : I64) (cols : I64),
    /// Tick event (frame update)
    tick,
    /// Bracketed-paste content, verbatim (newlines included).
    paste (s : String)
}

/// The screen buffer — a 2D grid of cells represented as a list of rows
pub struct Screen {
    rows: I64,
    cols: I64,
    row_cells: List (List Cell)
}

/// A delta representing a change to a single cell
#[derive BEq]
pub type CellDelta {
    /// Position of the cell to change
    set (row : I64) (col : I64) (cell : Cell),
    /// Clear a cell (set to default/empty)
    clear (row : I64) (col : I64)
}
