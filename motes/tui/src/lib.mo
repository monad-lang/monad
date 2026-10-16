// The tui mote's library root -- bare `use tui` resolves here.
//
// Six modules, in the order a frame moves through them: `types` (the
// value types -- a `Rect`, a styled `Cell`, a `Screen` of cells, and the
// input events -- with their derived `BEq`/`Lens` instances), `core` (the
// functions over those types: style helpers, screen accessors, `Screen`'s
// hand-rolled `BEq`), `layout` (splitting a `Rect` by `LayoutSize`),
// `widget` (the widget tree and its smart constructors), `render`
// (tree -> `Screen` -> `CellDelta`s -> one ANSI string) and `terminal`
// (the one terminal-control native plus the ANSI escape builders).
//
// One type group per module, which is the rule `build/src/lib.mo` set. The
// functions are reached by naming the module (`use tui::render {render}`);
// this file's job is to make `use tui` resolve. No `{*}` globs: a glob here
// would pull six namespaces into every importer's scope.

pub use lib::types {Rect, TextStyle, Cell, LayoutSize, MouseButton, Key, MouseEvent, Event, Screen, CellDelta}
pub use lib::core {}
pub use lib::layout {}
pub use lib::terminal {}
pub use lib::input {Input.decode, Input.pending_escape, Input.produce, InputReader, input_reader}
pub use lib::frp {EventStream, Signal}
pub use lib::widgets::input {InputState, input_state, handle_input_key}
pub use lib::widgets::list {ListState, list_state, handle_list_key}
pub use lib::widget {BorderStyle, LeafWidget, SizedWidget, DecoratorKind, Widget, text_input, list}
pub use lib::render {BorderChars}
