// Shared helpers for the oak_ui test files (no #[test] defs here).

use oak::typed {Oak.Node, Oak.to_html}
use xml_html::html {Html.to_string}

/// The server rendering of a view, as the goldens compare it.
pub def ui_render {Msg : Type} (n : Oak.Node Msg) : String :=
    Html.to_string (Oak.to_html n)

pub def ui_renders {Msg : Type} (n : Oak.Node Msg) (want : String) : Bool :=
    String.beq (ui_render n) want

/// `needle` occurs in `hay` (for attribute/aria checks where a full golden
/// would be noise).
pub def ui_has {Msg : Type} (n : Oak.Node Msg) (needle : String) : Bool :=
    String.contains (ui_render n) needle
