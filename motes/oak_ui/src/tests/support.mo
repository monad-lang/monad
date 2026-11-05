// Shared helpers for the oak_ui test files (no #[test] defs here).

use std::list {List.length}
use web_event::event {WebEvent, HandlerResult}
use oak::typed {Oak.Node, Oak.Lowered, Oak.lower, Oak.to_html}
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

/// The message the FIRST handler in a view produces for `e` (handlers are
/// collected in document order by `Oak.lower`).
pub def ui_first_msg {Msg : Type} (n : Oak.Node Msg) (e : WebEvent) : Option Msg :=
    match Oak.lower n {
        Oak.Lowered.lowered _ handlers =>
            match handlers {
                List.empty => Option.none,
                List.cons entry _ =>
                    match entry {
                        Pair.pair _ h => match h e { HandlerResult.handler_result m _ _ => m }
                    },
            },
    }

/// Whether the first handler asks for `preventDefault`.
pub def ui_first_prevents {Msg : Type} (n : Oak.Node Msg) (e : WebEvent) : Bool :=
    match Oak.lower n {
        Oak.Lowered.lowered _ handlers =>
            match handlers {
                List.empty => false,
                List.cons entry _ =>
                    match entry {
                        Pair.pair _ h => match h e { HandlerResult.handler_result _ p _ => p }
                    },
            },
    }

/// How many handlers a view registers.
pub def ui_handler_count {Msg : Type} (n : Oak.Node Msg) : I64 :=
    match Oak.lower n { Oak.Lowered.lowered _ handlers => List.length handlers }
