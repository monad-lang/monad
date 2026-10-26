// Oak's library root -- bare `use oak` resolves here.
//
// The re-exports are explicit (no globs), following xml_html's lib.mo.
// The raw markup types are re-exported too, so an application can mix plain
// `Html.Node` trees into a typed view (`Oak.of_html`) or serialize one
// without adding an `xml_html` dependency.
//
// `Oak.Node`/`Oak.Attr` are the typed view layer (event handlers ride in
// `Oak.Attr.on`); `Oak.lower` turns a view into the plain markup tree plus
// the handler table the browser runtime dispatches through.

pub use xml_html::html {
    Html.Node, Html.Attr, Html.RenderOpts, Html.default_opts,
    Html.to_string, Html.to_string_with, Html.beq,
}

pub use lib::typed {
    Oak.Node, Oak.Attr, Oak.Lowered,
    Oak.of_html, Oak.of_attr, Oak.text, Oak.lower, Oak.to_html,
    Handler.id, Handler.spec, Handler.spec_of, Handler.prefix,
}

pub use lib::events {
    Subscription, Subscription.window_msg, Subscription.document_msg, Subscription.animation_frame_msg,
    Html.on, Html.msg, Html.msg_with,
    Html.on_click, Html.on_click_with, Html.on_dblclick, Html.on_contextmenu,
    Html.on_auxclick, Html.on_mousedown, Html.on_mouseup, Html.on_mousemove,
    Html.on_mouseenter, Html.on_mouseleave, Html.on_mouseover, Html.on_mouseout,
    Html.on_pointerdown, Html.on_pointerup, Html.on_pointermove,
    Html.on_pointerover, Html.on_pointerout, Html.on_pointerenter,
    Html.on_pointerleave, Html.on_pointercancel, Html.on_wheel,
    Html.on_keydown, Html.on_keyup, Html.on_focus, Html.on_blur,
    Html.on_focusin, Html.on_focusout, Html.on_input, Html.on_change,
    Html.on_submit, Html.on_submit_prevent, Html.on_reset, Html.on_scroll,
    Html.on_touchstart, Html.on_touchmove, Html.on_touchend, Html.on_touchcancel,
    Html.on_animationstart, Html.on_animationend, Html.on_animationiteration,
    Html.on_transitionend, Html.on_load, Html.on_error,
    Html.on_dragstart, Html.on_dragstart_msg, Html.on_drag, Html.on_dragenter,
    Html.on_dragleave, Html.on_dragend, Html.on_dragend_msg, Html.on_dragover,
    Html.on_drop, Html.on_drop_msg,
    Html.on_copy, Html.on_copy_msg, Html.on_cut, Html.on_cut_msg,
    Html.on_paste, Html.on_paste_msg,
    Html.on_play, Html.on_pause, Html.on_ended, Html.on_timeupdate,
    Html.on_loadedmetadata, Html.on_canplay, Html.on_volumechange, Html.on_timeupdate_msg,
    Html.drag_payload, Html.drag_effect, Html.drop_effect, Html.copy_text,
}

// The event vocabulary, re-exported so an application that depends on oak
// alone can name an `WebEvent` and build a `HandlerResult`.
pub use web_event::event {
    WebEvent, FileInfo, ListenerFlags, HandlerResult,
    WebEvent.mod_shift, WebEvent.mod_ctrl, WebEvent.mod_alt, WebEvent.mod_meta,
    ListenerFlags.none, ListenerFlags.letters, ListenerFlags.encode,
    HandlerResult.msg, HandlerResult.ignore, HandlerResult.prevent,
}

pub use lib::elements {
    Html.id_, Html.class_, Html.href, Html.src, Html.alt, Html.type_, Html.value_,
    Html.placeholder, Html.name_, Html.for_, Html.open_, Html.data, Html.style_attr,
    Html.disabled, Html.checked, Html.required, Html.readonly, Html.selected,
    Html.autofocus, Html.hidden,

    Html.div, Html.span, Html.p, Html.a, Html.ul, Html.ol, Html.li,
    Html.h1, Html.h2, Html.h3, Html.h4, Html.h5, Html.h6,
    Html.header, Html.footer, Html.nav, Html.main_, Html.section, Html.article, Html.aside,

    Html.table, Html.thead, Html.tbody, Html.tfoot, Html.tr, Html.th, Html.td,
    Html.caption, Html.colgroup,
    Html.form, Html.label, Html.fieldset, Html.legend, Html.select, Html.option,
    Html.optgroup, Html.textarea, Html.button, Html.datalist, Html.output,
    Html.input, Html.img, Html.br, Html.hr, Html.meta, Html.link, Html.col,
    Html.source, Html.area, Html.base, Html.embed, Html.track, Html.wbr,
    Html.script, Html.style, Html.title, Html.head, Html.body,
    Html.canvas, Html.video, Html.audio,

    Html.node, Html.void, Html.text, Html.html_node, Html.raw, Html.comment,
    Html.doctype, Html.fragment, Html.document, Html.navbar, Html.card
}

pub use lib::elements {
    Html.attr, Html.bool_attr, Html.role, Html.aria,
    Html.key_attr, Html.key,
    Html.method_, Html.action, Html.enctype, Html.enctype_multipart,
    Html.target, Html.rel, Html.charset, Html.accept,
    Html.width, Html.height, Html.min_, Html.max_, Html.step,
    Html.pattern_, Html.autocomplete, Html.minlength, Html.maxlength,
    Html.multiple, Html.novalidate,
    Html.draggable, Html.contenteditable, Html.translate, Html.spellcheck,
    Html.tabindex, Html.dir, Html.lang, Html.title_attr,
    Html.document_with, Html.document_utf8
}

pub use lib::html_t {
    Page, Page.empty, Page.append_head, Page.append_heads, Page.append_body,
    Page.append_bodies, Emitted, HtmlT, Open, PageM, PageM.pure, PageM.run,
    Render, Render.io, Render.lift_page, Render.write, Sealed,
    HtmlT.run, HtmlT.pure, HtmlT.bind, HtmlT.map, HtmlT.and_then, HtmlT.lift,
    HtmlT.head_node, HtmlT.head_nodes, HtmlT.body_node, HtmlT.body_nodes,
    HtmlT.seal, HtmlT.emit
}

pub use lib::app {
    Program, Program.app, Program.with_subs, Program.subscriptions,
    Program.init, Program.run_batch, Program.step, Program.view,
    Command, Host, Host.run_effect
}

pub use lib::ssr {
    Ssr.render_page, Ssr.render_body, Ssr.to_response, Ssr.to_response_node,
    Ssr.fragment_response, Ssr.render_io
}
