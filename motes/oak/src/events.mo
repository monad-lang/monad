// The pure event API: typed listener attributes and subscriptions.
//
// A listener is an ordinary function `WebEvent -> HandlerResult Msg`; there is
// no numeric handler id in the surface and no decoder to write. The lowering
// in `lib::typed` turns each binding into the `data-oak-on-*` attribute and
// collects the handler table.
//
// Outgoing effects are declarative attributes (`drag_payload`, `drop_effect`,
// `copy_text`). The JS host performs them during the event, so an oak view
// and update stay pure. Incoming payloads (text, types, files, value) arrive
// in the `WebEvent` snapshot.

use web_event::event {WebEvent, HandlerResult, ListenerFlags}
use xml_html::html {Html.Attr}
use lib::typed {Oak.Attr}

// ═══ Subscriptions ═══
//
// Elm's `Sub msg` — named `Subscription` here because a bare imported `Sub`
// collides with the prelude's subtraction class on the Rust host (the same
// reason `Doc`/`Cmd` became `Page`/`Command`). It is a pure declarative
// request for an event source outside the view tree; the runtime diffs the
// list by (target, event) each render.

pub type Subscription (Msg : Type) {
    none,
    window (event : String) (handler : WebEvent -> Msg),
    document (event : String) (handler : WebEvent -> Msg),
    animation_frame (handler : WebEvent -> Msg)
}

pub def Subscription.window_msg {Msg : Type} (event : String) (m : Msg) : Subscription Msg :=
    Subscription.window event (fn (_e : WebEvent) => m)

pub def Subscription.document_msg {Msg : Type} (event : String) (m : Msg) : Subscription Msg :=
    Subscription.document event (fn (_e : WebEvent) => m)

pub def Subscription.animation_frame_msg {Msg : Type} (m : Msg) : Subscription Msg :=
    Subscription.animation_frame (fn (_e : WebEvent) => m)

// ═══ Handler helpers ═══

def always {Msg : Type} (m : Msg) : WebEvent -> HandlerResult Msg :=
    fn (_e : WebEvent) => HandlerResult.msg m

def from_event {Msg : Type} (f : WebEvent -> Msg) : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) => HandlerResult.msg (f e)

def from_value {Msg : Type} (f : String -> Msg) : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) => HandlerResult.msg (f e.value)

def prevent_always {Msg : Type} (m : Msg) : WebEvent -> HandlerResult Msg :=
    fn (_e : WebEvent) => HandlerResult.prevent m

def prevent_from_event {Msg : Type} (f : WebEvent -> Msg) : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) => HandlerResult.prevent (f e)

def prevent_flags : ListenerFlags := { prevent_default := true }

with Html {
    // ─── Generic ───────────────────────────────────────────────────────

    pub def on {Msg : Type} (event : String) (flags : ListenerFlags)
        (handler : WebEvent -> HandlerResult Msg) : Oak.Attr Msg :=
        Oak.Attr.on event flags handler

    /// Bind an event to a constant message.
    pub def msg {Msg : Type} (event : String) (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on event ListenerFlags.none (always m)

    pub def msg_with {Msg : Type} (event : String) (flags : ListenerFlags) (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on event flags (always m)

    // ─── Mouse and pointer ─────────────────────────────────────────────

    pub def on_click {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "click" ListenerFlags.none (always m)

    pub def on_click_with {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "click" ListenerFlags.none (from_event f)

    pub def on_dblclick {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dblclick" ListenerFlags.none (always m)

    pub def on_contextmenu {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "contextmenu" ListenerFlags.none (always m)

    pub def on_auxclick {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "auxclick" ListenerFlags.none (always m)

    pub def on_mousedown {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mousedown" ListenerFlags.none (from_event f)

    pub def on_mouseup {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mouseup" ListenerFlags.none (from_event f)

    pub def on_mousemove {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mousemove" ListenerFlags.none (from_event f)

    pub def on_mouseenter {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mouseenter" ListenerFlags.none (always m)

    pub def on_mouseleave {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mouseleave" ListenerFlags.none (always m)

    pub def on_mouseover {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mouseover" ListenerFlags.none (from_event f)

    pub def on_mouseout {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "mouseout" ListenerFlags.none (from_event f)

    pub def on_pointerdown {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerdown" ListenerFlags.none (from_event f)

    pub def on_pointerup {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerup" ListenerFlags.none (from_event f)

    pub def on_pointermove {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointermove" ListenerFlags.none (from_event f)

    pub def on_pointerover {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerover" ListenerFlags.none (from_event f)

    pub def on_pointerout {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerout" ListenerFlags.none (from_event f)

    pub def on_pointerenter {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerenter" ListenerFlags.none (always m)

    pub def on_pointerleave {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointerleave" ListenerFlags.none (always m)

    pub def on_pointercancel {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pointercancel" ListenerFlags.none (always m)

    pub def on_wheel {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "wheel" ListenerFlags.none (from_event f)

    // ─── Keyboard and focus ────────────────────────────────────────────

    pub def on_keydown {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "keydown" ListenerFlags.none (from_event f)

    pub def on_keyup {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "keyup" ListenerFlags.none (from_event f)

    pub def on_focus {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "focus" ListenerFlags.none (always m)

    pub def on_blur {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "blur" ListenerFlags.none (always m)

    pub def on_focusin {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "focusin" ListenerFlags.none (always m)

    pub def on_focusout {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "focusout" ListenerFlags.none (always m)

    // ─── Form ──────────────────────────────────────────────────────────

    /// The live value at event time (`e.value`).
    pub def on_input {Msg : Type} (f : String -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "input" ListenerFlags.none (from_value f)

    pub def on_change {Msg : Type} (f : String -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "change" ListenerFlags.none (from_value f)

    pub def on_submit {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "submit" ListenerFlags.none (always m)

    pub def on_submit_prevent {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "submit" prevent_flags (prevent_always m)

    pub def on_reset {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "reset" ListenerFlags.none (always m)

    // ─── Scroll, touch, animation ──────────────────────────────────────

    pub def on_scroll {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "scroll" ListenerFlags.none (from_event f)

    pub def on_touchstart {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "touchstart" ListenerFlags.none (from_event f)

    pub def on_touchmove {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "touchmove" ListenerFlags.none (from_event f)

    pub def on_touchend {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "touchend" ListenerFlags.none (from_event f)

    pub def on_touchcancel {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "touchcancel" ListenerFlags.none (always m)

    pub def on_animationstart {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "animationstart" ListenerFlags.none (always m)

    pub def on_animationend {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "animationend" ListenerFlags.none (always m)

    pub def on_animationiteration {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "animationiteration" ListenerFlags.none (always m)

    pub def on_transitionend {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "transitionend" ListenerFlags.none (always m)

    pub def on_load {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "load" ListenerFlags.none (always m)

    pub def on_error {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "error" ListenerFlags.none (from_event f)

    // ─── Drag and drop ─────────────────────────────────────────────────
    //
    // `dragover` and `drop` carry the preventDefault flag: the browser
    // decides whether a drop is allowed when the handler returns, so it
    // cannot come from a later update.

    pub def on_dragstart {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragstart" ListenerFlags.none (from_event f)

    pub def on_dragstart_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragstart" ListenerFlags.none (always m)

    pub def on_drag {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "drag" ListenerFlags.none (from_event f)

    pub def on_dragenter {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragenter" prevent_flags (prevent_always m)

    pub def on_dragleave {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragleave" ListenerFlags.none (always m)

    pub def on_dragend {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragend" ListenerFlags.none (from_event f)

    pub def on_dragend_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragend" ListenerFlags.none (always m)

    pub def on_dragover {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "dragover" prevent_flags (prevent_always m)

    pub def on_drop {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "drop" prevent_flags (prevent_from_event f)

    pub def on_drop_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "drop" prevent_flags (prevent_always m)

    // ─── Clipboard ─────────────────────────────────────────────────────

    pub def on_copy {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "copy" ListenerFlags.none (from_event f)

    pub def on_copy_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "copy" ListenerFlags.none (always m)

    pub def on_cut {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "cut" ListenerFlags.none (from_event f)

    pub def on_cut_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "cut" ListenerFlags.none (always m)

    pub def on_paste {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "paste" ListenerFlags.none (from_event f)

    pub def on_paste_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "paste" ListenerFlags.none (always m)

    // ─── Media elements ────────────────────────────────────────────────

    pub def on_play {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "play" ListenerFlags.none (always m)

    pub def on_pause {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "pause" ListenerFlags.none (always m)

    pub def on_ended {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "ended" ListenerFlags.none (always m)

    pub def on_timeupdate {Msg : Type} (f : WebEvent -> Msg) : Oak.Attr Msg :=
        Oak.Attr.on "timeupdate" ListenerFlags.none (from_event f)

    pub def on_timeupdate_msg {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "timeupdate" ListenerFlags.none (always m)

    pub def on_loadedmetadata {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "loadedmetadata" ListenerFlags.none (always m)

    pub def on_canplay {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "canplay" ListenerFlags.none (always m)

    pub def on_volumechange {Msg : Type} (m : Msg) : Oak.Attr Msg :=
        Oak.Attr.on "volumechange" ListenerFlags.none (always m)

    // ─── Declarative outgoing effects ─────────────────────────────────
    //
    // The JS host reads these from the listening element while the event is
    // dispatching. `drag_payload` encodes `<mime-byte-length>:<mime><text>`
    // in one attribute so the text needs no escaping.

    pub def drag_payload {Msg : Type} (mime : String) (text : String) : Oak.Attr Msg :=
        let value : String :=
            String.concat (I64.to_string (String.length mime))
                (String.concat ":" (String.concat mime text)) in
        Oak.Attr.html (Html.Attr.attr "data-oak-drag" value)

    pub def drag_effect {Msg : Type} (effect : String) : Oak.Attr Msg :=
        Oak.Attr.html (Html.Attr.attr "data-oak-drag-effect" effect)

    pub def drop_effect {Msg : Type} (effect : String) : Oak.Attr Msg :=
        Oak.Attr.html (Html.Attr.attr "data-oak-drop-effect" effect)

    pub def copy_text {Msg : Type} (text : String) : Oak.Attr Msg :=
        Oak.Attr.html (Html.Attr.attr "data-oak-copy-text" text)
}
