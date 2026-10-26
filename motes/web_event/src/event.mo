/// A snapshot of one browser event.
///
/// The snapshot is deliberately **pure data**: no DOM handle, no effect
/// capability. A handler is an ordinary function `WebEvent -> HandlerResult Msg`,
/// so views and updates stay pure; the runtime builds the snapshot before
/// dispatch and applies any `preventDefault`/`stopPropagation` the handler
/// asks for. Outgoing effects (drag payloads, clipboard writes) are
/// declarative attributes on the view, not calls from a handler.
///
/// `valid` is false outside a dispatch: the JavaScript host keeps the live
/// event in a slot only for the duration of the synchronous export call, and
/// every field then reads as its zero value.

pub struct FileInfo {
    name : String := "",
    size : I64 := 0,
    mime_type : String := "",
    last_modified : I64 := 0
}

/// Listener options, encoded into the handler attribute as the flag letters
/// `cdsop` (`c` capture, `d` preventDefault before dispatch, `s`
/// stopPropagation before dispatch, `o` once, `p` passive). The encoding is
/// shared with `wasm/web/web_runtime.js`; keep `letters` and `encode` in step
/// with `parseListenerSpec` there.
pub struct ListenerFlags {
    capture : Bool := false,
    prevent_default : Bool := false,
    stop_propagation : Bool := false,
    once : Bool := false,
    passive : Bool := false
}

/// What a handler decided. `prevent_default`/`stop_propagation` are applied
/// by the runtime while the browser is still dispatching, so they cannot be
/// expressed from a later update.
pub type HandlerResult (Msg : Type) {
    handler_result (msg : Option Msg) (prevent_default : Bool) (stop_propagation : Bool)
}

pub struct WebEvent {
    kind : String := "",
    valid : Bool := false,
    time_stamp : F64 := 0.0,
    /// Bitmask: shift = 1, ctrl = 2, alt = 4, meta = 8.
    modifiers : I64 := 0,
    client_x : F64 := 0.0,
    client_y : F64 := 0.0,
    page_x : F64 := 0.0,
    page_y : F64 := 0.0,
    screen_x : F64 := 0.0,
    screen_y : F64 := 0.0,
    offset_x : F64 := 0.0,
    offset_y : F64 := 0.0,
    button : I64 := 0,
    buttons : I64 := 0,
    detail : I64 := 0,
    pointer_id : I64 := 0,
    pointer_type : String := "",
    pressure : F64 := 0.0,
    is_primary : Bool := false,
    width : F64 := 0.0,
    height : F64 := 0.0,
    key : String := "",
    code : String := "",
    repeat : Bool := false,
    location : I64 := 0,
    delta_x : F64 := 0.0,
    delta_y : F64 := 0.0,
    delta_z : F64 := 0.0,
    delta_mode : I64 := 0,
    /// The live form value (`input`, `textarea`, `select`) at event time.
    value : String := "",
    checked : Bool := false,
    /// Drag/clipboard payload text (`text/plain`), empty when absent.
    data : String := "",
    /// `DataTransfer.types`, in source order.
    data_types : List String := List.empty,
    files : List FileInfo := List.empty,
    effect_allowed : String := "",
    drop_effect : String := "",
    default_prevented : Bool := false
}

with ListenerFlags {
    /// No options: bubbling, non-passive, repeated.
    pub def none : ListenerFlags :=
        { capture := false, prevent_default := false, stop_propagation := false,
          once := false, passive := false }

    /// The canonical letters, in encoding order.
    pub def letters : String := "cdsop"

    /// The `:<flags>` suffix (empty when no flag is set).
    pub def encode (f : ListenerFlags) : String :=
        match f {
            { capture, prevent_default, stop_propagation, once, passive } =>
                let body : String :=
                    String.concat (if capture then "c" else "")
                        (String.concat (if prevent_default then "d" else "")
                            (String.concat (if stop_propagation then "s" else "")
                                (String.concat (if once then "o" else "")
                                    (if passive then "p" else "")))) in
                if String.is_empty body then "" else String.concat ":" body
        }
}

with WebEvent {
    pub def mod_shift (e : WebEvent) : Bool :=
        U32.beq (U32.and (I64.to_u32 e.modifiers) 1u32) 1u32

    pub def mod_ctrl (e : WebEvent) : Bool :=
        U32.beq (U32.and (I64.to_u32 e.modifiers) 2u32) 2u32

    pub def mod_alt (e : WebEvent) : Bool :=
        U32.beq (U32.and (I64.to_u32 e.modifiers) 4u32) 4u32

    pub def mod_meta (e : WebEvent) : Bool :=
        U32.beq (U32.and (I64.to_u32 e.modifiers) 8u32) 8u32
}

with HandlerResult {
    /// Handle the event and produce one message.
    pub def msg {Msg : Type} (m : Msg) : HandlerResult Msg :=
        HandlerResult.handler_result (Option.some m) false false

    /// Handle nothing.
    pub def ignore {Msg : Type} : HandlerResult Msg :=
        HandlerResult.handler_result Option.none false false

    /// Handle the event and stop its default action.
    pub def prevent {Msg : Type} (m : Msg) : HandlerResult Msg :=
        HandlerResult.handler_result (Option.some m) true false
}
