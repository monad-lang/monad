// Oak's typed view layer.
//
// `Oak.Node Msg` / `Oak.Attr Msg` are a thin wrapper over `xml_html`: an
// attribute is either a real `Html.Attr` or an event binding, and nodes are
// typed containers around real `Html.Node` values. Everything that is not a
// container (text, comments, doctypes, raw subtrees) is reached through
// `Oak.Node.raw`, so there is one markup ADT, not two.
//
// Lowering is the boundary:
//   * `Oak.lower` writes `on` as `data-oak-on-<event>="<id>:<flags>"` and
//     returns the id -> handler table. The browser runtime calls the handler
//     with a `web_event::WebEvent` snapshot.
//   * `Oak.to_html` drops `on` (SSR has no client handler ids) and keeps the
//     declarative `data-oak-*` effect attributes.
//
// Handler ids are derived from the node's patch path and the event name, so
// they are stable across renders and already correct when `Patch` mounts a
// lowered subtree at an arbitrary path.

use web_event::event {WebEvent, HandlerResult, ListenerFlags, ListenerFlags.encode}
use xml_html::html {Html.Attr, Html.Node}

pub type Oak.Attr (Msg : Type) {
    html (attr : Html.Attr),
    on (event : String) (flags : ListenerFlags) (handler : WebEvent -> HandlerResult Msg)
}

pub type Oak.Node (Msg : Type) {
    raw (node : Html.Node),
    element (tag : String) (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)),
    void (tag : String) (attrs : List (Oak.Attr Msg)),
    raw_text (tag : String) (attrs : List (Oak.Attr Msg)) (content : String),
    fragment (children : List (Oak.Node Msg))
}

pub type Oak.Lowered (Msg : Type) {
    lowered (node : Html.Node) (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
}

// ═══ Escape hatches ═══
//
// A raw value is a first-class part of a typed view: wrap it and it lowers
// through untouched (and contributes no handlers, so write
// `data-oak-on-*` by hand only if you mean it).

pub def Oak.of_html {Msg : Type} (node : Html.Node) : Oak.Node Msg :=
    Oak.Node.raw node

pub def Oak.of_attr {Msg : Type} (attr : Html.Attr) : Oak.Attr Msg :=
    Oak.Attr.html attr

pub def Oak.text {Msg : Type} (content : String) : Oak.Node Msg :=
    Oak.Node.raw (Html.Node.node_text content)

// ═══ Handler ids ═══
//
// FNV-1a over "<path>:<event>", masked to a positive 31-bit id. The wire
// value is `0x` plus eight hex digits; the JS host parses it with `BigInt`.

def fnv_init : U32 := 2166136261u32

def fnv_prime : U32 := 16777619u32

def fnv_byte (h : U32) (b : U8) : U32 :=
    U32.mul (U32.xor h (U8.to_u32 b)) fnv_prime

#[terminating]
def fnv_string (s : String) (i : I64) (h : U32) : U32 :=
    if I64.gt i (String.length s)
    then h
    else
        match String.get s i {
            Option.some b => fnv_string s (i + 1i64) (fnv_byte h b),
            Option.none => h,
        }

/// A stable textual key for a patch path (`"0.1.2."`).
#[terminating]
def path_key (path : List I64) (acc : String) : String :=
    match path {
        List.empty => acc,
        List.cons i rest => path_key rest (String.concat acc (String.concat (I64.to_string i) ".")),
    }

/// The handler id for one event binding at `path`.
pub def Handler.id (path : List I64) (event : String) : U32 :=
    let key : String := String.concat (path_key path "") event in
    U32.and (fnv_string key 0i64 fnv_init) 0x7FFFFFFFu32

/// One hex digit. U32 has no `to_string` native wired in the compiled
/// backends, so ids are rendered from the wired shift/and ops instead.
def hex_digit (n : U32) : String :=
    if U32.beq n 0u32 then "0"
    else if U32.beq n 1u32 then "1"
    else if U32.beq n 2u32 then "2"
    else if U32.beq n 3u32 then "3"
    else if U32.beq n 4u32 then "4"
    else if U32.beq n 5u32 then "5"
    else if U32.beq n 6u32 then "6"
    else if U32.beq n 7u32 then "7"
    else if U32.beq n 8u32 then "8"
    else if U32.beq n 9u32 then "9"
    else if U32.beq n 10u32 then "a"
    else if U32.beq n 11u32 then "b"
    else if U32.beq n 12u32 then "c"
    else if U32.beq n 13u32 then "d"
    else if U32.beq n 14u32 then "e"
    else "f"

def hex_nibble (v : U32) (shift : U32) : String :=
    hex_digit (U32.and (U32.shr v shift) 15u32)

/// `0x` + eight hex digits (BigInt parses this on the JS side).
pub def Handler.hex (v : U32) : String :=
    String.concat "0x" (String.concat_list
        [ hex_nibble v 28u32, hex_nibble v 24u32, hex_nibble v 20u32, hex_nibble v 16u32,
          hex_nibble v 12u32, hex_nibble v 8u32, hex_nibble v 4u32, hex_nibble v 0u32 ])

/// The attribute value the JS host parses: `"<id><:flags>"`.
pub def Handler.spec_of (id : U32) (flags : ListenerFlags) : String :=
    String.concat (Handler.hex id) (ListenerFlags.encode flags)

pub def Handler.spec (path : List I64) (event : String) (flags : ListenerFlags) : String :=
    Handler.spec_of (Handler.id path event) flags

/// The prefix every event attribute carries. Shared with
/// `wasm/web/web_runtime.js`; a drift test pins the literal.
pub def Handler.prefix : String := "data-oak-on-"

// ═══ Lowering for the browser ═══

pub def Oak.lower (n : Oak.Node Msg) : Oak.Lowered Msg :=
    lower_at (List.cons 0i64 List.empty) n

#[partial]
def lower_at (path : List I64) (n : Oak.Node Msg) : Oak.Lowered Msg :=
    match n {
        Oak.Node.raw node => Oak.Lowered.lowered node List.empty,
        Oak.Node.element tag attrs children =>
            match lower_attrs path attrs List.empty List.empty {
                Pair.pair nodes_attrs handlers =>
                    match lower_children path children 0i64 List.empty List.empty {
                        Pair.pair nodes child_handlers =>
                            Oak.Lowered.lowered
                                (Html.Node.node_element tag nodes_attrs nodes)
                                (List.append handlers child_handlers)
                    }
            },
        Oak.Node.void tag attrs =>
            match lower_attrs path attrs List.empty List.empty {
                Pair.pair nodes_attrs handlers =>
                    Oak.Lowered.lowered (Html.Node.node_void tag nodes_attrs) handlers
            },
        Oak.Node.raw_text tag attrs content =>
            match lower_attrs path attrs List.empty List.empty {
                Pair.pair nodes_attrs handlers =>
                    Oak.Lowered.lowered (Html.Node.node_raw_text tag nodes_attrs content) handlers
            },
        Oak.Node.fragment children =>
            match lower_children path children 0i64 List.empty List.empty {
                Pair.pair nodes handlers =>
                    Oak.Lowered.lowered (Html.Node.node_fragment nodes) handlers
            },
    }

def lower_attr (path : List I64) (a : Oak.Attr Msg)
    : Pair (List Html.Attr) (List (Pair U32 (WebEvent -> HandlerResult Msg))) :=
    match a {
        Oak.Attr.html attr =>
            Pair.pair (List.cons attr List.empty) List.empty,
        Oak.Attr.on event flags handler =>
            let id : U32 := Handler.id path event in
            let name : String := String.concat Handler.prefix event in
            let attr : Html.Attr := Html.Attr.attr name (Handler.spec_of id flags) in
            Pair.pair (List.cons attr List.empty)
                (List.cons (Pair.pair id handler) List.empty),
    }

/// Prepend every element of `xs` to `acc` (reversing `xs` onto it); the
/// caller reverses once at the end. Linear, unlike `List.append` per step.
#[terminating]
def prepend_all {A : Type} (xs : List A) (acc : List A) : List A :=
    match xs {
        List.empty => acc,
        List.cons x rest => prepend_all rest (List.cons x acc),
    }

#[terminating]
def lower_attrs (path : List I64) (attrs : List (Oak.Attr Msg))
    (acc_attrs : List Html.Attr)
    (acc_handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
    : Pair (List Html.Attr) (List (Pair U32 (WebEvent -> HandlerResult Msg))) :=
    match attrs {
        List.empty => Pair.pair (List.reverse acc_attrs) (List.reverse acc_handlers),
        List.cons a rest =>
            match lower_attr path a {
                Pair.pair new_attrs new_handlers =>
                    lower_attrs path rest
                        (prepend_all new_attrs acc_attrs)
                        (prepend_all new_handlers acc_handlers)
            },
    }

#[terminating]
def lower_children (path : List I64) (children : List (Oak.Node Msg)) (index : I64)
    (acc_nodes : List Html.Node)
    (acc_handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
    : Pair (List Html.Node) (List (Pair U32 (WebEvent -> HandlerResult Msg))) :=
    match children {
        List.empty => Pair.pair (List.reverse acc_nodes) (List.reverse acc_handlers),
        List.cons child rest =>
            match lower_at (List.append path (List.cons index List.empty)) child {
                Oak.Lowered.lowered node handlers =>
                    lower_children path rest
                        (index + 1i64)
                        (List.cons node acc_nodes)
                        (prepend_all handlers acc_handlers)
            },
    }

// ═══ Lowering for the server ═══
//
// SSR markup carries no handler ids: the client re-applies the view's
// attributes during hydration and registers the listeners then.

pub def Oak.to_html (n : Oak.Node Msg) : Html.Node :=
    to_html_node n

def to_html_node (n : Oak.Node Msg) : Html.Node :=
    match n {
        Oak.Node.raw node => node,
        Oak.Node.element tag attrs children =>
            Html.Node.node_element tag (to_html_attrs attrs) (to_html_children children),
        Oak.Node.void tag attrs => Html.Node.node_void tag (to_html_attrs attrs),
        Oak.Node.raw_text tag attrs content =>
            Html.Node.node_raw_text tag (to_html_attrs attrs) content,
        Oak.Node.fragment children => Html.Node.node_fragment (to_html_children children),
    }

#[terminating]
def to_html_children (children : List (Oak.Node Msg)) : List Html.Node :=
    match children {
        List.empty => List.empty,
        List.cons child rest => List.cons (to_html_node child) (to_html_children rest),
    }

#[terminating]
def to_html_attrs (attrs : List (Oak.Attr Msg)) : List Html.Attr :=
    match attrs {
        List.empty => List.empty,
        List.cons a rest =>
            match a {
                Oak.Attr.html attr => List.cons attr (to_html_attrs rest),
                Oak.Attr.on _event _flags _handler => to_html_attrs rest,
            },
    }
