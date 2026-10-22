/// HTML markup nodes and their serializer.
///
/// The type is shared with the HTML parser (a later phase) and with the
/// `oak` builder library: one tree, two producers, one serializer.
///
/// Attributes are a `List`, not a map: source order, duplicate spelling
/// and the boolean-attribute distinction all survive. The `node_`
/// constructor prefixes leave `Html.text`/`Html.div`/`Html.node` free for
/// builder defs in `oak` -- a builder in another module can then use the
/// Elm-shaped short names without colliding with a constructor.
///
/// Escaping walks UTF-8 characters via `utf8_char_width`. `String.slice`
/// returns `""` for a cut that is not on a character boundary, so a
/// byte-at-a-time walk silently truncates at the first non-ASCII
/// character (the bug `Json.escape_string` records).

use init::string {}
use parsec::core {is_empty}
use parsec::combinators {utf8_char_width}

// The types are declared with their dotted names directly, not inside a
// `with Html` block: a constructor declared through `with` is not visible
// across modules (the Rust host reports it unbound), while a `Type.ctor`
// path on a dotted declaration is (`Html.Node.node_text`, the
// `Toml.Value.string` pattern). `with Html` is still used for the defs,
// which do resolve cross-module.
pub type Html.Attr {
    attr (name : String) (value : String),
    bool_attr (name : String)
}

pub type Html.Node {
    node_element (tag : String) (attrs : List Html.Attr) (children : List Html.Node),
    node_void (tag : String) (attrs : List Html.Attr),
    node_text (content : String),
    node_raw_text (tag : String) (attrs : List Html.Attr) (content : String),
    node_comment (content : String),
    node_doctype (declaration : String),
    node_fragment (children : List Html.Node)
}

with Html {
    pub def to_string (n : Html.Node) : String := html_node_to_string n

    /// Serialize with render options. `annotate` writes `data-oak="<path>"`
    /// on every element (a stable tree path for client hydration); `charset`
    /// is consulted by `oak`'s document builder, not here.
    pub def to_string_with (opts : Html.RenderOpts) (n : Html.Node) : String :=
        if opts.annotate then html_node_to_string_at opts "0" n else html_node_to_string n

    pub def beq (a b : Html.Node) : Bool := html_node_beq a b
}

pub struct Html.RenderOpts {
    charset : Bool,
    annotate : Bool
}

pub def Html.default_opts : Html.RenderOpts :=
    { charset := false, annotate := false }

// ─── Escaping ───

def html_escape_text_char (c : String) : String :=
    if String.beq "&" c then "&amp;"
    else if String.beq "<" c then "&lt;"
    else if String.beq ">" c then "&gt;"
    else c

def html_escape_attr_char (c : String) : String :=
    if String.beq "&" c then "&amp;"
    else if String.beq "<" c then "&lt;"
    else if String.beq ">" c then "&gt;"
    else if String.beq "\"" c then "&quot;"
    else c

/// Accumulate escaped pieces, then join once. Stepping by `utf8_char_width`
/// keeps multi-byte characters whole; `is_empty` is the terminator.
#[terminating]
def html_escape_pieces (escape_one : String -> String) (input : String) (acc : List String) : List String :=
    if is_empty input
    then List.reverse acc
    else
        let width : I64 := utf8_char_width input in
        let step : I64 := if width < 1 then 1 else width in
        let ch : String := String.slice input 0 step in
        html_escape_pieces escape_one (String.drop step input) (List.cons (escape_one ch) acc)

def html_escape_text (input : String) : String :=
    String.concat_list (html_escape_pieces html_escape_text_char input List.empty)

def html_escape_attr (input : String) : String :=
    String.concat_list (html_escape_pieces html_escape_attr_char input List.empty)

// ─── Serializer ───

def html_attr_to_string (a : Html.Attr) : String :=
    match a {
        attr name value =>
            String.concat " " (String.concat name (String.concat "=\"" (String.concat (html_escape_attr value) "\""))),
        bool_attr name => String.concat " " name
    }

def html_attrs_to_string (attrs : List Html.Attr) : String :=
    match attrs {
        empty => "",
        cons a rest => String.concat (html_attr_to_string a) (html_attrs_to_string rest)
    }

def html_children_to_string (children : List Html.Node) : String :=
    match children {
        empty => "",
        cons child rest => String.concat (html_node_to_string child) (html_children_to_string rest)
    }

def html_open_tag (tag : String) (attrs : List Html.Attr) : String :=
    String.concat "<" (String.concat tag (String.concat (html_attrs_to_string attrs) ">"))

def html_close_tag (tag : String) : String :=
    String.concat "</" (String.concat tag ">")

def html_node_to_string (n : Html.Node) : String :=
    match n {
        node_element tag attrs children =>
            String.concat (html_open_tag tag attrs)
                (String.concat (html_children_to_string children) (html_close_tag tag)),
        node_void tag attrs => html_open_tag tag attrs,
        node_text content => html_escape_text content,
        node_raw_text tag attrs content =>
            String.concat (html_open_tag tag attrs) (String.concat content (html_close_tag tag)),
        node_comment content => String.concat "<!--" (String.concat content "-->"),
        node_doctype declaration => String.concat "<!DOCTYPE " (String.concat declaration ">"),
        node_fragment children => html_children_to_string children
    }

// ─── Annotated serializer (hydration paths) ───

def html_annotated_attrs (opts : Html.RenderOpts) (path : String) (attrs : List Html.Attr) : List Html.Attr :=
    if opts.annotate
    then List.append attrs (List.cons (Html.Attr.attr "data-oak" path) List.empty)
    else attrs

#[terminating]
def html_children_to_string_at (opts : Html.RenderOpts) (path : String) (idx : I64) (children : List Html.Node) : String :=
    match children {
        empty => "",
        cons child rest =>
            String.concat
                (html_node_to_string_at opts (String.concat path (String.concat "." (I64.to_string idx))) child)
                (html_children_to_string_at opts path (I64.add idx 1) rest)
    }

#[terminating]
def html_node_to_string_at (opts : Html.RenderOpts) (path : String) (n : Html.Node) : String :=
    match n {
        node_element tag attrs children =>
            String.concat (html_open_tag tag (html_annotated_attrs opts path attrs))
                (String.concat (html_children_to_string_at opts path 0 children) (html_close_tag tag)),
        node_void tag attrs => html_open_tag tag (html_annotated_attrs opts path attrs),
        node_fragment children => html_children_to_string_at opts path 0 children,
        _ => html_node_to_string n
    }

// ─── Equality ───
//
// Element-wise throughout: generic `BEq (List A)` dispatch is unreliable
// at run time (`motes/tui/src/core.mo`'s hand-rolled `Screen` instance is
// the standing precedent), so the list walks are local.

def html_attr_beq (a b : Html.Attr) : Bool :=
    match a {
        attr n1 v1 => match b {
            attr n2 v2 => String.beq n1 n2 && String.beq v1 v2,
            bool_attr _ => false
        },
        bool_attr n1 => match b {
            bool_attr n2 => String.beq n1 n2,
            attr _ _ => false
        }
    }

def html_attrs_beq (a b : List Html.Attr) : Bool :=
    match a {
        empty => match b { empty => true, cons _ _ => false },
        cons x xs => match b {
            empty => false,
            cons y ys => html_attr_beq x y && html_attrs_beq xs ys
        }
    }

def html_children_beq (a b : List Html.Node) : Bool :=
    match a {
        empty => match b { empty => true, cons _ _ => false },
        cons x xs => match b {
            empty => false,
            cons y ys => html_node_beq x y && html_children_beq xs ys
        }
    }

def html_node_beq (a b : Html.Node) : Bool :=
    match a {
        node_element t1 a1 c1 => match b {
            node_element t2 a2 c2 =>
                String.beq t1 t2 && html_attrs_beq a1 a2 && html_children_beq c1 c2,
            _ => false
        },
        node_void t1 a1 => match b {
            node_void t2 a2 => String.beq t1 t2 && html_attrs_beq a1 a2,
            _ => false
        },
        node_text c1 => match b {
            node_text c2 => String.beq c1 c2,
            _ => false
        },
        node_raw_text t1 a1 c1 => match b {
            node_raw_text t2 a2 c2 => String.beq t1 t2 && html_attrs_beq a1 a2 && String.beq c1 c2,
            _ => false
        },
        node_comment c1 => match b {
            node_comment c2 => String.beq c1 c2,
            _ => false
        },
        node_doctype d1 => match b {
            node_doctype d2 => String.beq d1 d2,
            _ => false
        },
        node_fragment c1 => match b {
            node_fragment c2 => html_children_beq c1 c2,
            _ => false
        }
    }

pub instance BEq Html.Attr {
    def beq (a b : Html.Attr) : Bool := html_attr_beq a b
}

pub instance BEq Html.Node {
    def beq (a b : Html.Node) : Bool := html_node_beq a b
}
