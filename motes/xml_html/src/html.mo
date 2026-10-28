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
    node_raw_html (literal : String),
    node_comment (content : String),
    node_doctype (declaration : String),
    node_fragment (children : List Html.Node)
}

with Html {
    pub def to_string (n : Html.Node) : String :=
        let opts : Html.RenderOpts := { charset := false, annotate := false, xhtml_void := false } in
        html_node_to_string opts "0" n

    /// Serialize with render options. `annotate` writes `data-oak="<path>"`
    /// on every element (a stable tree path for client hydration);
    /// `xhtml_void` spells void elements `<br />` instead of `<br>`;
    /// `charset` is consulted by `oak`'s document builder, not here.
    pub def to_string_with (opts : Html.RenderOpts) (n : Html.Node) : String :=
        html_node_to_string opts "0" n

    pub def beq (a b : Html.Node) : Bool := html_node_beq a b
}

/// Every field is named at every literal: an omitted field is filled
/// positionally, which shifts the fields that follow it (measured on the
/// Rust host, 2026-10-19), and a constructor-valued default cannot be
/// lowered by the Rust host at all.
pub struct Html.RenderOpts {
    charset : Bool := false,
    annotate : Bool := false,
    xhtml_void : Bool := false
}

pub def Html.default_opts : Html.RenderOpts :=
    { charset := false, annotate := false, xhtml_void := false }

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
//
// Pieces, not concatenation. The output is a reversed `List String` joined
// once by `String.concat_list`: the old shape, `concat child (rest)`,
// re-copied every remaining sibling per child, which is quadratic on the
// flat hundred-thousand-node lists the oak hydration path builds.

def html_attr_to_string (a : Html.Attr) : String :=
    match a {
        attr name value =>
            String.concat " " (String.concat name (String.concat "=\"" (String.concat (html_escape_attr value) "\""))),
        bool_attr name => String.concat " " name
    }

#[terminating]
def html_attr_pieces (attrs : List Html.Attr) (acc : List String) : List String :=
    match attrs {
        empty => acc,
        cons a rest => html_attr_pieces rest (List.cons (html_attr_to_string a) acc)
    }

def html_attrs_to_string (attrs : List Html.Attr) : String :=
    String.concat_list (List.reverse (html_attr_pieces attrs List.empty))

def html_open_tag (tag : String) (attrs : List Html.Attr) : String :=
    String.concat "<" (String.concat tag (String.concat (html_attrs_to_string attrs) ">"))

/// `xhtml_void` is for CommonMark conformance, where cmark spells void
/// elements `<br />`; the default keeps the HTML5 spelling.
def html_void_tag (opts : Html.RenderOpts) (tag : String) (attrs : List Html.Attr) : String :=
    if opts.xhtml_void
    then String.concat "<" (String.concat tag (String.concat (html_attrs_to_string attrs) " />"))
    else html_open_tag tag attrs

def html_close_tag (tag : String) : String :=
    String.concat "</" (String.concat tag ">")

// ─── Hydration paths and annotation ───

def html_child_path (opts : Html.RenderOpts) (path : String) (idx : I64) : String :=
    if opts.annotate
    then String.concat path (String.concat "." (I64.to_string idx))
    else path

def html_annotated_attrs (opts : Html.RenderOpts) (path : String) (attrs : List Html.Attr) : List Html.Attr :=
    if opts.annotate
    then List.append attrs (List.cons (Html.Attr.attr "data-oak" path) List.empty)
    else attrs

/// `n`'s pieces, reversed, prepended to `acc`; the caller reverses once.
/// `path` is the hydration path of `n` (unused unless `opts.annotate`).
#[partial]
def html_node_pieces (opts : Html.RenderOpts) (path : String) (n : Html.Node) (acc : List String) : List String :=
    match n {
        node_element tag attrs children =>
            List.cons (html_close_tag tag)
                (html_children_pieces opts path 0 children
                    (List.cons (html_open_tag tag (html_annotated_attrs opts path attrs)) acc)),
        node_void tag attrs =>
            List.cons (html_void_tag opts tag (html_annotated_attrs opts path attrs)) acc,
        node_text content => List.cons (html_escape_text content) acc,
        node_raw_text tag attrs content =>
            List.cons (html_close_tag tag)
                (List.cons content (List.cons (html_open_tag tag attrs) acc)),
        node_raw_html literal => List.cons literal acc,
        node_comment content =>
            List.cons (String.concat "<!--" (String.concat content "-->")) acc,
        node_doctype declaration =>
            List.cons (String.concat "<!DOCTYPE " (String.concat declaration ">")) acc,
        node_fragment children => html_children_pieces opts path 0 children acc
    }

#[partial]
def html_children_pieces (opts : Html.RenderOpts) (path : String) (idx : I64) (children : List Html.Node) (acc : List String) : List String :=
    match children {
        empty => acc,
        cons child rest =>
            html_children_pieces opts path (I64.add idx 1) rest
                (html_node_pieces opts (html_child_path opts path idx) child acc)
    }

def html_node_to_string (opts : Html.RenderOpts) (path : String) (n : Html.Node) : String :=
    String.concat_list (List.reverse (html_node_pieces opts path n List.empty))

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
        node_raw_html l1 => match b {
            node_raw_html l2 => String.beq l1 l2,
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
