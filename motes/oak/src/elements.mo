// The pure builder surface: attributes and elements as plain functions
// returning `Html.Node`, in the Elm-shaped call style
// `Html.div [Html.class_ ["card"]] [Html.text "hi"]`.
//
// The public defs live inside `with Html { … }`, which prefixes each
// declaration name (`Html.div`, `Html.class_`); call sites therefore read
// like an Elm module without every line spelling the prefix. Types are NOT
// declared here: a `with`-declared type's constructors are unbound across
// motes on the Rust host (implementations/with-block-constructors-cross-module).
// Private helpers stay outside the block.

use std::list {List.intercalate}
use xml_html::html {Html.Attr, Html.Node}
use xml_html::html {}

def mk_element (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    Html.Node.node_element tag attrs children

def mk_void (tag : String) (attrs : List Html.Attr) : Html.Node :=
    Html.Node.node_void tag attrs

// `navbar_link` is a named helper, not an inline lambda passed to
// `List.map` (the json/toml precedent), and it sits outside the block so
// only the user-facing component name is prefixed.
def navbar_link (link : Pair String String) : Html.Node :=
    match link {
        Pair.pair href label =>
            Html.li List.empty
                [Html.a [Html.href href] [Html.text label]]
    }

with Html {
    // ═══ Attributes ═══
    //
    // Reserved keywords get the underscore spelling (`class`, `type`, `for`,
    // `open`; see RESERVED_KEYWORDS in core/src/parser.rs). The emitted
    // attribute name never carries the underscore.

    pub def id_ (value : String) : Html.Attr :=
        Html.Attr.attr "id" value

    pub def class_ (names : List String) : Html.Attr :=
        Html.Attr.attr "class" (List.intercalate " " names)

    pub def href (value : String) : Html.Attr :=
        Html.Attr.attr "href" value

    pub def src (value : String) : Html.Attr :=
        Html.Attr.attr "src" value

    pub def alt (value : String) : Html.Attr :=
        Html.Attr.attr "alt" value

    pub def type_ (value : String) : Html.Attr :=
        Html.Attr.attr "type" value

    pub def value_ (value : String) : Html.Attr :=
        Html.Attr.attr "value" value

    pub def placeholder (value : String) : Html.Attr :=
        Html.Attr.attr "placeholder" value

    pub def name_ (value : String) : Html.Attr :=
        Html.Attr.attr "name" value

    pub def for_ (value : String) : Html.Attr :=
        Html.Attr.attr "for" value

    pub def style_attr (value : String) : Html.Attr :=
        Html.Attr.attr "style" value

    pub def data (key : String) (value : String) : Html.Attr :=
        Html.Attr.attr (String.concat "data-" key) value

    /// The attribute a keyed list child carries. One literal, imported by
    /// `oak_wasm`'s diff so the two motes cannot drift.
    pub def key_attr : String := "data-oak-key"

    /// Mark a list child with a stable identity. A list whose children all
    /// carry distinct keys is reconciled by key, so reordering keeps the
    /// DOM nodes (and their focus/scroll/listeners) instead of rewriting
    /// each position.
    pub def key (k : String) : Html.Attr := Html.attr Html.key_attr k

    pub def open_ : Html.Attr := Html.Attr.bool_attr "open"
    pub def disabled : Html.Attr := Html.Attr.bool_attr "disabled"
    pub def checked : Html.Attr := Html.Attr.bool_attr "checked"
    pub def required : Html.Attr := Html.Attr.bool_attr "required"
    pub def readonly : Html.Attr := Html.Attr.bool_attr "readonly"
    pub def selected : Html.Attr := Html.Attr.bool_attr "selected"

    // Generic and form attributes. The curated list above covers the common
    // surface; `attr`/`bool_attr` are the escape hatch for `role`, `aria-*`,
    // `method`, `action`, `enctype`, `target`, `rel`, `charset`, dimensions
    // and validation attributes. Names that are Monad keywords take `_`.

    pub def attr (name : String) (value : String) : Html.Attr :=
        Html.Attr.attr name value

    pub def bool_attr (name : String) : Html.Attr :=
        Html.Attr.bool_attr name

    pub def role (value : String) : Html.Attr := Html.attr "role" value
    pub def aria (name : String) (value : String) : Html.Attr :=
        Html.attr (String.concat "aria-" name) value
    pub def method_ (value : String) : Html.Attr := Html.attr "method" value
    pub def action (value : String) : Html.Attr := Html.attr "action" value
    pub def enctype (value : String) : Html.Attr := Html.attr "enctype" value
    pub def target (value : String) : Html.Attr := Html.attr "target" value
    pub def rel (value : String) : Html.Attr := Html.attr "rel" value
    pub def charset (value : String) : Html.Attr := Html.attr "charset" value
    pub def accept (value : String) : Html.Attr := Html.attr "accept" value
    pub def width (value : I64) : Html.Attr := Html.attr "width" (I64.to_string value)
    pub def height (value : I64) : Html.Attr := Html.attr "height" (I64.to_string value)
    pub def min_ (value : String) : Html.Attr := Html.attr "min" value
    pub def max_ (value : String) : Html.Attr := Html.attr "max" value
    pub def step (value : String) : Html.Attr := Html.attr "step" value
    pub def pattern_ (value : String) : Html.Attr := Html.attr "pattern" value
    pub def autocomplete (value : String) : Html.Attr := Html.attr "autocomplete" value
    pub def minlength (value : I64) : Html.Attr := Html.attr "minlength" (I64.to_string value)
    pub def maxlength (value : I64) : Html.Attr := Html.attr "maxlength" (I64.to_string value)
    pub def multiple : Html.Attr := Html.bool_attr "multiple"
    pub def novalidate : Html.Attr := Html.bool_attr "novalidate"

    /// The conventional `enctype` for a file-upload form.
    pub def enctype_multipart : String := "multipart/form-data"

    // ═══ Structural and text-level elements ═══

    pub def div (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "div" attrs children

    pub def span (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "span" attrs children

    pub def p (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "p" attrs children

    pub def a (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "a" attrs children

    pub def ul (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "ul" attrs children

    pub def ol (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "ol" attrs children

    pub def li (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "li" attrs children

    pub def h1 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h1" attrs children

    pub def h2 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h2" attrs children

    pub def h3 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h3" attrs children

    pub def h4 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h4" attrs children

    pub def h5 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h5" attrs children

    pub def h6 (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "h6" attrs children

    pub def header (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "header" attrs children

    pub def footer (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "footer" attrs children

    pub def nav (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "nav" attrs children

    pub def main_ (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "main" attrs children

    pub def section (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "section" attrs children

    pub def article (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "article" attrs children

    pub def aside (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "aside" attrs children

    // ═══ Table family ═══

    pub def table (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "table" attrs children

    pub def thead (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "thead" attrs children

    pub def tbody (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "tbody" attrs children

    pub def tfoot (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "tfoot" attrs children

    pub def tr (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "tr" attrs children

    pub def th (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "th" attrs children

    pub def td (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "td" attrs children

    pub def caption (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "caption" attrs children

    pub def colgroup (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "colgroup" attrs children

    // ═══ Form family ═══

    pub def form (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "form" attrs children

    pub def label (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "label" attrs children

    pub def fieldset (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "fieldset" attrs children

    pub def legend (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "legend" attrs children

    pub def select (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "select" attrs children

    pub def option (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "option" attrs children

    pub def optgroup (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "optgroup" attrs children

    pub def textarea (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "textarea" attrs children

    pub def button (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "button" attrs children

    pub def datalist (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "datalist" attrs children

    pub def output (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "output" attrs children

    // ═══ Document pieces ═══

    pub def title (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "title" attrs children

    pub def head (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "head" attrs children

    pub def body (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element "body" attrs children

    // ═══ Void elements ═══

    pub def input (attrs : List Html.Attr) : Html.Node := mk_void "input" attrs
    pub def img (attrs : List Html.Attr) : Html.Node := mk_void "img" attrs
    pub def br (attrs : List Html.Attr) : Html.Node := mk_void "br" attrs
    pub def hr (attrs : List Html.Attr) : Html.Node := mk_void "hr" attrs
    pub def meta (attrs : List Html.Attr) : Html.Node := mk_void "meta" attrs
    pub def link (attrs : List Html.Attr) : Html.Node := mk_void "link" attrs
    pub def col (attrs : List Html.Attr) : Html.Node := mk_void "col" attrs
    pub def source (attrs : List Html.Attr) : Html.Node := mk_void "source" attrs
    pub def area (attrs : List Html.Attr) : Html.Node := mk_void "area" attrs
    pub def base (attrs : List Html.Attr) : Html.Node := mk_void "base" attrs
    pub def embed (attrs : List Html.Attr) : Html.Node := mk_void "embed" attrs
    pub def track (attrs : List Html.Attr) : Html.Node := mk_void "track" attrs
    pub def wbr (attrs : List Html.Attr) : Html.Node := mk_void "wbr" attrs

    // ═══ Raw-text elements ═══
    //
    // Raw-text nodes carry attributes too, so `<script type="module" src=…>`
    // is representable.

    pub def script (attrs : List Html.Attr) (content : String) : Html.Node :=
        Html.Node.node_raw_text "script" attrs content

    pub def style (attrs : List Html.Attr) (content : String) : Html.Node :=
        Html.Node.node_raw_text "style" attrs content

    // ═══ Escape hatches and node constructors ═══

    pub def node (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
        mk_element tag attrs children

    pub def void (tag : String) (attrs : List Html.Attr) : Html.Node :=
        mk_void tag attrs

    pub def text (content : String) : Html.Node := Html.Node.node_text content
    pub def raw (tag : String) (attrs : List Html.Attr) (content : String) : Html.Node := Html.Node.node_raw_text tag attrs content
    pub def comment (content : String) : Html.Node := Html.Node.node_comment content
    pub def doctype (declaration : String) : Html.Node := Html.Node.node_doctype declaration
    pub def fragment (children : List Html.Node) : Html.Node := Html.Node.node_fragment children

    // ═══ Documents and components ═══

    /// A complete document. The doctype must precede `<html>`, so the
    /// result is a fragment rather than an `<html>` element with three
    /// children.
    pub def document (head : List Html.Node) (body : List Html.Node) : Html.Node :=
        Html.Node.node_fragment
            [ Html.Node.node_doctype "html",
              Html.Node.node_element "html" List.empty
                  [ Html.Node.node_element "head" List.empty head,
                    Html.Node.node_element "body" List.empty body ] ]

    /// A document with attributes on `<html>`, `<head>` and `<body>`.
    pub def document_with (html_attrs : List Html.Attr) (head_attrs : List Html.Attr) (body_attrs : List Html.Attr) (head : List Html.Node) (body : List Html.Node) : Html.Node :=
        Html.Node.node_fragment
            [ Html.Node.node_doctype "html",
              Html.Node.node_element "html" html_attrs
                  [ Html.Node.node_element "head" head_attrs head,
                    Html.Node.node_element "body" body_attrs body ] ]

    /// The common case: a UTF-8 document with `<meta charset="utf-8">`
    /// prepended to the head.
    pub def document_utf8 (head : List Html.Node) (body : List Html.Node) : Html.Node :=
        let charset_meta := Html.Node.node_void "meta" [Html.charset "utf-8"] in
        Html.document_with List.empty List.empty List.empty (List.cons charset_meta head) body

    /// A navigation bar over `(href, label)` links, in source order.
    pub def navbar (links : List (Pair String String)) : Html.Node :=
        Html.nav
            [Html.class_ ["navbar"]]
            [Html.ul List.empty (List.map navbar_link links)]

    /// A title/body card.
    pub def card (title : String) (body : String) : Html.Node :=
        Html.div
            [Html.class_ ["card"]]
            [ Html.h2 List.empty [Html.text title],
              Html.p List.empty [Html.text body] ]
}
