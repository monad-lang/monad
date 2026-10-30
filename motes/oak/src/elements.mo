// The pure builder surface: attributes and elements as plain functions
// returning `Oak.Node Msg`, in the Elm-shaped call style
// `Html.div [Html.class_ ["card"]] [Html.text "hi"]`.
//
// The public defs live inside `with Html { … }`, which prefixes each
// declaration name (`Html.div`, `Html.class_`); call sites therefore read
// like an Elm module without every line spelling the prefix. Types are NOT
// declared here: a `with`-declared type's constructors are unbound across
// motes on the Rust host (implementations/with-block-constructors-cross-module).
// Private helpers stay outside the block.
//
// `Oak.Node`/`Oak.Attr` wrap `xml_html` values; only event bindings are new.
// See `lib::typed` for the lowering that turns them into the markup tree and
// the handler table.

use std::list {List.intercalate}
use xml_html::html {Html.Attr, Html.Node}
use xml_html::html {}
use lib::typed {Oak.Attr, Oak.Node}

def mk_element {Msg : Type} (tag : String) (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
    Oak.Node.element tag attrs children

def mk_void {Msg : Type} (tag : String) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
    Oak.Node.void tag attrs

// `navbar_link` is a named helper, not an inline lambda passed to
// `List.map` (the json/toml precedent), and it sits outside the block so
// only the user-facing component name is prefixed.
def navbar_link {Msg : Type} (link : Pair String String) : Oak.Node Msg :=
    match link {
        Pair.pair href label =>
            Html.li List.empty
                [Html.a [Html.href href] [Html.text label]]
    }

#[terminating]
def navbar_links {Msg : Type} (links : List (Pair String String)) : List (Oak.Node Msg) :=
    match links {
        List.empty => List.empty,
        List.cons link rest => List.cons (navbar_link link) (navbar_links rest),
    }

with Html {
    // ═══ Attributes ═══
    //
    // Reserved keywords get the underscore spelling (`class`, `type`, `for`,
    // `open`; see RESERVED_KEYWORDS in rust/core/src/parser.rs). The emitted
    // attribute name never carries the underscore.

    pub def id_ {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "id" value

    pub def class_ {Msg : Type} (names : List String) : Oak.Attr Msg :=
        Html.attr "class" (List.intercalate " " names)

    pub def href {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "href" value

    pub def src {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "src" value

    pub def alt {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "alt" value

    pub def type_ {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "type" value

    pub def value_ {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "value" value

    pub def placeholder {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "placeholder" value

    pub def name_ {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "name" value

    pub def for_ {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "for" value

    pub def style_attr {Msg : Type} (value : String) : Oak.Attr Msg :=
        Html.attr "style" value

    pub def data {Msg : Type} (key : String) (value : String) : Oak.Attr Msg :=
        Html.attr (String.concat "data-" key) value

    /// The attribute a keyed list child carries. One literal, imported by
    /// `oak_wasm`'s diff so the two motes cannot drift.
    pub def key_attr : String := "data-oak-key"

    /// Mark a list child with a stable identity. A list whose children all
    /// carry distinct keys is reconciled by key, so reordering keeps the
    /// DOM nodes (and their focus/scroll/listeners) instead of rewriting
    /// each position.
    pub def key {Msg : Type} (k : String) : Oak.Attr Msg := Html.attr Html.key_attr k

    pub def open_ {Msg : Type} : Oak.Attr Msg := Html.bool_attr "open"
    pub def disabled {Msg : Type} : Oak.Attr Msg := Html.bool_attr "disabled"
    pub def checked {Msg : Type} : Oak.Attr Msg := Html.bool_attr "checked"
    pub def required {Msg : Type} : Oak.Attr Msg := Html.bool_attr "required"
    pub def readonly {Msg : Type} : Oak.Attr Msg := Html.bool_attr "readonly"
    pub def selected {Msg : Type} : Oak.Attr Msg := Html.bool_attr "selected"
    pub def autofocus {Msg : Type} : Oak.Attr Msg := Html.bool_attr "autofocus"
    pub def hidden {Msg : Type} : Oak.Attr Msg := Html.bool_attr "hidden"

    // Generic and form attributes. The curated list above covers the common
    // surface; `attr`/`bool_attr` are the escape hatch for `role`, `aria-*`,
    // `method`, `action`, `enctype`, `target`, `rel`, `charset`, dimensions
    // and validation attributes. Names that are Monad keywords take `_`.

    pub def attr {Msg : Type} (name : String) (value : String) : Oak.Attr Msg :=
        Oak.Attr.html (Html.Attr.attr name value)

    pub def bool_attr {Msg : Type} (name : String) : Oak.Attr Msg :=
        Oak.Attr.html (Html.Attr.bool_attr name)

    pub def role {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "role" value
    pub def aria {Msg : Type} (name : String) (value : String) : Oak.Attr Msg :=
        Html.attr (String.concat "aria-" name) value
    pub def method_ {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "method" value
    pub def action {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "action" value
    pub def enctype {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "enctype" value
    pub def target {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "target" value
    pub def rel {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "rel" value
    pub def charset {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "charset" value
    pub def accept {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "accept" value
    pub def width {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "width" (I64.to_string value)
    pub def height {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "height" (I64.to_string value)
    pub def min_ {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "min" value
    pub def max_ {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "max" value
    pub def step {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "step" value
    pub def pattern_ {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "pattern" value
    pub def autocomplete {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "autocomplete" value
    pub def minlength {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "minlength" (I64.to_string value)
    pub def maxlength {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "maxlength" (I64.to_string value)
    pub def multiple {Msg : Type} : Oak.Attr Msg := Html.bool_attr "multiple"
    pub def novalidate {Msg : Type} : Oak.Attr Msg := Html.bool_attr "novalidate"

    // Element-level interaction and document attributes.
    pub def draggable {Msg : Type} (value : Bool) : Oak.Attr Msg :=
        Html.attr "draggable" (if value then "true" else "false")
    pub def contenteditable {Msg : Type} (value : Bool) : Oak.Attr Msg :=
        Html.attr "contenteditable" (if value then "true" else "false")
    pub def translate {Msg : Type} (value : Bool) : Oak.Attr Msg :=
        Html.attr "translate" (if value then "yes" else "no")
    pub def spellcheck {Msg : Type} (value : Bool) : Oak.Attr Msg :=
        Html.attr "spellcheck" (if value then "true" else "false")
    pub def tabindex {Msg : Type} (value : I64) : Oak.Attr Msg :=
        Html.attr "tabindex" (I64.to_string value)
    pub def dir {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "dir" value
    pub def lang {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "lang" value
    /// `title` already names the element; the attribute takes `_attr`.
    pub def title_attr {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "title" value

    /// The conventional `enctype` for a file-upload form.
    pub def enctype_multipart : String := "multipart/form-data"

    // ═══ Structural and text-level elements ═══

    pub def div {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "div" attrs children

    pub def span {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "span" attrs children

    pub def p {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "p" attrs children

    pub def a {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "a" attrs children

    pub def ul {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "ul" attrs children

    pub def ol {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "ol" attrs children

    pub def li {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "li" attrs children

    pub def h1 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h1" attrs children

    pub def h2 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h2" attrs children

    pub def h3 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h3" attrs children

    pub def h4 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h4" attrs children

    pub def h5 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h5" attrs children

    pub def h6 {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "h6" attrs children

    pub def header {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "header" attrs children

    pub def footer {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "footer" attrs children

    pub def nav {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "nav" attrs children

    pub def main_ {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "main" attrs children

    pub def section {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "section" attrs children

    pub def article {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "article" attrs children

    pub def aside {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "aside" attrs children

    // ═══ Table family ═══

    pub def table {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "table" attrs children

    pub def thead {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "thead" attrs children

    pub def tbody {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "tbody" attrs children

    pub def tfoot {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "tfoot" attrs children

    pub def tr {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "tr" attrs children

    pub def th {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "th" attrs children

    pub def td {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "td" attrs children

    pub def caption {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "caption" attrs children

    pub def colgroup {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "colgroup" attrs children

    // ═══ Form family ═══

    pub def form {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "form" attrs children

    pub def label {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "label" attrs children

    pub def fieldset {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "fieldset" attrs children

    pub def legend {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "legend" attrs children

    pub def select {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "select" attrs children

    pub def option {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "option" attrs children

    pub def optgroup {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "optgroup" attrs children

    pub def textarea {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "textarea" attrs children

    pub def button {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "button" attrs children

    pub def datalist {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "datalist" attrs children

    pub def output {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "output" attrs children

    // ═══ Document pieces ═══

    pub def title {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "title" attrs children

    pub def head {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "head" attrs children

    pub def body {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "body" attrs children

    pub def canvas {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "canvas" attrs children

    pub def video {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "video" attrs children

    pub def audio {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element "audio" attrs children

    // ═══ Void elements ═══

    pub def input {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "input" attrs
    pub def img {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "img" attrs
    pub def br {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "br" attrs
    pub def hr {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "hr" attrs
    pub def meta {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "meta" attrs
    pub def link {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "link" attrs
    pub def col {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "col" attrs
    pub def source {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "source" attrs
    pub def area {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "area" attrs
    pub def base {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "base" attrs
    pub def embed {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "embed" attrs
    pub def track {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "track" attrs
    pub def wbr {Msg : Type} (attrs : List (Oak.Attr Msg)) : Oak.Node Msg := mk_void "wbr" attrs

    // ═══ Raw-text elements ═══
    //
    // Raw-text nodes carry attributes too, so `<script type="module" src=…>`
    // is representable.

    pub def script {Msg : Type} (attrs : List (Oak.Attr Msg)) (content : String) : Oak.Node Msg :=
        Oak.Node.raw_text "script" attrs content

    pub def style {Msg : Type} (attrs : List (Oak.Attr Msg)) (content : String) : Oak.Node Msg :=
        Oak.Node.raw_text "style" attrs content

    // ═══ Escape hatches and node constructors ═══

    pub def node {Msg : Type} (tag : String) (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        mk_element tag attrs children

    pub def void {Msg : Type} (tag : String) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        mk_void tag attrs

    /// A plain text node.
    pub def text {Msg : Type} (content : String) : Oak.Node Msg :=
        Oak.Node.raw (Html.Node.node_text content)

    /// Any raw `Html.Node`, lowered through untouched.
    pub def html_node {Msg : Type} (node : Html.Node) : Oak.Node Msg :=
        Oak.Node.raw node

    pub def raw {Msg : Type} (tag : String) (attrs : List (Oak.Attr Msg)) (content : String) : Oak.Node Msg :=
        Oak.Node.raw_text tag attrs content
    pub def comment {Msg : Type} (content : String) : Oak.Node Msg :=
        Oak.Node.raw (Html.Node.node_comment content)
    pub def doctype {Msg : Type} (declaration : String) : Oak.Node Msg :=
        Oak.Node.raw (Html.Node.node_doctype declaration)
    pub def fragment {Msg : Type} (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Oak.Node.fragment children

    // ═══ Documents and components ═══

    /// A complete document. The doctype must precede `<html>`, so the
    /// result is a fragment rather than an `<html>` element with three
    /// children.
    pub def document {Msg : Type} (head : List (Oak.Node Msg)) (body : List (Oak.Node Msg)) : Oak.Node Msg :=
        Oak.Node.fragment
            [ Oak.Node.raw (Html.Node.node_doctype "html"),
              mk_element "html" List.empty
                  [ mk_element "head" List.empty head,
                    mk_element "body" List.empty body ] ]

    /// A document with attributes on `<html>`, `<head>` and `<body>`.
    pub def document_with {Msg : Type} (html_attrs : List (Oak.Attr Msg)) (head_attrs : List (Oak.Attr Msg)) (body_attrs : List (Oak.Attr Msg)) (head : List (Oak.Node Msg)) (body : List (Oak.Node Msg)) : Oak.Node Msg :=
        Oak.Node.fragment
            [ Oak.Node.raw (Html.Node.node_doctype "html"),
              mk_element "html" html_attrs
                  [ mk_element "head" head_attrs head,
                    mk_element "body" body_attrs body ] ]

    /// The common case: a UTF-8 document with `<meta charset="utf-8">`
    /// prepended to the head.
    pub def document_utf8 {Msg : Type} (head : List (Oak.Node Msg)) (body : List (Oak.Node Msg)) : Oak.Node Msg :=
        let charset_meta : Oak.Node Msg := mk_void "meta" [Html.charset "utf-8"] in
        Html.document_with List.empty List.empty List.empty (List.cons charset_meta head) body

    /// A navigation bar over `(href, label)` links, in source order.
    pub def navbar {Msg : Type} (links : List (Pair String String)) : Oak.Node Msg :=
        Html.nav
            [Html.class_ ["navbar"]]
            [Html.ul List.empty (navbar_links links)]

    /// A title/body card.
    pub def card {Msg : Type} (title : String) (body : String) : Oak.Node Msg :=
        Html.div
            [Html.class_ ["card"]]
            [ Html.h2 List.empty [Html.text title],
              Html.p List.empty [Html.text body] ]
}
