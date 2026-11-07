/// A chapter's on-page table of contents: its `h2`/`h3` headings with ids,
/// read from the rendered (and passed) body.
use xml_html::html {Html.Node, Html.Attr}
use std::list {List.filter_map}
use lib::passes {Passes.id_of}

/// One heading: `level` 2 or 3, its anchor id, and its plain text.
pub struct TocEntry {
    level : I64,
    id : String,
    text : String,
}

instance Copy TocEntry {
    def copy (e : TocEntry) : Pair TocEntry TocEntry := Pair.pair e e
}

/// The TOC entries of a chapter body, in order. Only top-level headings
/// count: the markdown renderer emits a section heading at the top level,
/// and a heading inside a blockquote or list is not a section.
pub def Toc.of_nodes (nodes : List Html.Node) : List TocEntry :=
    List.filter_map toc_entry nodes

def heading_level (tag : String) : I64 :=
    if String.beq tag "h2" then 2 else if String.beq tag "h3" then 3 else 0

def toc_entry (n : Html.Node) : Option TocEntry :=
    match n {
        Html.Node.node_element tag attrs children => heading_entry (heading_level tag) attrs children,
        _ => Option.none,
    }

def heading_entry (level : I64) (attrs : List Html.Attr) (children : List Html.Node) : Option TocEntry :=
    if level == 0
    then Option.none
    else
        match Passes.id_of attrs {
            Option.none => Option.none,
            Option.some id => Option.some { level := level, id := id, text := String.trim (Toc.text_of children) },
        }

/// The plain text of some nodes, leaving out the heading's own `#` anchor.
pub def Toc.text_of (nodes : List Html.Node) : String :=
    match nodes {
        List.empty => "",
        List.cons n rest => String.concat (node_text n) (Toc.text_of rest),
    }

// Recursion over the node tree: `children` are subterms of `n`, but the
// walk threads them through `Toc.text_of`.
#[terminating]
def node_text (n : Html.Node) : String :=
    match n {
        Html.Node.node_text t => t,
        Html.Node.node_element tag attrs children =>
            if String.beq tag "a" && is_anchor attrs then "" else Toc.text_of children,
        Html.Node.node_fragment children => Toc.text_of children,
        _ => "",
    }

def is_anchor (attrs : List Html.Attr) : Bool :=
    match attrs {
        List.empty => false,
        List.cons a rest => anchor_attr a rest,
    }

// Mutual recursion with `is_anchor` on the list's own tail.
#[terminating]
def anchor_attr (a : Html.Attr) (rest : List Html.Attr) : Bool :=
    match a {
        Html.Attr.attr name value => (String.beq name "class" && String.beq value "anchor") || is_anchor rest,
        Html.Attr.bool_attr _ => is_anchor rest,
    }
