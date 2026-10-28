/// Render the AST as `Html.Node`s.
///
/// The output deliberately matches cmark's block formatting -- one newline
/// after each block, tight list items without a `<p>` wrapper, loose ones
/// with it -- so the conformance harness can compare byte for byte without
/// normalising whitespace. Text goes through `Html.Node.node_text`, so the
/// shared escaper owns `& < >`.
use init::string {}
use xml_html::html {Html.Attr, Html.Node}
use lib::options {Markdown.HtmlOptions, Markdown.default_html_options}
use lib::types {
    Markdown.Block, Markdown.Document, Markdown.Inline, Markdown.ListItem,
    Markdown.ListKind,
}

open Markdown.Block {
    block_paragraph, block_heading, block_thematic_break, block_code_block,
    block_quote, block_list, block_table, block_html_block,
}
open Markdown.Inline {
    inline_text, inline_soft_break, inline_hard_break, inline_emphasis,
    inline_strong, inline_strikethrough, inline_code, inline_link,
    inline_image, inline_autolink, inline_html,
}

// ─── Small helpers ───

def Markdown.el (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    Html.Node.node_element tag attrs children

def Markdown.txt (s : String) : Html.Node :=
    Html.Node.node_text s

def Markdown.vo (tag : String) (attrs : List Html.Attr) : Html.Node :=
    Html.Node.node_void tag attrs

def Markdown.at (name : String) (value : String) : Html.Attr :=
    Html.Attr.attr name value

/// Append `nodes` (in order) to a reversed accumulator.
#[partial]
def Markdown.nodes_rev (nodes : List Html.Node) (acc : List Html.Node) : List Html.Node :=
    match nodes {
        List.empty => acc,
        List.cons n rest => Markdown.nodes_rev rest (List.cons n acc)
    }

// ─── Inlines ───

#[partial]
def Markdown.inline_nodes (opts : Markdown.HtmlOptions) (inlines : List Markdown.Inline) : List Html.Node :=
    List.reverse (Markdown.inline_nodes_rev opts inlines List.empty)

#[partial]
def Markdown.inline_nodes_rev (opts : Markdown.HtmlOptions) (inlines : List Markdown.Inline) (acc : List Html.Node) : List Html.Node :=
    match inlines {
        List.empty => acc,
        List.cons i rest =>
            Markdown.inline_nodes_rev opts rest (Markdown.nodes_rev (Markdown.inline_node opts i) acc)
    }

def Markdown.inline_node (opts : Markdown.HtmlOptions) (i : Markdown.Inline) : List Html.Node :=
    match i {
        inline_text t => [Markdown.txt t],
        inline_soft_break => [Markdown.txt "\n"],
        inline_hard_break => [Markdown.vo "br" List.empty, Markdown.txt "\n"],
        inline_emphasis children => [Markdown.el "em" List.empty (Markdown.inline_nodes opts children)],
        inline_strong children => [Markdown.el "strong" List.empty (Markdown.inline_nodes opts children)],
        inline_strikethrough children => [Markdown.el "del" List.empty (Markdown.inline_nodes opts children)],
        inline_code t => [Markdown.el "code" List.empty [Markdown.txt t]],
        inline_link dest title children =>
            [Markdown.el "a" (Markdown.link_attrs dest title) (Markdown.inline_nodes opts children)],
        inline_image dest title alt =>
            [Markdown.vo "img" (Markdown.image_attrs dest title alt)],
        inline_autolink dest label =>
            [Markdown.el "a" (Markdown.autolink_attrs dest) [Markdown.txt label]],
        inline_html literal =>
            if opts.allow_raw_html
            then [Html.Node.node_raw_html literal]
            else [Markdown.txt literal]
    }

/// cmark's attribute order: `href`, then `title`.
def Markdown.link_attrs (dest : String) (title : Option String) : List Html.Attr :=
    match title {
        Option.some t => [Markdown.at "href" dest, Markdown.at "title" t],
        Option.none => [Markdown.at "href" dest]
    }

/// cmark's attribute order: `src`, `alt`, then `title`.
def Markdown.image_attrs (dest : String) (title : Option String) (alt : String) : List Html.Attr :=
    match title {
        Option.some t => [Markdown.at "src" dest, Markdown.at "alt" alt, Markdown.at "title" t],
        Option.none => [Markdown.at "src" dest, Markdown.at "alt" alt]
    }

def Markdown.autolink_attrs (dest : String) : List Html.Attr :=
    List.cons (Markdown.at "href" dest) List.empty

// ─── Blocks ───

#[partial]
#[partial]
def Markdown.block_nodes (opts : Markdown.HtmlOptions) (b : Markdown.Block) : List Html.Node :=
    match b {
        block_paragraph inlines =>
            [Markdown.el "p" List.empty (Markdown.inline_nodes opts inlines), Markdown.txt "\n"],
        block_heading level inlines =>
            [ Markdown.el (String.concat "h" (I64.to_string level)) List.empty
                (Markdown.inline_nodes opts inlines),
              Markdown.txt "\n" ],
        block_thematic_break => [Markdown.vo "hr" List.empty, Markdown.txt "\n"],
        block_code_block info literal =>
            let attrs : List Html.Attr :=
                match info {
                    Option.some language =>
                        List.cons (Markdown.at "class" (String.concat "language-" language)) List.empty,
                    Option.none => List.empty
                } in
            [ Markdown.el "pre" List.empty
                [Markdown.el "code" attrs [Markdown.txt literal]],
              Markdown.txt "\n" ],
        block_html_block literal =>
            if opts.allow_raw_html
            then [Html.Node.node_raw_html literal, Markdown.txt "\n"]
            else [Markdown.txt literal, Markdown.txt "\n"],
        block_quote blocks =>
            [ Markdown.el "blockquote" List.empty
                (List.cons (Markdown.txt "\n") (Markdown.blocks_nodes opts blocks)),
              Markdown.txt "\n" ],
        block_list kind tight items =>
            [ Markdown.el (Markdown.list_tag kind) (Markdown.list_attrs kind)
                (List.cons (Markdown.txt "\n") (Markdown.items_nodes opts tight items)),
              Markdown.txt "\n" ],
        block_table _aligns _head _rows =>
            // Phase 4 owns tables; an unrendered table must not crash.
            [Markdown.txt "\n"]
    }

def Markdown.list_tag (kind : Markdown.ListKind) : String :=
    match kind {
        Markdown.ListKind.list_ordered _ _ => "ol",
        Markdown.ListKind.list_bullet _ => "ul"
    }

def Markdown.list_attrs (kind : Markdown.ListKind) : List Html.Attr :=
    match kind {
        Markdown.ListKind.list_ordered start _ =>
            if I64.beq start 1i64
            then List.empty
            else List.cons (Markdown.at "start" (I64.to_string start)) List.empty,
        Markdown.ListKind.list_bullet _ => List.empty
    }

#[partial]
def Markdown.blocks_nodes (opts : Markdown.HtmlOptions) (blocks : List Markdown.Block) : List Html.Node :=
    List.reverse (Markdown.blocks_nodes_rev opts blocks List.empty)

#[partial]
def Markdown.blocks_nodes_rev (opts : Markdown.HtmlOptions) (blocks : List Markdown.Block) (acc : List Html.Node) : List Html.Node :=
    match blocks {
        List.empty => acc,
        List.cons b rest =>
            Markdown.blocks_nodes_rev opts rest (Markdown.nodes_rev (Markdown.block_nodes opts b) acc)
    }

#[partial]
def Markdown.items_nodes (opts : Markdown.HtmlOptions) (tight : Bool) (items : List Markdown.ListItem) : List Html.Node :=
    List.reverse (Markdown.items_nodes_rev opts tight items List.empty)

#[partial]
def Markdown.items_nodes_rev (opts : Markdown.HtmlOptions) (tight : Bool) (items : List Markdown.ListItem) (acc : List Html.Node) : List Html.Node :=
    match items {
        List.empty => acc,
        List.cons item rest =>
            let nodes : List Html.Node :=
                List.cons (Markdown.item_node opts tight item) (List.cons (Markdown.txt "\n") List.empty) in
            Markdown.items_nodes_rev opts tight rest (Markdown.nodes_rev nodes acc)
    }

#[partial]
def Markdown.item_node (opts : Markdown.HtmlOptions) (tight : Bool) (item : Markdown.ListItem) : Html.Node :=
    Markdown.el "li" List.empty (Markdown.item_children opts tight item.blocks)

#[partial]
def Markdown.item_children (opts : Markdown.HtmlOptions) (tight : Bool) (blocks : List Markdown.Block) : List Html.Node :=
    if tight
    then Markdown.tight_children opts blocks
    else Markdown.blocks_nodes opts blocks

/// A tight list item renders paragraphs without their `<p>` wrapper.
#[partial]
#[partial]
def Markdown.tight_children (opts : Markdown.HtmlOptions) (blocks : List Markdown.Block) : List Html.Node :=
    List.reverse (Markdown.tight_children_rev opts blocks List.empty)

#[partial]
def Markdown.tight_children_rev (opts : Markdown.HtmlOptions) (blocks : List Markdown.Block) (acc : List Html.Node) : List Html.Node :=
    match blocks {
        List.empty => acc,
        List.cons b rest =>
            let nodes : List Html.Node :=
                match b {
                    block_paragraph inlines => Markdown.inline_nodes opts inlines,
                    _ => Markdown.block_nodes opts b
                } in
            Markdown.tight_children_rev opts rest (Markdown.nodes_rev nodes acc)
    }

// ─── Entry points ───

pub def Markdown.to_html_nodes_with (opts : Markdown.HtmlOptions) (doc : Markdown.Document) : List Html.Node :=
    Markdown.blocks_nodes opts doc.blocks

pub def Markdown.to_html_with (opts : Markdown.HtmlOptions) (doc : Markdown.Document) : Html.Node :=
    Html.Node.node_fragment (Markdown.to_html_nodes_with opts doc)

pub def Markdown.to_html_nodes (doc : Markdown.Document) : List Html.Node :=
    Markdown.to_html_nodes_with Markdown.default_html_options doc

pub def Markdown.to_html (doc : Markdown.Document) : Html.Node :=
    Html.Node.node_fragment (Markdown.to_html_nodes doc)
