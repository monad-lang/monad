/// Render the AST as `Html.Node`s.
///
/// The output deliberately matches cmark's block formatting -- one newline
/// after each block, tight list items without a `<p>` wrapper, loose ones
/// with it -- so the conformance harness can compare byte for byte without
/// normalising whitespace. Text goes through `Html.Node.node_text`, so the
/// shared escaper owns `& < >`.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width}
use xml_html::html {Html.Attr, Html.Node}
use lib::options {Markdown.HtmlOptions, Markdown.default_html_options}
use lib::href {Markdown.escape_href}
use lib::types {
    Markdown.Align, Markdown.Block, Markdown.Document, Markdown.Inline,
    Markdown.ListItem, Markdown.ListKind, Markdown.TableRow,
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
        Option.some t => [Markdown.at "href" (Markdown.escape_href dest), Markdown.at "title" t],
        Option.none => [Markdown.at "href" (Markdown.escape_href dest)]
    }

/// cmark's attribute order: `src`, `alt`, then `title`.
def Markdown.image_attrs (dest : String) (title : Option String) (alt : String) : List Html.Attr :=
    match title {
        Option.some t =>
            [Markdown.at "src" (Markdown.escape_href dest), Markdown.at "alt" alt, Markdown.at "title" t],
        Option.none => [Markdown.at "src" (Markdown.escape_href dest), Markdown.at "alt" alt]
    }

def Markdown.autolink_attrs (dest : String) : List Html.Attr :=
    List.cons (Markdown.at "href" (Markdown.escape_href dest)) List.empty

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
                        List.cons (Markdown.at "class"
                            (String.concat "language-" (Markdown.first_word_of language))) List.empty,
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
        block_table aligns head rows =>
            [ Markdown.el "table" List.empty
                [ Markdown.txt "\n",
                  Markdown.el "thead" List.empty
                    [ Markdown.txt "\n",
                      Markdown.row_node opts "th" aligns head.cells,
                      Markdown.txt "\n" ],
                  Markdown.txt "\n",
                  Markdown.el "tbody" List.empty
                    (List.cons (Markdown.txt "\n") (Markdown.rows_nodes opts aligns rows)),
                  Markdown.txt "\n" ],
              Markdown.txt "\n" ]
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
    let children : List Html.Node := Markdown.item_children opts tight item.blocks in
    Markdown.el "li" List.empty (Markdown.task_prefix item.checked children)

/// A task-list item starts with its checkbox and a space.
def Markdown.task_prefix (checked : Option Bool) (children : List Html.Node) : List Html.Node :=
    match checked {
        Option.none => children,
        Option.some state =>
            List.cons (Markdown.checkbox state)
                (List.cons (Markdown.txt " ") children)
    }

def Markdown.checkbox (state : Bool) : Html.Node :=
    let attrs : List Html.Attr :=
        if state
        then [ Markdown.at "type" "checkbox", Markdown.at "checked" "", Markdown.at "disabled" "" ]
        else [ Markdown.at "type" "checkbox", Markdown.at "disabled" "" ] in
    Html.Node.node_void "input" attrs

#[partial]
/// cmark's `cr()`: a block child starts on its own line, so a loose item opens
/// with a newline and a tight item puts one before any non-paragraph child.
def Markdown.item_children (opts : Markdown.HtmlOptions) (tight : Bool) (blocks : List Markdown.Block) : List Html.Node :=
    if List.is_empty blocks
    then List.empty
    else if tight
    then Markdown.tight_children opts blocks
    else List.cons (Markdown.txt "\n") (Markdown.blocks_nodes opts blocks)

/// Whether the last emitted piece is already a newline (cmark's `cr()`).
def Markdown.at_line_start (acc : List Html.Node) : Bool :=
    match acc {
        List.empty => false,
        List.cons n _ =>
            match n {
                Html.Node.node_text t => String.beq t "\n",
                _ => false
            }
    }

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
                    _ =>
                        if Markdown.at_line_start acc
                        then Markdown.block_nodes opts b
                        else List.cons (Markdown.txt "\n") (Markdown.block_nodes opts b)
                } in
            Markdown.tight_children_rev opts rest (Markdown.nodes_rev nodes acc)
    }

/// cmark uses the info string's first word as the language class.
#[partial]
def Markdown.first_word (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
                then String.concat_list (List.reverse acc)
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.first_word (String.drop w s) (List.cons (String.slice s 0 w) acc),
            Option.none => String.concat_list (List.reverse acc)
        }

pub def Markdown.first_word_of (s : String) : String :=
    Markdown.first_word s List.empty

// ─── Tables (GFM) ───

#[partial]
def Markdown.aligns_len (aligns : List Markdown.Align) : I64 :=
    match aligns {
        List.empty => 0i64,
        List.cons _ rest => I64.add 1i64 (Markdown.aligns_len rest)
    }

/// A row is padded with empty cells and extra cells are dropped, so every
/// row has the header's width.
#[partial]
def Markdown.normalize_row (n : I64) (cells : List (List Markdown.Inline)) : List (List Markdown.Inline) :=
    if I64.lt n 1i64
    then List.empty
    else
        match cells {
            List.empty => List.cons List.empty (Markdown.normalize_row (I64.sub n 1i64) List.empty),
            List.cons c rest => List.cons c (Markdown.normalize_row (I64.sub n 1i64) rest)
        }

def Markdown.align_attr (align : Markdown.Align) : List Html.Attr :=
    match align {
        Markdown.Align.align_left => [Markdown.at "align" "left"],
        Markdown.Align.align_center => [Markdown.at "align" "center"],
        Markdown.Align.align_right => [Markdown.at "align" "right"],
        Markdown.Align.align_none => List.empty
    }

#[partial]
def Markdown.cell_nodes
    (opts : Markdown.HtmlOptions) (tag : String) (aligns : List Markdown.Align)
    (cells : List (List Markdown.Inline)) : List Html.Node :=
    match cells {
        List.empty => List.empty,
        List.cons c rest =>
            let align : Markdown.Align :=
                match aligns {
                    List.empty => Markdown.Align.align_none,
                    List.cons a _ => a
                } in
            let align_rest : List Markdown.Align :=
                match aligns {
                    List.empty => List.empty,
                    List.cons _ more => more
                } in
            List.cons (Markdown.el tag (Markdown.align_attr align) (Markdown.inline_nodes opts c))
                (List.cons (Markdown.txt "\n")
                    (Markdown.cell_nodes opts tag align_rest rest))
    }

def Markdown.row_node
    (opts : Markdown.HtmlOptions) (tag : String) (aligns : List Markdown.Align)
    (cells : List (List Markdown.Inline)) : Html.Node :=
    Markdown.el "tr" List.empty
        (List.cons (Markdown.txt "\n") (Markdown.cell_nodes opts tag aligns cells))

#[partial]
def Markdown.rows_nodes
    (opts : Markdown.HtmlOptions) (aligns : List Markdown.Align)
    (rows : List Markdown.TableRow) : List Html.Node :=
    List.reverse (Markdown.rows_nodes_rev opts aligns rows List.empty)

#[partial]
def Markdown.rows_nodes_rev
    (opts : Markdown.HtmlOptions) (aligns : List Markdown.Align)
    (rows : List Markdown.TableRow) (acc : List Html.Node) : List Html.Node :=
    match rows {
        List.empty => acc,
        List.cons r rest =>
            let n : I64 := Markdown.aligns_len aligns in
            let cells : List (List Markdown.Inline) := Markdown.normalize_row n r.cells in
            let nodes : List Html.Node :=
                List.cons (Markdown.el "tr" List.empty
                        (List.cons (Markdown.txt "\n") (Markdown.cell_nodes opts "td" aligns cells)))
                    (List.cons (Markdown.txt "\n") List.empty) in
            Markdown.rows_nodes_rev opts aligns rest (Markdown.nodes_rev nodes acc)
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
