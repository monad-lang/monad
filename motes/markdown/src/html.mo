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
use lib::inline {Markdown.flatten_alt}
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

/// cmark's safe-URL rule (`safe_urls`, on by default): `javascript:`,
/// `vbscript:`, `file:` and `data:` (except `data:image/`) are not rendered
/// as a URL. Leading whitespace and control bytes are ignored, as cmark does.
#[partial]
def Markdown.unurl_unsafe_check (s : String) : String :=
    match String.get s 0 {
        Option.some b =>
            if U8.lt b 33u8 then Markdown.unurl_unsafe_check (String.drop 1i64 s) else s,
        Option.none => s
    }

pub def Markdown.url_is_safe (dest : String) : Bool :=
    let lower : String := String.to_lowercase (Markdown.unurl_unsafe_check dest) in
    if String.starts_with "javascript:" lower then false
    else if String.starts_with "vbscript:" lower then false
    else if String.starts_with "file:" lower then false
    else if String.starts_with "data:" lower then String.starts_with "data:image/" lower
    else true

def Markdown.url_allowed (opts : Markdown.HtmlOptions) (dest : String) : Bool :=
    if opts.safe_urls then Markdown.url_is_safe dest else true

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
            if Markdown.url_allowed opts dest
            then [Markdown.el "a" (Markdown.link_attrs dest title) (Markdown.inline_nodes opts children)]
            else Markdown.inline_nodes opts children,
        inline_image dest title alt =>
            if Markdown.url_allowed opts dest
            then [Markdown.vo "img" (Markdown.image_attrs dest title alt)]
            else [Markdown.txt alt],
        inline_autolink dest label =>
            if Markdown.url_allowed opts dest
            then [Markdown.el "a" (Markdown.autolink_attrs dest) [Markdown.txt label]]
            else [Markdown.txt label],
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

// ─── Heading ids ───

/// GitHub-style slug: ASCII lowercase, spaces become `-`, everything that is
/// not a letter, digit, `-` or `_` is dropped.
#[partial]
def Markdown.slug_go (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.some b =>
                let w : I64 := Markdown.char_width s in
                let piece : String := String.slice s 0 w in
                if U8.beq b 32u8
                then Markdown.slug_go (String.drop w s) (List.cons "-" acc)
                else if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8)
                then Markdown.slug_go (String.drop w s) (List.cons piece acc)
                else if Bool.and (U8.lt 64u8 b) (U8.lt b 91u8)
                then Markdown.slug_go (String.drop w s)
                        (List.cons (String.to_lowercase piece) acc)
                else if Bool.and (U8.lt 96u8 b) (U8.lt b 123u8)
                then Markdown.slug_go (String.drop w s) (List.cons piece acc)
                else if Bool.or (U8.beq b 45u8) (U8.beq b 95u8)
                then Markdown.slug_go (String.drop w s) (List.cons piece acc)
                else Markdown.slug_go (String.drop w s) acc,
            Option.none => String.concat_list (List.reverse acc)
        }

pub def Markdown.slug_of (text : String) : String :=
    Markdown.slug_go text List.empty

/// `base`, then `base-1`, `base-2`, ... for repeats.
#[partial]
def Markdown.unique_slug (base : String) (taken : List String) : String :=
    if Markdown.member_slug base taken
    then Markdown.unique_slug_suffix base taken 1i64
    else base

#[partial]
def Markdown.unique_slug_suffix (base : String) (taken : List String) (n : I64) : String :=
    let candidate : String :=
        String.concat base (String.concat "-" (I64.to_string n)) in
    if Markdown.member_slug candidate taken
    then Markdown.unique_slug_suffix base taken (I64.add n 1i64)
    else candidate

#[partial]
def Markdown.member_slug (slug : String) (taken : List String) : Bool :=
    match taken {
        List.empty => false,
        List.cons t rest => Bool.or (String.beq t slug) (Markdown.member_slug slug rest)
    }

/// The heading texts of a document, in order, including headings inside
/// quotes and list items.
#[partial]
pub def Markdown.heading_texts (blocks : List Markdown.Block) : List String :=
    Markdown.heading_texts_rev blocks List.empty

#[partial]
def Markdown.heading_texts_rev (blocks : List Markdown.Block) (acc : List String) : List String :=
    match blocks {
        List.empty => List.reverse acc,
        List.cons b rest =>
            match b {
                block_heading _ inlines =>
                    Markdown.heading_texts_rev rest (List.cons (Markdown.plain_of inlines) acc),
                block_quote inner =>
                    Markdown.heading_texts_rev rest
                        (Markdown.rev_onto (Markdown.heading_texts inner) acc),
                block_list _ _ items =>
                    Markdown.heading_texts_rev rest
                        (Markdown.rev_onto (Markdown.item_texts items List.empty) acc),
                _ => Markdown.heading_texts_rev rest acc
            }
    }

#[partial]
def Markdown.item_texts (items : List Markdown.ListItem) (acc : List String) : List String :=
    match items {
        List.empty => List.reverse acc,
        List.cons item rest =>
            Markdown.item_texts rest (Markdown.rev_onto (Markdown.heading_texts item.blocks) acc)
    }

/// Prepend `xs` (in order) to a reversed accumulator.
#[partial]
def Markdown.rev_onto (xs : List String) (acc : List String) : List String :=
    match xs {
        List.empty => acc,
        List.cons x rest => Markdown.rev_onto rest (List.cons x acc)
    }

pub def Markdown.plain_of (inlines : List Markdown.Inline) : String :=
    Markdown.flatten_alt inlines List.empty

/// One id per heading, in document order, deduplicated and prefixed. Empty
/// unless `heading_ids` is on.
pub def Markdown.heading_ids (opts : Markdown.HtmlOptions) (texts : List String) : List String :=
    if opts.heading_ids
    then Markdown.heading_ids_go opts texts List.empty List.empty
    else List.empty

#[partial]
def Markdown.heading_ids_go
    (opts : Markdown.HtmlOptions) (texts : List String) (taken : List String) (acc : List String)
    : List String :=
    match texts {
        List.empty => List.reverse acc,
        List.cons text rest =>
            let base : String := String.concat opts.heading_id_prefix (Markdown.slug_of text) in
            let unique : String := Markdown.unique_slug base taken in
            Markdown.heading_ids_go opts rest (List.cons unique taken) (List.cons unique acc)
    }

// ─── Blocks ───
//
// Every walk threads the remaining heading ids, because a heading's id is its
// position in the document's heading sequence. `heading_ids` is empty unless
// the option is on, so nothing changes for the default.

def Markdown.take_id (opts : Markdown.HtmlOptions) (ids : List String) : Markdown.HeadingId :=
    let attrs : List Html.Attr :=
        match ids {
            List.cons id _ => if opts.heading_ids then List.cons (Markdown.at "id" id) List.empty else List.empty,
            List.empty => List.empty
        } in
    let rest : List String :=
        match ids {
            List.cons _ more => more,
            List.empty => List.empty
        } in
    let taken : Markdown.HeadingId := { attrs := attrs, rest := rest } in taken

struct Markdown.HeadingId {
    attrs : List Html.Attr,
    rest : List String
}

#[partial]
def Markdown.block_nodes
    (opts : Markdown.HtmlOptions) (ids : List String) (b : Markdown.Block)
    : Pair (List Html.Node) (List String) :=
    match b {
        block_paragraph inlines =>
            Pair.pair [Markdown.el "p" List.empty (Markdown.inline_nodes opts inlines), Markdown.txt "\n"] ids,
        block_heading level inlines =>
            let taken : Markdown.HeadingId := Markdown.take_id opts ids in
            Pair.pair
                [ Markdown.el (String.concat "h" (I64.to_string level)) taken.attrs
                    (Markdown.inline_nodes opts inlines),
                  Markdown.txt "\n" ]
                taken.rest,
        block_thematic_break => Pair.pair [Markdown.vo "hr" List.empty, Markdown.txt "\n"] ids,
        block_code_block info literal =>
            let attrs : List Html.Attr :=
                match info {
                    Option.some language =>
                        List.cons (Markdown.at "class"
                            (String.concat "language-" (Markdown.first_word_of language))) List.empty,
                    Option.none => List.empty
                } in
            Pair.pair
                [ Markdown.el "pre" List.empty
                    [Markdown.el "code" attrs [Markdown.txt literal]],
                  Markdown.txt "\n" ]
                ids,
        block_html_block literal =>
            Pair.pair
                (if opts.allow_raw_html
                 then [Html.Node.node_raw_html literal, Markdown.txt "\n"]
                 else [Markdown.txt literal, Markdown.txt "\n"])
                ids,
        block_quote blocks =>
            match Markdown.blocks_nodes opts ids blocks {
                Pair.pair inner ids2 =>
                    Pair.pair
                        [ Markdown.el "blockquote" List.empty
                            (List.cons (Markdown.txt "\n") inner),
                          Markdown.txt "\n" ]
                        ids2
            },
        block_list kind tight items =>
            match Markdown.items_nodes opts ids tight items {
                Pair.pair inner ids2 =>
                    Pair.pair
                        [ Markdown.el (Markdown.list_tag kind) (Markdown.list_attrs kind)
                            (List.cons (Markdown.txt "\n") inner),
                          Markdown.txt "\n" ]
                        ids2
            },
        block_table aligns head rows =>
            Pair.pair
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
                ids
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
def Markdown.blocks_nodes
    (opts : Markdown.HtmlOptions) (ids : List String) (blocks : List Markdown.Block)
    : Pair (List Html.Node) (List String) :=
    match Markdown.blocks_nodes_rev opts ids blocks List.empty {
        Pair.pair nodes ids2 => Pair.pair (List.reverse nodes) ids2
    }

#[partial]
def Markdown.blocks_nodes_rev
    (opts : Markdown.HtmlOptions) (ids : List String) (blocks : List Markdown.Block)
    (acc : List Html.Node) : Pair (List Html.Node) (List String) :=
    match blocks {
        List.empty => Pair.pair acc ids,
        List.cons b rest =>
            match Markdown.block_nodes opts ids b {
                Pair.pair nodes ids2 =>
                    Markdown.blocks_nodes_rev opts ids2 rest (Markdown.nodes_rev nodes acc)
            }
    }

#[partial]
def Markdown.items_nodes
    (opts : Markdown.HtmlOptions) (ids : List String) (tight : Bool) (items : List Markdown.ListItem)
    : Pair (List Html.Node) (List String) :=
    match Markdown.items_nodes_rev opts ids tight items List.empty {
        Pair.pair nodes ids2 => Pair.pair (List.reverse nodes) ids2
    }

#[partial]
def Markdown.items_nodes_rev
    (opts : Markdown.HtmlOptions) (ids : List String) (tight : Bool) (items : List Markdown.ListItem)
    (acc : List Html.Node) : Pair (List Html.Node) (List String) :=
    match items {
        List.empty => Pair.pair acc ids,
        List.cons item rest =>
            match Markdown.item_node opts ids tight item {
                Pair.pair node ids2 =>
                    let nodes : List Html.Node :=
                        List.cons node (List.cons (Markdown.txt "\n") List.empty) in
                    Markdown.items_nodes_rev opts ids2 tight rest (Markdown.nodes_rev nodes acc)
            }
    }

#[partial]
def Markdown.item_node
    (opts : Markdown.HtmlOptions) (ids : List String) (tight : Bool) (item : Markdown.ListItem)
    : Pair Html.Node (List String) :=
    match Markdown.item_children opts ids tight item {
        Pair.pair children ids2 => Pair.pair (Markdown.el "li" List.empty children) ids2
    }

/// A task-list item's checkbox and its following space are the first thing in
/// the item's first paragraph, so a loose item opens `<p><input … /> text`,
/// which is the shape cmark-gfm emits.
def Markdown.checkbox_prefix (checked : Option Bool) : List Html.Node :=
    match checked {
        Option.none => List.empty,
        Option.some state =>
            List.cons (Markdown.checkbox state) (List.cons (Markdown.txt " ") List.empty)
    }

def Markdown.checkbox (state : Bool) : Html.Node :=
    let attrs : List Html.Attr :=
        if state
        then [ Markdown.at "type" "checkbox", Markdown.at "checked" "", Markdown.at "disabled" "" ]
        else [ Markdown.at "type" "checkbox", Markdown.at "disabled" "" ] in
    Html.Node.node_void "input" attrs

/// cmark's `cr()`: a block child starts on its own line, so a loose item opens
/// with a newline and a tight item puts one before any non-paragraph child.
#[partial]
def Markdown.item_children
    (opts : Markdown.HtmlOptions) (ids : List String) (tight : Bool) (item : Markdown.ListItem)
    : Pair (List Html.Node) (List String) :=
    let blocks : List Markdown.Block := item.blocks in
    if List.is_empty blocks
    then Pair.pair List.empty ids
    else
        let prefix : List Html.Node := Markdown.checkbox_prefix item.checked in
        match blocks {
            List.cons first rest =>
                if tight
                then
                    match Markdown.tight_block_nodes opts ids prefix first {
                        Pair.pair head ids2 =>
                            match Markdown.tight_children opts ids2 rest {
                                Pair.pair tail ids3 =>
                                    Pair.pair (List.append head tail) ids3
                            }
                    }
                else
                    match Markdown.block_nodes_prefixed opts ids prefix first {
                        Pair.pair head ids2 =>
                            match Markdown.blocks_nodes opts ids2 rest {
                                Pair.pair tail ids3 =>
                                    Pair.pair
                                        (List.append
                                            (List.cons (Markdown.txt "\n") head) tail)
                                        ids3
                            }
                    },
            List.empty => Pair.pair List.empty ids
        }

/// A paragraph takes the prefix INSIDE its `<p>`; any other block puts it in
/// front.
#[partial]
def Markdown.block_nodes_prefixed
    (opts : Markdown.HtmlOptions) (ids : List String) (prefix : List Html.Node) (b : Markdown.Block)
    : Pair (List Html.Node) (List String) :=
    match b {
        block_paragraph inlines =>
            Pair.pair
                (List.cons (Markdown.el "p" List.empty
                        (List.append prefix (Markdown.inline_nodes opts inlines)))
                    (List.cons (Markdown.txt "\n") List.empty))
                ids,
        _ =>
            match Markdown.block_nodes opts ids b {
                Pair.pair nodes ids2 => Pair.pair (List.append prefix nodes) ids2
            }
    }

/// The tight-item variant: no `<p>` wrapper, and a non-paragraph block keeps
/// cmark's newline because the prefix ends on the `<li>` line.
#[partial]
def Markdown.tight_block_nodes
    (opts : Markdown.HtmlOptions) (ids : List String) (prefix : List Html.Node) (b : Markdown.Block)
    : Pair (List Html.Node) (List String) :=
    match b {
        block_paragraph inlines => Pair.pair (List.append prefix (Markdown.inline_nodes opts inlines)) ids,
        _ =>
            match Markdown.block_nodes opts ids b {
                Pair.pair nodes ids2 =>
                    Pair.pair (List.append prefix (List.cons (Markdown.txt "\n") nodes)) ids2
            }
    }

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
def Markdown.tight_children
    (opts : Markdown.HtmlOptions) (ids : List String) (blocks : List Markdown.Block)
    : Pair (List Html.Node) (List String) :=
    match Markdown.tight_children_rev opts ids blocks List.empty {
        Pair.pair nodes ids2 => Pair.pair (List.reverse nodes) ids2
    }

#[partial]
def Markdown.tight_children_rev
    (opts : Markdown.HtmlOptions) (ids : List String) (blocks : List Markdown.Block)
    (acc : List Html.Node) : Pair (List Html.Node) (List String) :=
    match blocks {
        List.empty => Pair.pair acc ids,
        List.cons b rest =>
            let newline : Bool := Bool.not (Markdown.at_line_start acc) in
            match b {
                block_paragraph inlines =>
                    Markdown.tight_children_rev opts ids rest
                        (Markdown.nodes_rev (Markdown.inline_nodes opts inlines) acc),
                _ =>
                    match Markdown.block_nodes opts ids b {
                        Pair.pair nodes ids2 =>
                            let nodes2 : List Html.Node :=
                                if newline
                                then List.cons (Markdown.txt "\n") nodes
                                else nodes in
                            Markdown.tight_children_rev opts ids2 rest (Markdown.nodes_rev nodes2 acc)
                    }
            }
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
    let ids : List String := Markdown.heading_ids opts (Markdown.heading_texts doc.blocks) in
    match Markdown.blocks_nodes opts ids doc.blocks {
        Pair.pair nodes _ => nodes
    }

pub def Markdown.to_html_with (opts : Markdown.HtmlOptions) (doc : Markdown.Document) : Html.Node :=
    Html.Node.node_fragment (Markdown.to_html_nodes_with opts doc)

pub def Markdown.to_html_nodes (doc : Markdown.Document) : List Html.Node :=
    Markdown.to_html_nodes_with Markdown.default_html_options doc

pub def Markdown.to_html (doc : Markdown.Document) : Html.Node :=
    Html.Node.node_fragment (Markdown.to_html_nodes doc)
