/// The styled-text renderer: the parser's AST to renderer-neutral
/// `StyledLine`s.
///
/// The styles are SEMANTIC, not colors: `span_code` says "this is code",
/// and the consumer (weaver's theme) decides the color. That keeps this
/// mote tui-free, so a web or dump renderer can map the same lines
/// differently. `to_plain_lines` flattens the same output for persistence
/// and copy paths, which must never carry ANSI or markup.
///
/// The parser is total, so this renderer is too: any malformed Markdown
/// is already literal text by the time it arrives.
use init::string {}
use lib::scan {Markdown.split_lines}
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

// ─── The output types ───────────────────────────────────────────────────

/// A span's semantic role. `span_heading` keeps the level so a consumer
/// can choose weight or an indent; the marker characters themselves are
/// not emitted.
pub type Markdown.SpanStyle {
    span_plain,
    span_heading (level : I64),
    span_emphasis,
    span_strong,
    span_strong_emphasis,
    span_strikethrough,
    span_code,
    span_link,
    span_quote,
    span_list_marker,
    span_table_head,
    span_table_border,
    span_rule,
}

pub struct Markdown.StyledSpan {
    text : String,
    style : Markdown.SpanStyle,
}

pub struct Markdown.StyledLine {
    spans : List Markdown.StyledSpan,
}

pub def Markdown.span (text : String) (style : Markdown.SpanStyle) : Markdown.StyledSpan :=
    let r : Markdown.StyledSpan := { text := text, style := style } in
    r

pub def Markdown.line (spans : List Markdown.StyledSpan) : Markdown.StyledLine :=
    let r : Markdown.StyledLine := { spans := spans } in
    r

/// A line's text with all styling flattened.
#[partial]
pub def Markdown.line_text (l : Markdown.StyledLine) : String :=
    String.concat_all (List.map (fn (s : Markdown.StyledSpan) => s.text) l.spans)

/// Stable names for goldens and debugging.
pub def Markdown.style_name (s : Markdown.SpanStyle) : String :=
    match s {
        Markdown.SpanStyle.span_plain => "plain",
        Markdown.SpanStyle.span_heading _ => "heading",
        Markdown.SpanStyle.span_emphasis => "emphasis",
        Markdown.SpanStyle.span_strong => "strong",
        Markdown.SpanStyle.span_strong_emphasis => "strong_emphasis",
        Markdown.SpanStyle.span_strikethrough => "strikethrough",
        Markdown.SpanStyle.span_code => "code",
        Markdown.SpanStyle.span_link => "link",
        Markdown.SpanStyle.span_quote => "quote",
        Markdown.SpanStyle.span_list_marker => "list_marker",
        Markdown.SpanStyle.span_table_head => "table_head",
        Markdown.SpanStyle.span_table_border => "table_border",
        Markdown.SpanStyle.span_rule => "rule",
    }

// ─── Inline inlines ─────────────────────────────────────────────────────

/// Flatten to plain text without pulling in the HTML renderer.
#[partial]
def Markdown.inlines_plain (inls : List Markdown.Inline) : String :=
    match inls {
        List.empty => "",
        List.cons i rest => String.concat (Markdown.inline_plain i) (Markdown.inlines_plain rest),
    }

def Markdown.inline_plain (i : Markdown.Inline) : String :=
    match i {
        inline_text t => t,
        inline_soft_break => " ",
        inline_hard_break => "\n",
        inline_emphasis c => Markdown.inlines_plain c,
        inline_strong c => Markdown.inlines_plain c,
        inline_strikethrough c => Markdown.inlines_plain c,
        inline_code t => t,
        inline_link _ _ c => Markdown.inlines_plain c,
        inline_image _ _ alt => alt,
        inline_autolink _ l => l,
        inline_html l => l,
    }

/// Nesting emphasis under strong (or the reverse) keeps both.
def Markdown.emphasis_under (s : Markdown.SpanStyle) : Markdown.SpanStyle :=
    match s {
        Markdown.SpanStyle.span_strong => Markdown.SpanStyle.span_strong_emphasis,
        Markdown.SpanStyle.span_strong_emphasis => Markdown.SpanStyle.span_strong_emphasis,
        _ => Markdown.SpanStyle.span_emphasis,
    }

def Markdown.strong_under (s : Markdown.SpanStyle) : Markdown.SpanStyle :=
    match s {
        Markdown.SpanStyle.span_emphasis => Markdown.SpanStyle.span_strong_emphasis,
        Markdown.SpanStyle.span_strong_emphasis => Markdown.SpanStyle.span_strong_emphasis,
        _ => Markdown.SpanStyle.span_strong,
    }

/// The destination after a link label, when it says something the label
/// does not already say.
def Markdown.link_tail (dest : String) (children : List Markdown.Inline) : List Markdown.StyledSpan :=
    let label : String := Markdown.inlines_plain children in
    if Bool.or (String.is_empty dest) (String.beq dest label)
    then List.empty
    else List.cons (Markdown.span (String.concat " <" (String.concat dest ">")) Markdown.SpanStyle.span_link) List.empty

def Markdown.autolink_spans (dest : String) (label : String) : List Markdown.StyledSpan :=
    if String.beq dest label
    then List.cons (Markdown.span label Markdown.SpanStyle.span_link) List.empty
    else Markdown.link_tail dest List.empty

#[partial]
def Markdown.inline_spans (inls : List Markdown.Inline) (style : Markdown.SpanStyle) : List Markdown.StyledSpan :=
    match inls {
        List.empty => List.empty,
        List.cons i rest =>
            List.append (Markdown.inline_span i style) (Markdown.inline_spans rest style),
    }

def Markdown.inline_span (i : Markdown.Inline) (style : Markdown.SpanStyle) : List Markdown.StyledSpan :=
    match i {
        inline_text t => List.cons (Markdown.span t style) List.empty,
        inline_soft_break => List.cons (Markdown.span "\n" style) List.empty,
        inline_hard_break => List.cons (Markdown.span "\n" style) List.empty,
        inline_emphasis c => Markdown.inline_spans c (Markdown.emphasis_under style),
        inline_strong c => Markdown.inline_spans c (Markdown.strong_under style),
        inline_strikethrough c => Markdown.inline_spans c Markdown.SpanStyle.span_strikethrough,
        inline_code t => List.cons (Markdown.span t Markdown.SpanStyle.span_code) List.empty,
        inline_link dest _ children =>
            List.append (Markdown.inline_spans children Markdown.SpanStyle.span_link) (Markdown.link_tail dest children),
        inline_image dest _ alt =>
            List.append
                (List.cons (Markdown.span alt Markdown.SpanStyle.span_plain) List.empty)
                (List.cons (Markdown.span (String.concat " <" (String.concat dest ">")) Markdown.SpanStyle.span_plain) List.empty),
        inline_autolink dest label => Markdown.autolink_spans dest label,
        inline_html l => List.cons (Markdown.span l Markdown.SpanStyle.span_plain) List.empty,
    }

// ─── Line assembly ─────────────────────────────────────────────────────

#[terminating]
def Markdown.indent_spans (n : I64) : List Markdown.StyledSpan :=
    if n < 1 then List.empty
    else List.cons (Markdown.span " " Markdown.SpanStyle.span_plain) (Markdown.indent_spans (n - 1))

def Markdown.trim_cr (s : String) : String :=
    let n : I64 := String.length s in
    if I64.lt 0 n
    then (if String.beq (String.slice s (n - 1) 1) "\r" then String.slice s 0 (n - 1) else s)
    else s

/// Split on `\n`, preserving empty lines: `"\n"` is two empty parts, so a
/// hard break really starts a new line. `Markdown.split_lines` drops the
/// final empty line (right for source lines, wrong for span text).
#[partial]
def Markdown.split_newlines_go (s : String) (start : I64) (i : I64) (acc : List String) : List String :=
    let n : I64 := String.length s in
    if I64.lt n (i + 1)
    then List.reverse (List.cons (String.slice s start (n - start)) acc)
    else if String.beq (String.slice s i 1) "\n"
    then Markdown.split_newlines_go s (i + 1) (i + 1)
            (List.cons (Markdown.trim_cr (String.slice s start (i - start))) acc)
    else Markdown.split_newlines_go s start (i + 1) acc

pub def Markdown.split_newlines (s : String) : List String :=
    if String.is_empty s then List.cons "" List.empty
    else Markdown.split_newlines_go s 0 0 List.empty

/// One span's text split at newlines. An empty text contributes one empty
/// part so an empty span still occupies a position in the line.
def Markdown.span_parts (text : String) : List String :=
    Markdown.split_newlines text

/// Fold spans into lines, splitting at embedded newlines.
#[partial]
def Markdown.split_lines_spans
    (spans : List Markdown.StyledSpan)
    (cur : List Markdown.StyledSpan)
    (done : List (List Markdown.StyledSpan)) : List (List Markdown.StyledSpan) :=
    match spans {
        List.empty => List.reverse (List.cons cur done),
        List.cons s rest =>
            let parts : List String := Markdown.span_parts s.text in
            let first : String := Markdown.first_part parts in
            let cur2 : List Markdown.StyledSpan := List.append cur (List.cons (Markdown.span first s.style) List.empty) in
            Markdown.split_lines_more rest (Markdown.tail_parts parts) cur2 done s.style,
    }

def Markdown.first_part (parts : List String) : String :=
    match parts { List.empty => "", List.cons p _ => p }

#[partial]
def Markdown.tail_parts (parts : List String) : List String :=
    match parts { List.empty => List.empty, List.cons _ rest => rest }

/// Consume the parts after the first: each starts a new line.
#[partial]
def Markdown.split_lines_more
    (spans : List Markdown.StyledSpan) (parts : List String)
    (cur : List Markdown.StyledSpan) (done : List (List Markdown.StyledSpan))
    (style : Markdown.SpanStyle) : List (List Markdown.StyledSpan) :=
    match parts {
        List.empty => Markdown.split_lines_spans spans cur done,
        List.cons p rest =>
            let done2 : List (List Markdown.StyledSpan) := List.cons cur done in
            let next : List Markdown.StyledSpan := List.cons (Markdown.span p style) List.empty in
            Markdown.split_lines_more spans rest next done2 style,
    }

/// Prefix every line with `indent` spaces and `prefix` spans.
#[partial]
def Markdown.prefix_lines
    (indent : I64) (prefix : List Markdown.StyledSpan)
    (lines : List (List Markdown.StyledSpan)) : List Markdown.StyledLine :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            let pre : List Markdown.StyledSpan := List.append (Markdown.indent_spans indent) prefix in
            List.cons (Markdown.line (List.append pre l)) (Markdown.prefix_lines indent prefix rest),
    }

def Markdown.block_spans
    (indent : I64) (prefix : List Markdown.StyledSpan) (spans : List Markdown.StyledSpan)
    : List Markdown.StyledLine :=
    Markdown.prefix_lines indent prefix (Markdown.split_lines_spans spans List.empty List.empty)

// ─── Blocks ────────────────────────────────────────────────────────────

#[partial]
def Markdown.blocks_lines
    (blocks : List Markdown.Block) (indent : I64) (prefix : List Markdown.StyledSpan)
    : List Markdown.StyledLine :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest =>
            List.append (Markdown.block_lines b indent prefix) (Markdown.blocks_lines rest indent prefix),
    }

def Markdown.block_lines
    (b : Markdown.Block) (indent : I64) (prefix : List Markdown.StyledSpan)
    : List Markdown.StyledLine :=
    match b {
        block_paragraph inls =>
            Markdown.block_spans indent prefix (Markdown.inline_spans inls Markdown.SpanStyle.span_plain),
        block_heading level inls =>
            Markdown.block_spans indent prefix (Markdown.inline_spans inls (Markdown.SpanStyle.span_heading level)),
        block_thematic_break =>
            List.cons (Markdown.line (List.append (Markdown.indent_spans indent)
                (List.append prefix (List.cons (Markdown.span (String.repeat "─" 40) Markdown.SpanStyle.span_rule) List.empty)))) List.empty,
        block_code_block _info literal =>
            Markdown.code_lines literal indent prefix,
        block_quote inner =>
            Markdown.blocks_lines inner indent
                (List.append prefix (List.cons (Markdown.span "│ " Markdown.SpanStyle.span_quote) List.empty)),
        block_list kind tight items =>
            Markdown.list_lines kind tight items 0 indent prefix,
        block_table aligns head rows =>
            Markdown.table_lines aligns head rows indent prefix,
        block_html_block literal =>
            Markdown.html_lines literal indent prefix,
    }

#[partial]
def Markdown.code_lines
    (literal : String) (indent : I64) (prefix : List Markdown.StyledSpan) : List Markdown.StyledLine :=
    if String.is_empty (String.trim literal)
    then List.empty
    else Markdown.code_line_list (Markdown.split_lines literal) indent prefix

/// `literal` is split ONCE; the recursion walks the lines, not the text
/// (passing a `List String` where a `String` was expected is a check
/// error the best-effort elaborator can swallow -- it compiled and then
/// recursed until the GC stack overflowed).
#[partial]
def Markdown.code_line_list
    (lines : List String) (indent : I64) (prefix : List Markdown.StyledSpan) : List Markdown.StyledLine :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            let spans : List Markdown.StyledSpan :=
                List.append (Markdown.indent_spans indent)
                    (List.append prefix
                        (List.cons (Markdown.span (String.concat "  " l) Markdown.SpanStyle.span_code) List.empty)) in
            List.cons (Markdown.line spans) (Markdown.code_line_list rest indent prefix),
    }

#[partial]
def Markdown.html_lines
    (literal : String) (indent : I64) (prefix : List Markdown.StyledSpan) : List Markdown.StyledLine :=
    Markdown.html_line_list (Markdown.split_lines literal) indent prefix

#[partial]
def Markdown.html_line_list
    (lines : List String) (indent : I64) (prefix : List Markdown.StyledSpan) : List Markdown.StyledLine :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            List.append
                (Markdown.block_spans indent prefix (List.cons (Markdown.span l Markdown.SpanStyle.span_plain) List.empty))
                (Markdown.html_line_list rest indent prefix),
    }

def Markdown.list_marker (kind : Markdown.ListKind) (index : I64) (checked : Option Bool) : String :=
    match checked {
        Option.some true => "[x] ",
        Option.some false => "[ ] ",
        Option.none =>
            match kind {
                list_bullet _ => "• ",
                list_ordered start _ =>
                    String.concat (I64.to_string (start + index)) ". ",
            },
    }

/// An ordered/bullet item: the marker prefixes the first rendered line;
/// every further line is indented under it. The item's blocks are rendered
/// with no indent so the marker controls the first line.
#[partial]
def Markdown.list_lines
    (kind : Markdown.ListKind) (tight : Bool) (items : List Markdown.ListItem)
    (index : I64) (indent : I64) (prefix : List Markdown.StyledSpan)
    : List Markdown.StyledLine :=
    match items {
        List.empty => List.empty,
        List.cons item rest =>
            let marker : Markdown.StyledSpan :=
                Markdown.span (Markdown.list_marker kind index item.checked) Markdown.SpanStyle.span_list_marker in
            let first_prefix : List Markdown.StyledSpan :=
                List.append (Markdown.indent_spans indent)
                    (List.append prefix (List.cons marker List.empty)) in
            let rest_prefix : List Markdown.StyledSpan := Markdown.indent_spans (indent + 2) in
            let inner : List Markdown.StyledLine :=
                Markdown.blocks_lines item.blocks 0 List.empty in
            List.append (Markdown.mark_item first_prefix rest_prefix inner)
                (Markdown.list_lines kind tight rest (index + 1) indent prefix),
    }

/// Put `first_prefix` on the first line and `rest_prefix` on the others.
def Markdown.mark_item
    (first_prefix : List Markdown.StyledSpan) (rest_prefix : List Markdown.StyledSpan)
    (lines : List Markdown.StyledLine) : List Markdown.StyledLine :=
    match lines {
        List.empty => List.cons (Markdown.line first_prefix) List.empty,
        List.cons l rest =>
            List.cons (Markdown.line (List.append first_prefix l.spans))
                (List.map (fn (r : Markdown.StyledLine) => Markdown.line (List.append rest_prefix r.spans)) rest),
    }

#[partial]
def Markdown.table_cell_spans
    (cells : List (List Markdown.Inline)) (style : Markdown.SpanStyle) : List Markdown.StyledSpan :=
    match cells {
        List.empty => List.empty,
        List.cons c rest =>
            let here : List Markdown.StyledSpan := Markdown.inline_spans c style in
            match rest {
                List.empty => here,
                List.cons _ _ =>
                    List.append here
                        (List.append (List.cons (Markdown.span " │ " Markdown.SpanStyle.span_table_border) List.empty)
                            (Markdown.table_cell_spans rest style)),
            },
    }

def Markdown.table_row_spans (row : Markdown.TableRow) (style : Markdown.SpanStyle) : List Markdown.StyledSpan :=
    List.append (List.cons (Markdown.span "│ " Markdown.SpanStyle.span_table_border) List.empty)
        (List.append (Markdown.table_cell_spans row.cells style)
            (List.cons (Markdown.span " │" Markdown.SpanStyle.span_table_border) List.empty))

#[partial]
def Markdown.table_rows
    (rows : List Markdown.TableRow) (indent : I64) (prefix : List Markdown.StyledSpan)
    : List Markdown.StyledLine :=
    match rows {
        List.empty => List.empty,
        List.cons r rest =>
            List.cons (Markdown.line (List.append (Markdown.indent_spans indent)
                (List.append prefix (Markdown.table_row_spans r Markdown.SpanStyle.span_plain))))
                (Markdown.table_rows rest indent prefix),
    }

def Markdown.table_lines
    (aligns : List Markdown.Align) (head : Markdown.TableRow) (rows : List Markdown.TableRow)
    (indent : I64) (prefix : List Markdown.StyledSpan) : List Markdown.StyledLine :=
    let head_line : List Markdown.StyledLine :=
        List.cons (Markdown.line (List.append (Markdown.indent_spans indent)
            (List.append prefix (Markdown.table_row_spans head Markdown.SpanStyle.span_table_head)))) List.empty in
    let rule : Markdown.StyledLine :=
        Markdown.line (List.append (Markdown.indent_spans indent)
            (List.append prefix (List.cons (Markdown.span (String.repeat "─" 40) Markdown.SpanStyle.span_table_border) List.empty))) in
    List.append head_line (List.cons rule (Markdown.table_rows rows indent prefix))

// ─── Entry points ──────────────────────────────────────────────────────

pub def Markdown.to_lines (doc : Markdown.Document) : List Markdown.StyledLine :=
    Markdown.blocks_lines doc.blocks 0 List.empty

pub def Markdown.to_plain_lines (doc : Markdown.Document) : List String :=
    List.map Markdown.line_text (Markdown.to_lines doc)
