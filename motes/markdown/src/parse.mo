/// The parser entry points: frontmatter splitting, the block pass, and the
/// resolve pass that turns raw blocks into the public AST.
///
/// The contract is total. CommonMark has no invalid input, so there is no
/// `Result` and no failure branch: pathological nesting degrades to literal
/// text at `Options.max_depth` instead of erroring.
use init::string {}
use lib::options {Markdown.Options, Markdown.default_options}
use lib::scan {Markdown.split_lines}
use lib::block {
    Markdown.block_parse, Markdown.join_plain, Markdown.trim_end,
}
use lib::inline {Markdown.inline_parse_opts}
use lib::refs {Markdown.collect_refs}
use lib::types {
    Markdown.Block, Markdown.Document, Markdown.FrontFormat, Markdown.FrontSplit,
    Markdown.Frontmatter, Markdown.Inline, Markdown.LinkRef, Markdown.ListItem,
    Markdown.RawBlock, Markdown.RawItem,
    Markdown.TableRow,
}

open Markdown.Block {
    block_paragraph, block_heading, block_thematic_break, block_code_block,
    block_quote, block_list, block_table, block_html_block,
}
open Markdown.RawBlock {
    raw_paragraph, raw_heading, raw_thematic_break, raw_code_block,
    raw_block_quote, raw_list, raw_table, raw_html_block,
}

// ─── Frontmatter ───

def Markdown.delimiter_of (format : Markdown.FrontFormat) : String :=
    match format {
        Markdown.FrontFormat.front_yaml => "---",
        Markdown.FrontFormat.front_toml => "+++"
    }

def Markdown.mk_front_split (front : Option Markdown.Frontmatter) (body : String) : Markdown.FrontSplit :=
    let s : Markdown.FrontSplit := { front := front, body := body } in s

def Markdown.mk_frontmatter (format : Markdown.FrontFormat) (literal : String) : Markdown.Frontmatter :=
    let f : Markdown.Frontmatter := { format := format, literal := literal } in f

/// Walk the lines after the opening delimiter for the closing one.
#[partial]
def Markdown.split_on_delim
    (format : Markdown.FrontFormat) (src : String) (lines : List String)
    (acc : List String) : Markdown.FrontSplit :=
    let delim : String := Markdown.delimiter_of format in
    match lines {
        List.empty => Markdown.mk_front_split Option.none src,
        List.cons line rest =>
            if String.beq line delim
            then
                Markdown.mk_front_split
                    (Option.some (Markdown.mk_frontmatter format (Markdown.join_plain (List.reverse acc))))
                    (Markdown.join_plain rest)
            else Markdown.split_on_delim format src rest (List.cons line acc)
    }

/// Split `---` (YAML) or `+++` (TOML) frontmatter off the head of `src`.
///
/// Only a delimiter at the very start counts, and without a closing delimiter
/// the input is ordinary Markdown -- a leading `---` is then a thematic break
/// or a setext underline, never a swallowed document. The body is the
/// remaining lines joined with `\n` (a final newline is dropped, which does
/// not change the parse).
pub def Markdown.split_frontmatter (src : String) : Markdown.FrontSplit :=
    match Markdown.split_lines src {
        List.empty => Markdown.mk_front_split Option.none src,
        List.cons first rest =>
            if String.beq first "---"
            then Markdown.split_on_delim Markdown.FrontFormat.front_yaml src rest List.empty
            else if String.beq first "+++"
            then Markdown.split_on_delim Markdown.FrontFormat.front_toml src rest List.empty
            else Markdown.mk_front_split Option.none src
    }

// ─── Resolve: raw blocks to the public AST ───

pub def Markdown.inline_of_lines
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (lines : List String) : List Markdown.Inline :=
    Markdown.inline_parse_opts opts refs (Markdown.trim_end (Markdown.join_plain lines))

#[partial]
pub def Markdown.resolve_block (opts : Markdown.Options) (refs : List Markdown.LinkRef) (b : Markdown.RawBlock) : Markdown.Block :=
    match b {
        raw_paragraph lines => block_paragraph (Markdown.inline_of_lines opts refs lines),
        raw_heading level _ lines => block_heading level (Markdown.inline_of_lines opts refs lines),
        raw_thematic_break => block_thematic_break,
        raw_code_block info literal => block_code_block info literal,
        raw_block_quote blocks => block_quote (Markdown.resolve_blocks opts refs blocks),
        raw_list kind tight items => block_list kind tight (Markdown.resolve_items opts refs items),
        raw_table aligns head rows =>
            block_table aligns (Markdown.resolve_row opts refs head) (Markdown.resolve_rows opts refs rows),
        raw_html_block literal => block_html_block literal
    }

#[partial]
pub def Markdown.resolve_blocks
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (blocks : List Markdown.RawBlock)
    : List Markdown.Block :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest =>
            List.cons (Markdown.resolve_block opts refs b) (Markdown.resolve_blocks opts refs rest)
    }

#[partial]
def Markdown.resolve_item
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (item : Markdown.RawItem) : Markdown.ListItem :=
    let blocks : List Markdown.Block := Markdown.resolve_blocks opts refs item.blocks in
    if opts.gfm_task_lists
    then Markdown.task_item blocks
    else Markdown.mk_item item.checked blocks

def Markdown.mk_item (checked : Option Bool) (blocks : List Markdown.Block) : Markdown.ListItem :=
    let i : Markdown.ListItem := { checked := checked, blocks := blocks } in i

/// A leading `[ ] ` or `[x] `/`[X] ` in an item's first paragraph is a task
/// marker: it sets `checked` and is removed from the text.
#[partial]
def Markdown.task_item (blocks : List Markdown.Block) : Markdown.ListItem :=
    match blocks {
        List.cons b rest =>
            match b {
                block_paragraph inlines => Markdown.task_paragraph inlines rest,
                _ => Markdown.mk_item Option.none blocks
            },
        List.empty => Markdown.mk_item Option.none blocks
    }

#[partial]
#[partial]
def Markdown.task_paragraph (inlines : List Markdown.Inline) (rest : List Markdown.Block) : Markdown.ListItem :=
    match inlines {
        List.cons first more =>
            match first {
                inline_text t =>
                    match Markdown.task_marker t {
                        Option.some checked => Markdown.mk_item (Option.some checked) (Markdown.task_rest checked t more rest),
                        Option.none => Markdown.mk_item Option.none (List.cons (block_paragraph inlines) rest)
                    },
                _ => Markdown.mk_item Option.none (List.cons (block_paragraph inlines) rest)
            },
        List.empty => Markdown.mk_item Option.none (List.cons (block_paragraph inlines) rest)
    }

/// The marker is `[ ]`, `[x]` or `[X]` followed by a space.
def Markdown.task_marker (t : String) : Option Bool :=
    if String.starts_with "[ ] " t then Option.some false
    else if String.starts_with "[x] " t then Option.some true
    else if String.starts_with "[X] " t then Option.some true
    else Option.none

#[partial]
def Markdown.task_rest (checked : Bool) (t : String) (more : List Markdown.Inline) (rest : List Markdown.Block) : List Markdown.Block :=
    let text : String := String.drop 4i64 t in
    let inlines : List Markdown.Inline :=
        if String.beq text ""
        then more
        else List.cons (Markdown.Inline.inline_text text) more in
    let para : Markdown.Block := block_paragraph inlines in
    let blocks : List Markdown.Block :=
        if List.is_empty inlines then rest else List.cons para rest in
    blocks

#[partial]
def Markdown.resolve_items
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (items : List Markdown.RawItem)
    : List Markdown.ListItem :=
    match items {
        List.empty => List.empty,
        List.cons i rest =>
            List.cons (Markdown.resolve_item opts refs i) (Markdown.resolve_items opts refs rest)
    }

def Markdown.resolve_row (opts : Markdown.Options) (refs : List Markdown.LinkRef) (cells : List String) : Markdown.TableRow :=
    let row : Markdown.TableRow := { cells := Markdown.resolve_cells opts refs cells } in row

#[partial]
def Markdown.resolve_cells
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (cells : List String)
    : List (List Markdown.Inline) :=
    match cells {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (Markdown.inline_parse_opts opts refs (Markdown.trim_end c))
                (Markdown.resolve_cells opts refs rest)
    }

#[partial]
def Markdown.resolve_rows
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (rows : List (List String))
    : List Markdown.TableRow :=
    match rows {
        List.empty => List.empty,
        List.cons r rest => List.cons (Markdown.resolve_row opts refs r) (Markdown.resolve_rows opts refs rest)
    }

// ─── Entry points ───

pub def Markdown.parse_with (opts : Markdown.Options) (src : String) : Markdown.Document :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter src in
    let front : Option Markdown.Frontmatter :=
        if opts.frontmatter then split.front else Option.none in
    let body : String := if opts.frontmatter then split.body else src in
    let raw : List Markdown.RawBlock := Markdown.block_parse opts (Markdown.split_lines body) in
    let collected : Pair (List Markdown.LinkRef) (List Markdown.RawBlock) := Markdown.collect_refs raw in
    let blocks : List Markdown.Block :=
        match collected {
            Pair.pair refs rewritten => Markdown.resolve_blocks opts refs rewritten
        } in
    let doc : Markdown.Document := { front := front, blocks := blocks } in doc

/// Parse with the GFM-on defaults.
pub def Markdown.parse (src : String) : Markdown.Document :=
    Markdown.parse_with Markdown.default_options src
