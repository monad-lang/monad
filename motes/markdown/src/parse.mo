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
use lib::inline {Markdown.inline_parse}
use lib::types {
    Markdown.Block, Markdown.Document, Markdown.FrontFormat, Markdown.FrontSplit,
    Markdown.Frontmatter, Markdown.Inline, Markdown.ListItem, Markdown.RawBlock,
    Markdown.RawItem,
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

pub def Markdown.inline_of_lines (lines : List String) : List Markdown.Inline :=
    Markdown.inline_parse (Markdown.trim_end (Markdown.join_plain lines))

#[partial]
pub def Markdown.resolve_block (b : Markdown.RawBlock) : Markdown.Block :=
    match b {
        raw_paragraph lines => block_paragraph (Markdown.inline_of_lines lines),
        raw_heading level lines => block_heading level (Markdown.inline_of_lines lines),
        raw_thematic_break => block_thematic_break,
        raw_code_block info literal => block_code_block info literal,
        raw_block_quote blocks => block_quote (Markdown.resolve_blocks blocks),
        raw_list kind tight items => block_list kind tight (Markdown.resolve_items items),
        raw_table aligns head rows => block_table aligns (Markdown.resolve_row head) (Markdown.resolve_rows rows),
        raw_html_block literal => block_html_block literal
    }

#[partial]
pub def Markdown.resolve_blocks (blocks : List Markdown.RawBlock) : List Markdown.Block :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest => List.cons (Markdown.resolve_block b) (Markdown.resolve_blocks rest)
    }

def Markdown.resolve_item (item : Markdown.RawItem) : Markdown.ListItem :=
    let resolved : Markdown.ListItem :=
        { checked := item.checked, blocks := Markdown.resolve_blocks item.blocks } in
    resolved

#[partial]
def Markdown.resolve_items (items : List Markdown.RawItem) : List Markdown.ListItem :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.cons (Markdown.resolve_item i) (Markdown.resolve_items rest)
    }

def Markdown.resolve_row (cells : List String) : Markdown.TableRow :=
    let row : Markdown.TableRow := { cells := Markdown.resolve_cells cells } in row

#[partial]
def Markdown.resolve_cells (cells : List String) : List (List Markdown.Inline) :=
    match cells {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (Markdown.inline_parse (Markdown.trim_end c)) (Markdown.resolve_cells rest)
    }

#[partial]
def Markdown.resolve_rows (rows : List (List String)) : List Markdown.TableRow :=
    match rows {
        List.empty => List.empty,
        List.cons r rest => List.cons (Markdown.resolve_row r) (Markdown.resolve_rows rest)
    }

// ─── Entry points ───

pub def Markdown.parse_with (opts : Markdown.Options) (src : String) : Markdown.Document :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter src in
    let front : Option Markdown.Frontmatter :=
        if opts.frontmatter then split.front else Option.none in
    let body : String := if opts.frontmatter then split.body else src in
    let blocks : List Markdown.Block :=
        Markdown.resolve_blocks (Markdown.block_parse opts (Markdown.split_lines body)) in
    let doc : Markdown.Document := { front := front, blocks := blocks } in doc

/// Parse with the GFM-on defaults.
pub def Markdown.parse (src : String) : Markdown.Document :=
    Markdown.parse_with Markdown.default_options src
