/// Link reference definitions: extraction, normalisation and hoisting.
///
/// A definition is parsed from the START of a paragraph's text and removed
/// from it; definitions inside block quotes and list items are hoisted to
/// document scope, and the first definition for a normalized label wins.
use init::string {}
use parsec::core {is_empty}
use lib::link_syntax {
    Markdown.normalize_label, Markdown.parse_destination,
    Markdown.parse_ref_label, Markdown.parse_title,
}
use lib::scan {Markdown.Cursor}
use lib::types {Markdown.LinkRef, Markdown.RawBlock, Markdown.RawItem}

open Markdown.RawBlock {
    raw_paragraph, raw_heading, raw_thematic_break, raw_code_block,
    raw_block_quote, raw_list, raw_table, raw_html_block,
}

pub def Markdown.mk_ref (label : String) (dest : String) (title : Option String) : Markdown.LinkRef :=
    let r : Markdown.LinkRef := { label := label, dest := dest, title := title } in r

/// Only spaces and tabs may remain before the end of the line.
pub def Markdown.at_line_end (c : Markdown.Cursor) : Bool :=
    let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    match Markdown.Cursor.peek skipped {
        Option.none => true,
        Option.some b => U8.beq b 10u8
    }

/// Consume the line's terminating newline, if any.
pub def Markdown.skip_line_end (c : Markdown.Cursor) : Markdown.Cursor :=
    match Markdown.Cursor.peek c {
        Option.some b => if U8.beq b 10u8 then Markdown.Cursor.step c else c,
        Option.none => c
    }

/// `[label]: destination "title"` at the start of a line.
pub def Markdown.parse_ref_def (c0 : Markdown.Cursor) : Option (Pair Markdown.LinkRef Markdown.Cursor) :=
    let c : Markdown.Cursor := Markdown.Cursor.skip_spaces c0 in
    if I64.gt (I64.sub c.column c0.column) 3i64
    then Option.none
    else
        match Markdown.parse_ref_label c {
            Option.none => Option.none,
            Option.some labelled =>
                match labelled {
                    Pair.pair label after_label =>
                        match Markdown.Cursor.peek after_label {
                            Option.some colon =>
                                if Bool.not (U8.beq colon 58u8)
                                then Option.none
                                else
                                    match Markdown.parse_destination (Markdown.Cursor.step after_label) {
                                        Option.none => Option.none,
                                        Option.some destination =>
                                            match destination {
                                                Pair.pair dest after_dest =>
                                                    Markdown.ref_def_tail label dest after_dest
                                            }
                                    },
                            Option.none => Option.none
                        }
                }
        }

def Markdown.ref_def_tail
    (label : String) (dest : String) (after_dest : Markdown.Cursor)
    : Option (Pair Markdown.LinkRef Markdown.Cursor) :=
    let normalized : String := Markdown.normalize_label label in
    if String.beq normalized ""
    then Option.none
    else
        match Markdown.parse_title after_dest {
            Option.some titled =>
                match titled {
                    Pair.pair title after_title =>
                        if Markdown.at_line_end after_title
                        then Option.some
                            (Pair.pair (Markdown.mk_ref normalized dest (Option.some title))
                                (Markdown.skip_line_end (Markdown.Cursor.skip_spaces after_title)))
                        else Markdown.ref_def_no_title normalized dest after_dest
                },
            Option.none => Markdown.ref_def_no_title normalized dest after_dest
        }

/// Without a title the definition must end on the destination's line.
def Markdown.ref_def_no_title
    (label : String) (dest : String) (after_dest : Markdown.Cursor)
    : Option (Pair Markdown.LinkRef Markdown.Cursor) :=
    if Markdown.at_line_end after_dest
    then Option.some
        (Pair.pair (Markdown.mk_ref label dest Option.none)
            (Markdown.skip_line_end (Markdown.Cursor.skip_spaces after_dest)))
    else Option.none

/// Peel definitions off the front of a paragraph's text.
#[partial]
def Markdown.refs_go (c : Markdown.Cursor) (acc : List Markdown.LinkRef)
    : Pair (List Markdown.LinkRef) String :=
    match Markdown.parse_ref_def c {
        Option.some parsed =>
            match parsed {
                Pair.pair found rest => Markdown.refs_go rest (List.cons found acc)
            },
        Option.none => Pair.pair (List.reverse acc) c.text
    }

pub def Markdown.refs_of_text (text : String) : Pair (List Markdown.LinkRef) String :=
    Markdown.refs_go (Markdown.Cursor.start text) List.empty

// ─── Hoisting ───

#[partial]
def Markdown.collect_refs (blocks : List Markdown.RawBlock)
    : Pair (List Markdown.LinkRef) (List Markdown.RawBlock) :=
    Markdown.collect_refs_go blocks List.empty List.empty

#[partial]
def Markdown.collect_refs_go
    (blocks : List Markdown.RawBlock)
    (refs : List Markdown.LinkRef) (kept : List Markdown.RawBlock)
    : Pair (List Markdown.LinkRef) (List Markdown.RawBlock) :=
    match blocks {
        List.empty => Pair.pair (List.reverse refs) (List.reverse kept),
        List.cons b rest =>
            match Markdown.collect_block b refs {
                Pair.pair refs2 block =>
                    match block {
                        Option.some rewritten => Markdown.collect_refs_go rest refs2 (List.cons rewritten kept),
                        Option.none => Markdown.collect_refs_go rest refs2 kept
                    }
            }
    }

#[partial]
def Markdown.collect_block
    (b : Markdown.RawBlock) (refs : List Markdown.LinkRef)
    : Pair (List Markdown.LinkRef) (Option Markdown.RawBlock) :=
    match b {
        raw_paragraph lines =>
            match Markdown.refs_of_text (Markdown.join_lines lines) {
                Pair.pair found remaining =>
                    let all : List Markdown.LinkRef := Markdown.refs_onto found refs in
                    if String.beq (Markdown.trim_space remaining) ""
                    then Pair.pair all Option.none
                    else Pair.pair all (Option.some (raw_paragraph [remaining]))
            },
        // A setext heading was a paragraph until its underline arrived, so it
        // can still start with reference definitions.
        raw_heading level setext lines =>
            if setext
            then
                match Markdown.refs_of_text (Markdown.join_lines lines) {
                    Pair.pair found remaining =>
                        let all : List Markdown.LinkRef := Markdown.refs_onto found refs in
                        if String.beq (Markdown.trim_space remaining) ""
                        then Pair.pair all Option.none
                        else Pair.pair all (Option.some (raw_heading level setext [remaining]))
                }
            else Pair.pair refs (Option.some b),
        raw_block_quote blocks =>
            match Markdown.collect_refs blocks {
                Pair.pair found rewritten =>
                    Pair.pair (Markdown.refs_onto found refs) (Option.some (raw_block_quote rewritten))
            },
        raw_list kind tight items =>
            match Markdown.collect_items items List.empty List.empty {
                Pair.pair found rewritten =>
                    Pair.pair (Markdown.refs_onto found refs) (Option.some (raw_list kind tight rewritten))
            },
        _ => Pair.pair refs (Option.some b)
    }

#[partial]
def Markdown.collect_items
    (items : List Markdown.RawItem)
    (refs : List Markdown.LinkRef) (kept : List Markdown.RawItem)
    : Pair (List Markdown.LinkRef) (List Markdown.RawItem) :=
    match items {
        List.empty => Pair.pair (List.reverse refs) (List.reverse kept),
        List.cons item rest =>
            match Markdown.collect_refs item.blocks {
                Pair.pair found rewritten =>
                    let item2 : Markdown.RawItem := { checked := item.checked, blocks := rewritten } in
                    Markdown.collect_items rest (Markdown.refs_onto found refs) (List.cons item2 kept)
            }
    }

/// Definitions are collected in document order; because the caller's list is
/// reversed, appending keeps the earliest definition first.
#[partial]
def Markdown.refs_onto (found : List Markdown.LinkRef) (acc : List Markdown.LinkRef) : List Markdown.LinkRef :=
    match found {
        List.empty => acc,
        List.cons r rest => Markdown.refs_onto rest (List.cons r acc)
    }

/// Join a paragraph's lines back into one string with `\n`; the inline pass
/// and definition parser both work on text.
#[partial]
def Markdown.join_lines (lines : List String) : String :=
    Markdown.join_lines_go lines List.empty

#[partial]
def Markdown.join_lines_go (lines : List String) (acc : List String) : String :=
    match lines {
        List.empty => String.concat_list (List.reverse acc),
        List.cons l rest =>
            match rest {
                List.empty => Markdown.join_lines_go rest (List.cons l acc),
                List.cons _ _ => Markdown.join_lines_go rest (List.cons "\n" (List.cons l acc))
            }
    }

#[partial]
def Markdown.trim_space (s : String) : String :=
    if is_empty s
    then s
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.or (U8.beq b 32u8) (Bool.or (U8.beq b 9u8) (U8.beq b 10u8))
                then Markdown.trim_space (String.drop 1i64 s)
                else s,
            Option.none => s
        }

// ─── Lookup ───

/// The first definition with this normalized label (first wins).
#[partial]
pub def Markdown.lookup_ref (label : String) (refs : List Markdown.LinkRef) : Option Markdown.LinkRef :=
    match refs {
        List.empty => Option.none,
        List.cons r rest =>
            if String.beq r.label label then Option.some r else Markdown.lookup_ref label rest
    }
