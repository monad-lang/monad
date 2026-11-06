/// The book's navigation, read from `SUMMARY.md` (mdBook's format).
///
/// A `# Heading` after the first starts a part; each list item is a chapter
/// whose link names its source file (`./intro.md`); a nested list nests
/// chapters. The tree is kept flat, with a depth per chapter: the sidebar
/// renders it in order, and prev/next walk the same order.
use markdown::types {Markdown.Block, Markdown.Inline, Markdown.ListItem}
use markdown::parse {Markdown.parse}
use markdown::html {Markdown.plain_of}

/// One sidebar line.
pub type NavEntry {
    /// A part title (`# Tutorial`).
    part (title : String),
    /// A chapter: its title, its page stem (`intro` for `./intro.md`) and its
    /// nesting depth (0 at the top level).
    chapter (title : String) (stem : String) (depth : I64),
}

/// `./foo.md` → `foo`, `bar/baz.md` → `bar/baz`; anything not ending in
/// `.md` is not a chapter link.
pub def Summary.stem_of_link (dest : String) : Option String :=
    let d : String := if String.starts_with "./" dest then String.drop 2 dest else dest in
    let n : I64 := String.length d in
    if n > 3 && String.ends_with d ".md"
    then Option.some (String.slice d 0 (n - 3))
    else Option.none

/// The first link among inlines: its destination and its text.
def first_link (inlines : List Markdown.Inline) : Option (Pair String String) :=
    match inlines {
        List.empty => Option.none,
        List.cons i rest =>
            match i {
                Markdown.Inline.inline_link dest _ children => Option.some (Pair.pair dest (Markdown.plain_of children)),
                _ => first_link rest,
            },
    }

def entry_of_link (depth : I64) (link : Pair String String) : List NavEntry :=
    match link {
        Pair.pair dest title =>
            match Summary.stem_of_link dest {
                Option.some stem => [NavEntry.chapter title stem depth],
                Option.none => List.empty,
            },
    }

/// An item's own link (from its first paragraph) followed by its nested
/// lists, one level deeper.
def item_entries (depth : I64) (blocks : List Markdown.Block) : List NavEntry :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest =>
            List.append (item_block depth b) (item_entries depth rest),
    }

def item_block (depth : I64) (b : Markdown.Block) : List NavEntry :=
    match b {
        Markdown.Block.block_paragraph inlines => link_entries depth (first_link inlines),
        Markdown.Block.block_list _ _ items => list_entries (depth + 1) items,
        _ => List.empty,
    }

def link_entries (depth : I64) (link : Option (Pair String String)) : List NavEntry :=
    match link {
        Option.some l => entry_of_link depth l,
        Option.none => List.empty,
    }

def list_entries (depth : I64) (items : List Markdown.ListItem) : List NavEntry :=
    match items {
        List.empty => List.empty,
        List.cons item rest =>
            match item {
                { blocks, .. } => List.append (item_entries depth blocks) (list_entries depth rest),
            },
    }

/// The entries of the top-level blocks. `first` is true until the first
/// heading has been seen: that one is the file's own title (`# Summary`).
def block_entries (first : Bool) (blocks : List Markdown.Block) : List NavEntry :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest =>
            match b {
                Markdown.Block.block_heading _ inlines =>
                    if first
                    then block_entries false rest
                    else List.cons (NavEntry.part (Markdown.plain_of inlines)) (block_entries false rest),
                Markdown.Block.block_list _ _ items => List.append (list_entries 0 items) (block_entries first rest),
                _ => block_entries first rest,
            },
    }

/// Parse `SUMMARY.md` text into its sidebar entries, in order.
pub def Summary.parse (src : String) : List NavEntry :=
    match Markdown.parse src {
        { blocks, .. } => block_entries true blocks,
    }

/// One chapter in reading order.
pub struct NavChapter {
    title : String,
    stem : String,
}

/// The chapters alone, in reading order (prev/next walk this).
pub def Summary.chapters (entries : List NavEntry) : List NavChapter :=
    match entries {
        List.empty => List.empty,
        List.cons e rest =>
            match e {
                NavEntry.chapter title stem _ =>
                    let c : NavChapter := { title := title, stem := stem } in
                    List.cons c (Summary.chapters rest),
                NavEntry.part _ => Summary.chapters rest,
            },
    }

/// Two `String`s: duplicating shares pointers.
pub instance Copy NavChapter {
    def copy (c : NavChapter) : Pair NavChapter NavChapter := Pair.pair c c
}
