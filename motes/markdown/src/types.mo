/// The renderer-neutral Markdown AST.
///
/// Single-constructor shapes are structs (named fields, dot access, update
/// syntax); multi-constructor sums are `type`s. Types carry their dotted
/// names directly rather than living inside `with Markdown { ... }`: a
/// `with`-declared constructor is not visible across modules on the Rust host
/// (see `motes/xml_html/src/html.mo`).
///
/// The contract is total: any byte sequence parses to a `Document`, so there
/// is no `ParseError`, no `Result`, and no failure branch in any consumer.
///
/// Equality is hand-rolled throughout (`Markdown.beq` and its helpers):
/// generic `BEq (List A)` dispatch is unreliable at run time, the same reason
/// `motes/xml_html` and `motes/yaml` walk their own lists.
use init::string {}

pub struct Markdown.Document {
    front : Option Markdown.Frontmatter,
    blocks : List Markdown.Block
}

/// Frontmatter is metadata: the delimiter splitter preserves its literal
/// text and nothing here interprets it.
pub struct Markdown.Frontmatter {
    format : Markdown.FrontFormat,
    literal : String
}

pub type Markdown.FrontFormat {
    front_yaml,
    front_toml
}

/// The result of splitting frontmatter off the head of a source string.
pub struct Markdown.FrontSplit {
    front : Option Markdown.Frontmatter,
    body : String
}

pub type Markdown.Block {
    block_paragraph (inlines : List Markdown.Inline),
    block_heading (level : I64) (inlines : List Markdown.Inline),
    block_thematic_break,
    block_code_block (info : Option String) (literal : String),
    block_quote (blocks : List Markdown.Block),
    block_list (kind : Markdown.ListKind) (tight : Bool) (items : List Markdown.ListItem),
    block_table (aligns : List Markdown.Align) (head : Markdown.TableRow) (rows : List Markdown.TableRow),
    block_html_block (literal : String)
}

/// Bullet markers (`-`, `+`, `*`) and ordered delimiters (`.`, `)`) are
/// stored so parsing is source-faithful; builders default to `-` and `.`.
pub type Markdown.ListKind {
    list_bullet (marker : String),
    list_ordered (start : I64) (delimiter : String)
}

/// `checked` is a GFM task-list state; `none` is an ordinary item.
pub struct Markdown.ListItem {
    checked : Option Bool,
    blocks : List Markdown.Block
}

pub struct Markdown.TableRow {
    cells : List (List Markdown.Inline)
}

pub type Markdown.Align {
    align_none,
    align_left,
    align_center,
    align_right
}

/// `inline_image.alt` is flattened at parse time, matching CommonMark's HTML
/// `alt` rendering: emphasis inside an image label is intentionally lost.
/// Raw HTML is preserved (`inline_html`, `block_html_block`); escaping is a
/// renderer policy, not a parse policy.
pub type Markdown.Inline {
    inline_text (text : String),
    inline_soft_break,
    inline_hard_break,
    inline_emphasis (children : List Markdown.Inline),
    inline_strong (children : List Markdown.Inline),
    inline_strikethrough (children : List Markdown.Inline),
    inline_code (text : String),
    inline_link (dest : String) (title : Option String) (children : List Markdown.Inline),
    inline_image (dest : String) (title : Option String) (alt : String),
    inline_autolink (dest : String) (label : String),
    inline_html (literal : String)
}

// ─── Parser-internal tree ───
//
// The block pass produces `RawBlock`s, whose paragraphs, headings and table
// cells still hold SOURCE text. Inline parsing runs after the whole block
// pass, so a link reference definition anywhere in the document resolves a
// link anywhere else. `Markdown.resolve_block` (parse.mo) turns this into the
// public `Block`.

pub type Markdown.RawBlock {
    raw_paragraph (lines : List String),
    raw_heading (level : I64) (setext : Bool) (lines : List String),
    raw_thematic_break,
    raw_code_block (info : Option String) (literal : String),
    raw_block_quote (blocks : List Markdown.RawBlock),
    raw_list (kind : Markdown.ListKind) (tight : Bool) (items : List Markdown.RawItem),
    raw_table (aligns : List Markdown.Align) (head : List String) (rows : List (List String)),
    raw_html_block (literal : String)
}

/// A resolved link reference definition. `label` is already normalized.
pub struct Markdown.LinkRef {
    label : String,
    dest : String,
    title : Option String
}

pub struct Markdown.RawItem {
    checked : Option Bool,
    blocks : List Markdown.RawBlock
}

// ─── Equality ───

/// `Bool` has a `BEq` instance but no `Bool.beq` def, and generic dispatch is
/// what this file avoids; this is the instance's own body.
def Markdown.bool_eq (a b : Bool) : Bool :=
    if a then b else Bool.not b

def Markdown.option_string_beq (a b : Option String) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => String.beq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

def Markdown.option_i64_beq (a b : Option I64) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => I64.beq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

def Markdown.option_bool_beq (a b : Option Bool) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => Markdown.bool_eq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

pub def Markdown.align_beq (a b : Markdown.Align) : Bool :=
    match a {
        align_none => match b { align_none => true, _ => false },
        align_left => match b { align_left => true, _ => false },
        align_center => match b { align_center => true, _ => false },
        align_right => match b { align_right => true, _ => false }
    }

pub def Markdown.list_kind_beq (a b : Markdown.ListKind) : Bool :=
    match a {
        list_bullet m1 => match b {
            list_bullet m2 => String.beq m1 m2,
            _ => false
        },
        list_ordered s1 d1 => match b {
            list_ordered s2 d2 => Bool.and (I64.beq s1 s2) (String.beq d1 d2),
            _ => false
        }
    }

#[partial]
pub def Markdown.inline_beq (a b : Markdown.Inline) : Bool :=
    match a {
        inline_text t1 => match b {
            inline_text t2 => String.beq t1 t2,
            _ => false
        },
        inline_soft_break => match b { inline_soft_break => true, _ => false },
        inline_hard_break => match b { inline_hard_break => true, _ => false },
        inline_emphasis c1 => match b {
            inline_emphasis c2 => Markdown.inlines_beq c1 c2,
            _ => false
        },
        inline_strong c1 => match b {
            inline_strong c2 => Markdown.inlines_beq c1 c2,
            _ => false
        },
        inline_strikethrough c1 => match b {
            inline_strikethrough c2 => Markdown.inlines_beq c1 c2,
            _ => false
        },
        inline_code t1 => match b {
            inline_code t2 => String.beq t1 t2,
            _ => false
        },
        inline_link d1 ti1 c1 => match b {
            inline_link d2 ti2 c2 =>
                Bool.and (String.beq d1 d2)
                    (Bool.and (Markdown.option_string_beq ti1 ti2) (Markdown.inlines_beq c1 c2)),
            _ => false
        },
        inline_image d1 ti1 a1 => match b {
            inline_image d2 ti2 a2 =>
                Bool.and (String.beq d1 d2)
                    (Bool.and (Markdown.option_string_beq ti1 ti2) (String.beq a1 a2)),
            _ => false
        },
        inline_autolink d1 l1 => match b {
            inline_autolink d2 l2 => Bool.and (String.beq d1 d2) (String.beq l1 l2),
            _ => false
        },
        inline_html l1 => match b {
            inline_html l2 => String.beq l1 l2,
            _ => false
        }
    }

#[partial]
pub def Markdown.inlines_beq (a b : List Markdown.Inline) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.inline_beq x y) (Markdown.inlines_beq xs ys)
        }
    }

pub def Markdown.table_row_beq (a b : Markdown.TableRow) : Bool :=
    Markdown.cells_beq a.cells b.cells

#[partial]
def Markdown.cells_beq (a b : List (List Markdown.Inline)) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.inlines_beq x y) (Markdown.cells_beq xs ys)
        }
    }

#[partial]
pub def Markdown.block_beq (a b : Markdown.Block) : Bool :=
    match a {
        block_paragraph i1 => match b {
            block_paragraph i2 => Markdown.inlines_beq i1 i2,
            _ => false
        },
        block_heading l1 i1 => match b {
            block_heading l2 i2 => Bool.and (I64.beq l1 l2) (Markdown.inlines_beq i1 i2),
            _ => false
        },
        block_thematic_break => match b { block_thematic_break => true, _ => false },
        block_code_block f1 t1 => match b {
            block_code_block f2 t2 =>
                Bool.and (Markdown.option_string_beq f1 f2) (String.beq t1 t2),
            _ => false
        },
        block_quote b1 => match b {
            block_quote b2 => Markdown.blocks_beq b1 b2,
            _ => false
        },
        block_list k1 tight1 items1 => match b {
            block_list k2 tight2 items2 =>
                Bool.and (Markdown.list_kind_beq k1 k2)
                    (Bool.and (Markdown.bool_eq tight1 tight2) (Markdown.items_beq items1 items2)),
            _ => false
        },
        block_table a1 h1 r1 => match b {
            block_table a2 h2 r2 =>
                Bool.and (Markdown.aligns_beq a1 a2)
                    (Bool.and (Markdown.table_row_beq h1 h2) (Markdown.rows_beq r1 r2)),
            _ => false
        },
        block_html_block l1 => match b {
            block_html_block l2 => String.beq l1 l2,
            _ => false
        }
    }

#[partial]
def Markdown.blocks_beq (a b : List Markdown.Block) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.block_beq x y) (Markdown.blocks_beq xs ys)
        }
    }

#[partial]
pub def Markdown.list_item_beq (a b : Markdown.ListItem) : Bool :=
    Bool.and (Markdown.option_bool_beq a.checked b.checked) (Markdown.blocks_beq a.blocks b.blocks)

#[partial]
def Markdown.items_beq (a b : List Markdown.ListItem) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.list_item_beq x y) (Markdown.items_beq xs ys)
        }
    }

#[partial]
def Markdown.rows_beq (a b : List Markdown.TableRow) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.table_row_beq x y) (Markdown.rows_beq xs ys)
        }
    }

#[partial]
def Markdown.aligns_beq (a b : List Markdown.Align) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => Bool.and (Markdown.align_beq x y) (Markdown.aligns_beq xs ys)
        }
    }

pub def Markdown.front_format_beq (a b : Markdown.FrontFormat) : Bool :=
    match a {
        front_yaml => match b { front_yaml => true, _ => false },
        front_toml => match b { front_toml => true, _ => false }
    }

pub def Markdown.frontmatter_beq (a b : Markdown.Frontmatter) : Bool :=
    Bool.and (Markdown.front_format_beq a.format b.format) (String.beq a.literal b.literal)

pub def Markdown.front_split_beq (a b : Markdown.FrontSplit) : Bool :=
    Bool.and (Markdown.option_frontmatter_beq a.front b.front) (String.beq a.body b.body)

def Markdown.option_frontmatter_beq (a b : Option Markdown.Frontmatter) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => Markdown.frontmatter_beq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

pub def Markdown.beq (a b : Markdown.Document) : Bool :=
    Bool.and (Markdown.option_frontmatter_beq a.front b.front) (Markdown.blocks_beq a.blocks b.blocks)
