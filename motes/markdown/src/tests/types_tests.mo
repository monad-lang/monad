// AST and options tests: the hand-rolled equality that later phases rely on,
// and the presets that pin each option's default.
use lib::types {
    Markdown.Align, Markdown.Block, Markdown.Document, Markdown.Inline,
    Markdown.ListItem, Markdown.ListKind, Markdown.TableRow, Markdown.beq,
}
use lib::options {
    Markdown.Options, Markdown.commonmark_options, Markdown.default_options,
}

def doc_with (blocks : List Markdown.Block) : Markdown.Document :=
    let d : Markdown.Document := { front := Option.none, blocks := blocks } in d

def paragraph (text : String) : Markdown.Block :=
    Markdown.Block.block_paragraph [Markdown.Inline.inline_text text]

#[test]
def test_empty_document_equals_itself : Bool :=
    Markdown.beq (doc_with List.empty) (doc_with List.empty)

#[test]
def test_paragraph_equality_distinguishes_text : Bool :=
    Bool.not (Markdown.beq (doc_with [paragraph "a"]) (doc_with [paragraph "b"]))

#[test]
def test_paragraph_equality_matches : Bool :=
    Markdown.beq (doc_with [paragraph "a"]) (doc_with [paragraph "a"])

#[test]
def test_equality_sees_list_length : Bool :=
    Bool.not (Markdown.beq (doc_with [paragraph "a"]) (doc_with [paragraph "a", paragraph "b"]))

#[test]
def test_equality_sees_structure : Bool :=
    let emphasised : Markdown.Block :=
        Markdown.Block.block_paragraph [Markdown.Inline.inline_emphasis [Markdown.Inline.inline_text "a"]] in
    Bool.not (Markdown.beq (doc_with [paragraph "a"]) (doc_with [emphasised]))

#[test]
def test_equality_sees_heading_level : Bool :=
    let h1 : Markdown.Block := Markdown.Block.block_heading 1i64 [Markdown.Inline.inline_text "t"] in
    let h2 : Markdown.Block := Markdown.Block.block_heading 2i64 [Markdown.Inline.inline_text "t"] in
    Bool.not (Markdown.beq (doc_with [h1]) (doc_with [h2]))

#[test]
def test_equality_sees_list_tightness : Bool :=
    let item : Markdown.ListItem :=
        { checked := Option.none, blocks := [paragraph "a"] } in
    let tight : Markdown.Block :=
        Markdown.Block.block_list (Markdown.ListKind.list_bullet "-") true [item] in
    let loose : Markdown.Block :=
        Markdown.Block.block_list (Markdown.ListKind.list_bullet "-") false [item] in
    Bool.not (Markdown.beq (doc_with [tight]) (doc_with [loose]))

#[test]
def test_equality_sees_table_cells : Bool :=
    let row_a : Markdown.TableRow := { cells := [[Markdown.Inline.inline_text "a"]] } in
    let row_b : Markdown.TableRow := { cells := [[Markdown.Inline.inline_text "b"]] } in
    let table_a : Markdown.Block :=
        Markdown.Block.block_table [Markdown.Align.align_none] row_a List.empty in
    let table_b : Markdown.Block :=
        Markdown.Block.block_table [Markdown.Align.align_none] row_b List.empty in
    Bool.not (Markdown.beq (doc_with [table_a]) (doc_with [table_b]))

// ─── Option presets ───
//
// Field access lives in helpers, never in a `#[test]` def: a test def with a
// struct field access compiles to the FIELD's type (recorded codegen trap).

def gfm_all_on (o : Markdown.Options) : Bool :=
    Bool.and o.gfm_tables
        (Bool.and o.gfm_task_lists
            (Bool.and o.gfm_strikethrough (Bool.and o.gfm_autolinks (Bool.not o.frontmatter))))

def gfm_all_off (o : Markdown.Options) : Bool :=
    Bool.and (Bool.not o.gfm_tables)
        (Bool.and (Bool.not o.gfm_task_lists)
            (Bool.and (Bool.not o.gfm_strikethrough)
                (Bool.and (Bool.not o.gfm_autolinks) (Bool.not o.frontmatter))))

def max_depth_of (o : Markdown.Options) : I64 := o.max_depth

#[test]
def test_default_options_enable_gfm : Bool :=
    gfm_all_on Markdown.default_options

#[test]
def test_commonmark_options_disable_gfm : Bool :=
    gfm_all_off Markdown.commonmark_options

#[test]
def test_options_default_depth_is_64 : Bool :=
    I64.beq (max_depth_of Markdown.default_options) 64i64
