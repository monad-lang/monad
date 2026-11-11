/// Extraction tests: the doc-comment scan, the signature cut, and the
/// file filters, on source strings -- no filesystem, no checkout.
use lib::extract {DocExtract.extract_source}
use lib::model {DocItem, DocModule}

/// A source with every shape the extractor handles: a module doc, a
/// documented pub def, an undocumented priv def, an attribute between
/// docs and declaration, a struct, and a bodyless native.
def sample : String :=
    "/// Module docs.\n///\n/// Second paragraph.\n\n/// Docs for foo.\n#[test]\npub def foo (x : I64) : I64 := x + 1\n\npriv def hidden : I64 := 2\n\n/// A point.\npub struct P { x : I64 }\n\n#[native \"bar\"]\npub def bar (s : String) : String\n"

/// The sample's first item, or a crash message the test output names.
def first_item (m : DocModule) : DocItem :=
    match m.items {
        List.empty => DocItem.mk "NONE" "NONE" false Option.none "" "NONE" 0,
        List.cons i rest => i,
    }

/// The sample's items, as a list of names for easy assertions.
def names_of (m : DocModule) : List String :=
    List.map (fn (i : DocItem) => i.name) m.items

#[test]
def test_module_doc_is_the_leading_block : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    match m {
        { doc, .. } =>
            match doc {
                Option.none => false,
                Option.some d =>
                    let shared : Shared String := Shared.of d in
                    String.contains (Shared.get shared) "Module docs."
                        && String.contains (Shared.get shared) "Second paragraph.",
            },
    }

#[test]
def test_every_declaration_is_an_item : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    match m {
        { items, .. } => I64.beq (List.length items) 4,
    }

#[test]
def test_docs_skip_the_attribute : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    match first_item m {
        { name, doc, .. } =>
            Bool.and (String.beq name "foo")
                (match doc {
                    Option.none => false,
                    Option.some d => String.beq d "Docs for foo.",
                }),
    }

#[test]
def test_signature_cuts_the_body : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    match first_item m {
        { signature, .. } =>
            Bool.and (String.contains signature ": I64 := x + 1")
                (Bool.not (String.contains signature "\n")),
    }

/// A bodyless native's signature is its whole declaration: there is no
/// body to cut, and the trailing `:` line ends the header.
#[test]
def test_bodyless_native_signature_is_whole : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    has_native_signature (List.reverse m.items) false

#[terminating]
def has_native_signature (items : List DocItem) (found : Bool) : Bool :=
    match items {
        List.empty => found,
        List.cons i rest =>
            if String.beq i.name "bar"
            then has_native_signature rest (String.contains i.signature ": String")
            else has_native_signature rest found,
    }

#[test]
def test_priv_is_not_pub : Bool :=
    let m : DocModule := DocExtract.extract_source "init/src/sample.mo" sample in
    all_priv_not_pub m.items true

#[terminating]
def all_priv_not_pub (items : List DocItem) (ok : Bool) : Bool :=
    match items {
        List.empty => ok,
        List.cons i rest =>
            if String.beq i.name "hidden"
            then all_priv_not_pub rest (Bool.and ok (Bool.not i.pub_item))
            else all_priv_not_pub rest ok,
    }

/// A `//` line between the docs and the declaration separates them: the
/// declaration gets no docs, and the comment does not leak in.
#[test]
def test_plain_comment_separates_docs : Bool :=
    let src : String := "/// Docs.\n// separator\npub def foo : I64 := 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest =>
                    match i.doc {
                        Option.none => true,
                        Option.some d => false,
                    },
            },
    }

/// A blank line between the docs and the declaration ends the block: the
/// docs do not attach, because the same gap is how the file separates a
/// module header or a previous declaration from this one.
#[test]
def test_blank_line_ends_the_doc_block : Bool :=
    let src : String := "/// Docs.\n\npub def foo : I64 := 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest =>
                    match i.doc {
                        Option.none => true,
                        Option.some d => false,
                    },
            },
    }

/// A multi-line doc block keeps its reading order: the line nearest the
/// declaration is the LAST line, not the first. The declaration walk moves
/// upward and conses, so getting this wrong reverses the whole paragraph.
#[test]
def test_multi_line_doc_keeps_reading_order : Bool :=
    let src : String := "/// Line one.\n/// Line two.\n/// Line three.\npub def foo : I64 := 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest =>
                    match i.doc {
                        Option.none => false,
                        Option.some d =>
                            let shared : Shared String := Shared.of d in
                            String.starts_with "Line one." (Shared.get shared)
                                && String.ends_with (Shared.get shared) "Line three.",
                    },
            },
    }

/// A `#[test]` def is not API: a page shows a `pub def`, and the test
/// attribute is dropped with the other leading attributes. The signature
/// carries the visibility and the type, never the attribute.
#[test]
def test_signature_drops_leading_attributes : Bool :=
    let src : String := "#[test]\npub def foo (x : I64) : I64 := x + 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest =>
                    let shared : Shared String := Shared.of i.signature in
                    String.starts_with "pub def foo" (Shared.get shared)
                        && Bool.not (String.contains (Shared.get shared) "#["),
            },
    }

/// `use` lines are the file's wiring, not its API: they carry no name a
/// reader of the module comes for, so they are not items.
#[test]
def test_use_lines_are_not_items : Bool :=
    let src : String := "use std::io {IO.println}\n\npub def foo : I64 := 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } => I64.beq (List.length items) 1,
    }

/// The line number is 1-based and points at the declaration's first line.
#[test]
def test_line_numbers_are_one_based : Bool :=
    let src : String := "/// Docs.\n#[test]\npub def foo : I64 := 1\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest => I64.beq i.line 3,
            },
    }
