/// Trimmed declaration spans and name ranges (`toolkit::decl_text`).
///
/// Field reads go through typed accessor defs, never inline: a `#[test]`
/// def that touches a struct field is the recorded self-hosted codegen
/// hazard.
use std::list {}
use lang::types {Location, SourceRange}
use toolkit::decl_text {
    DeclText, decl_text_name, decl_text_name_span, decl_text_span, decl_texts_of_source,
}

def range_start (r : SourceRange) : Location := r.start

def range_end (r : SourceRange) : Location := r.end

def loc_offset (l : Location) : I64 := l.offset

def loc_line (l : Location) : I64 := l.line

def loc_column (l : Location) : I64 := l.column

def range_start_offset (r : SourceRange) : I64 := loc_offset (range_start r)

def range_end_offset (r : SourceRange) : I64 := loc_offset (range_end r)

def range_start_line (r : SourceRange) : I64 := loc_line (range_start r)

def range_start_column (r : SourceRange) : I64 := loc_column (range_start r)

def range_end_column (r : SourceRange) : I64 := loc_column (range_end r)

def two_def_source : String := "def a : I64 := 1\ndef b : I64 := 2\n"

/// One of each kind that carries a name.
def kind_source : String :=
    "def a : I64 := 1\ntype Maybe A { some (a : A), none }\nstruct S { x : I64 }\nclass Show A { def show (a : A) : String }\n"

/// A def ends at its own last byte. The parse's end is the next
/// declaration's first byte -- here past a comment line and a doc comment
/// that belong to `b`.
def commented_source : String :=
    "def a : I64 := 1\n// about b\n/// b's doc\ndef b : I64 := 2\n"

#[test]
def test_a_def_span_ends_at_its_last_token : Bool :=
    match decl_texts_of_source commented_source {
        List.cons first _ => I64.beq (range_end_offset (decl_text_span first)) 16,
        List.empty => false,
    }

#[test]
def test_the_last_def_span_drops_the_trailing_newline : Bool :=
    match decl_texts_of_source two_def_source {
        List.cons _ rest => match rest {
            List.cons second _ => I64.beq (range_end_offset (decl_text_span second)) 33,
            List.empty => false,
        },
        List.empty => false,
    }

/// An attribute naming the def in a string, and a doc comment naming it,
/// both come before the name and neither is taken for it.
def attributed_source : String :=
    "/// zz is an answer\n#[native \"zz\"]\npub def zz : I64\n"

/// The name range of every named declaration slices back to the name, and
/// sits inside the declaration's span.
def names_slice_back (src : String) (ds : List DeclText) : Bool :=
    match ds {
        List.empty => true,
        List.cons d rest => name_slices_back src d && names_slice_back src rest,
    }

def name_slices_back (src : String) (d : DeclText) : Bool :=
    let sp : SourceRange := decl_text_span d in
    let nm : SourceRange := decl_text_name_span d in
    let off : I64 := range_start_offset nm in
    let len : I64 := range_end_offset nm - off in
    String.beq (String.slice src off len) (decl_text_name d)
        && Bool.not (I64.lt off (range_start_offset sp))
        && Bool.not (I64.gt (range_end_offset nm) (range_end_offset sp))

#[test]
def test_name_ranges_slice_back_to_the_names : Bool :=
    let ds : List DeclText := decl_texts_of_source kind_source in
    I64.beq (List.length ds) 4 && names_slice_back kind_source ds

#[test]
def test_a_name_range_skips_comments_and_attributes : Bool :=
    let ds : List DeclText := decl_texts_of_source attributed_source in
    I64.beq (List.length ds) 1 && names_slice_back attributed_source ds

#[test]
def test_a_name_range_carries_line_and_column : Bool :=
    match decl_texts_of_source two_def_source {
        List.cons _ rest => match rest {
            List.cons second _ =>
                let nm : SourceRange := decl_text_name_span second in
                I64.beq (range_start_line nm) 2 && I64.beq (range_start_column nm) 5,
            List.empty => false,
        },
        List.empty => false,
    }

/// An unnamed instance has no name in its header (`_` is the parser's
/// sentinel), so its name range is its whole span.
#[test]
def test_an_unnamed_instance_selects_its_whole_span : Bool :=
    match decl_texts_of_source "instance Show I64 { def show x := \"i\" }\n" {
        List.cons d _ =>
            I64.beq (range_start_offset (decl_text_name_span d)) (range_start_offset (decl_text_span d))
                && I64.beq (range_end_offset (decl_text_name_span d)) (range_end_offset (decl_text_span d)),
        List.empty => false,
    }

/// Columns count CHARACTERS, as the parser's do: `é` is two bytes and one
/// column, so the end is byte 23 but column 23, not 24.
#[test]
def test_a_trimmed_end_counts_characters_for_its_column : Bool :=
    match decl_texts_of_source "def zz : String := \"\u{e9}\"\ndef b : I64 := 1\n" {
        List.cons first _ =>
            I64.beq (range_end_offset (decl_text_span first)) 23
                && I64.beq (range_end_column (decl_text_span first)) 23,
        List.empty => false,
    }
