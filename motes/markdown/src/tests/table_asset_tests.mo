// Asset tests for the two generated tables. A regenerated table that loses a
// chunk or shifts a codepoint shows up here long before the corpus notices.
use lib::entities {Markdown.entity_count, Markdown.entity_lookup}
use lib::unicode {
    Markdown.case_fold, Markdown.is_unicode_punctuation, Markdown.is_unicode_whitespace,
}

def some_is (got : Option String) (want : String) : Bool :=
    match got {
        Option.some s => String.beq s want,
        Option.none => false
    }

// ─── Entities ───

#[test]
def test_entity_count : Bool :=
    I64.beq Markdown.entity_count 2125i64

#[test]
def test_entity_lookup_basics : Bool :=
    Bool.and (some_is (Markdown.entity_lookup "amp") "&")
        (Bool.and (some_is (Markdown.entity_lookup "lt") "<")
            (some_is (Markdown.entity_lookup "nbsp") "\u{a0}"))

/// A long name from the middle of the alphabet exercises the chunked trees.
#[test]
def test_entity_lookup_long_name : Bool :=
    some_is (Markdown.entity_lookup "CounterClockwiseContourIntegral") "\u{2233}"

/// Some entities expand to two codepoints.
#[test]
def test_entity_lookup_multi_codepoint : Bool :=
    some_is (Markdown.entity_lookup "NotEqualTilde") "\u{2242}\u{338}"

#[test]
def test_entity_lookup_unknown : Bool :=
    match Markdown.entity_lookup "definitelyNotAnEntity" {
        Option.some _ => false,
        Option.none => true
    }

// ─── Unicode ───

#[test]
def test_unicode_whitespace : Bool :=
    Bool.and (Markdown.is_unicode_whitespace 160u32)
        (Bool.and (Markdown.is_unicode_whitespace 32u32)
            (Bool.and (Markdown.is_unicode_whitespace 9u32)
                (Bool.not (Markdown.is_unicode_whitespace 65u32))))

#[test]
def test_unicode_punctuation : Bool :=
    Bool.and (Markdown.is_unicode_punctuation 8212u32)
        (Bool.and (Markdown.is_unicode_punctuation 36u32)
            (Bool.and (Markdown.is_unicode_punctuation 163u32)
                (Bool.not (Markdown.is_unicode_punctuation 65u32))))

#[test]
def test_case_fold_ascii : Bool :=
    String.beq (Markdown.case_fold "Hello") "hello"

#[test]
def test_case_fold_greek : Bool :=
    String.beq (Markdown.case_fold "ΑΓΩ") "αγω"

/// `ẞ` folds to two characters, which is why labels need the table and not
/// `String.to_lowercase`.
#[test]
def test_case_fold_sharp_s : Bool :=
    Bool.and (String.beq (Markdown.case_fold "ẞ") "ss")
        (String.beq (Markdown.case_fold "Straße") "strasse")
