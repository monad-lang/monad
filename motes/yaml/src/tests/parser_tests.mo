/// Parser tests for `motes/yaml`: the supported subset, the explicit
/// rejections, error positions, and the round-trip invariant.
use init::number {}
use yaml::yaml {Yaml}

def parser_is (src : String) (want : Yaml) : Bool :=
    match Yaml.parse src {
        Result.ok v => Yaml.beq v want,
        Result.err _ => false,
    }

def parser_err (src : String) : Bool :=
    match Yaml.parse src {
        Result.ok _ => false,
        Result.err _ => true,
    }

def parser_roundtrips (y : Yaml) : Bool :=
    match Yaml.parse (Yaml.to_string y) {
        Result.ok v => Yaml.beq v y,
        Result.err _ => false,
    }

// ─── Scalars and the empty document ───

#[test]
def test_parse_empty_document_is_null : Bool :=
    parser_is "" Yaml.make_null

#[test]
def test_parse_comments_only_is_null : Bool :=
    parser_is "# just a comment\n\n# another\n" Yaml.make_null

#[test]
def test_parse_plain_string : Bool :=
    parser_is "hello world" (Yaml.make_str "hello world")

#[test]
def test_parse_plain_integer : Bool :=
    parser_is "42" (Yaml.make_int 42)

#[test]
def test_parse_plain_negative_integer : Bool :=
    parser_is "-7" (Yaml.make_int (I64.neg 7i64))

#[test]
def test_parse_plain_float : Bool :=
    parser_is "3.14" (Yaml.make_float 3.14f64)

#[test]
def test_parse_plain_booleans : Bool :=
    parser_is "true" (Yaml.make_bool true) && parser_is "False" (Yaml.make_bool false)

#[test]
def test_parse_null_spellings : Bool :=
    parser_is "~" Yaml.make_null && parser_is "null" Yaml.make_null

#[test]
def test_parse_double_quoted : Bool :=
    parser_is "\"hi\"" (Yaml.make_str "hi")

#[test]
def test_parse_double_quoted_escape : Bool :=
    parser_is "\"a\\nb\"" (Yaml.make_str "a\nb")

#[test]
def test_parse_single_quoted_doubled_quote : Bool :=
    parser_is "'it''s'" (Yaml.make_str "it's")

// ─── Flow collections ───

#[test]
def test_parse_flow_sequence : Bool :=
    parser_is "[1, 2, 3]" (Yaml.make_seq [Yaml.int 1, Yaml.int 2, Yaml.int 3])

#[test]
def test_parse_flow_sequence_trailing_comma : Bool :=
    parser_is "[1, 2,]" (Yaml.make_seq [Yaml.int 1, Yaml.int 2])

#[test]
def test_parse_flow_mapping : Bool :=
    parser_is "{a: 1, b: two}" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.make_str "two")])

#[test]
def test_parse_flow_empty_collections : Bool :=
    parser_is "[]" (Yaml.make_seq []) && parser_is "{}" (Yaml.make_mapping_pairs [])

#[test]
def test_parse_flow_nested : Bool :=
    parser_is "{a: [1, 2]}" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_seq [Yaml.int 1, Yaml.int 2])])

#[test]
def test_parse_flow_duplicate_key_is_error : Bool :=
    parser_err "{a: 1, a: 2}"

// ─── Block structure ───

#[test]
def test_parse_block_mapping : Bool :=
    parser_is "a: 1\nb: 2\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.int 2)])

#[test]
def test_parse_missing_value_is_null : Bool :=
    parser_is "a:\nb: 1\n" (Yaml.make_mapping_pairs [Pair.pair "a" Yaml.make_null, Pair.pair "b" (Yaml.int 1)])

#[test]
def test_parse_nested_mapping : Bool :=
    parser_is "outer:\n  a: 1\n" (Yaml.make_mapping_pairs [Pair.pair "outer" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1)])])

#[test]
def test_parse_block_sequence : Bool :=
    parser_is "- 1\n- 2\n" (Yaml.make_seq [Yaml.int 1, Yaml.int 2])

#[test]
def test_parse_sequence_of_mappings : Bool :=
    parser_is "- a: 1\n  b: 2\n"
        (Yaml.make_seq [Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.int 2)]])

#[test]
def test_parse_indentless_sequence : Bool :=
    parser_is "a:\n- 1\n- 2\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_seq [Yaml.int 1, Yaml.int 2])])

#[test]
def test_parse_sequence_under_key : Bool :=
    parser_is "a:\n  - 1\n  - 2\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_seq [Yaml.int 1, Yaml.int 2])])

// ─── Block scalars ───

#[test]
def test_parse_block_scalar_literal_clip : Bool :=
    parser_is "a: |\n  line1\n  line2\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "line1\nline2\n")])

#[test]
def test_parse_block_scalar_literal_strip : Bool :=
    parser_is "a: |-\n  x\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "x")])

#[test]
def test_parse_block_scalar_folded : Bool :=
    parser_is "a: >\n  one\n  two\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "one two\n")])

/// `+` keeps every trailing newline the source had -- exactly one here, not
/// two. This branch is where an off-by-one hides.
#[test]
def test_parse_block_scalar_keep_one_newline : Bool :=
    parser_is "a: |+\n  x\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "x\n")])

#[test]
def test_parse_block_scalar_keep_trailing_blank_line : Bool :=
    parser_is "a: |+\n  x\n\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "x\n\n")])

#[test]
def test_parse_block_scalar_folded_keep : Bool :=
    parser_is "a: >+\n  one\n  two\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "one two\n")])

#[test]
def test_parse_block_scalar_keeps_hash_lines : Bool :=
    parser_is "a: |\n  # not a comment\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "# not a comment\n")])

// ─── Comments and quoting ───

#[test]
def test_parse_trailing_comment : Bool :=
    parser_is "a: 1 # note\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1)])

#[test]
def test_parse_hash_inside_quotes_is_kept : Bool :=
    parser_is "a: \"x # y\"\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_str "x # y")])

// ─── Document markers ───

#[test]
def test_parse_document_markers : Bool :=
    parser_is "---\na: 1\n...\n" (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1)])

#[test]
def test_parse_multiple_documents_is_error : Bool :=
    parser_err "a: 1\n---\nb: 2\n"

// ─── Explicit rejections ───

#[test]
def test_parse_duplicate_key_is_error : Bool :=
    parser_err "a: 1\na: 2\n"

#[test]
def test_parse_tab_indentation_is_error : Bool :=
    parser_err "\ta: 1\n"

#[test]
def test_parse_anchor_is_error : Bool :=
    parser_err "a: &anchor 1\n"

#[test]
def test_parse_alias_is_error : Bool :=
    parser_err "a: *anchor\n"

#[test]
def test_parse_tag_is_error : Bool :=
    parser_err "a: !!str 1\n"

#[test]
def test_parse_directive_is_error : Bool :=
    parser_err "%YAML 1.2\n---\na: 1\n"

#[test]
def test_parse_complex_key_is_error : Bool :=
    parser_err "? complex\n: value\n"

#[test]
def test_parse_multiline_flow_is_error : Bool :=
    parser_err "a: [1,\n  2]\n"

#[test]
def test_parse_other_radix_is_error : Bool :=
    parser_err "a: 0x10\n"

#[test]
def test_parse_unterminated_quote_is_error : Bool :=
    parser_err "a: \"oops\n"

#[test]
def test_parse_error_carries_the_line : Bool :=
    match Yaml.parse "a: 1\nb: [1,\n" {
        Result.ok _ => false,
        Result.err e => I64.beq e.line 2i64,
    }

// ─── Round trips ───

#[test]
def test_roundtrip_mapping : Bool :=
    parser_roundtrips (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.make_seq [Yaml.int 2])])

#[test]
def test_roundtrip_nested_sequence : Bool :=
    parser_roundtrips (Yaml.make_seq [Yaml.make_seq [Yaml.int 1], Yaml.int 2])

#[test]
def test_roundtrip_ambiguous_strings : Bool :=
    parser_roundtrips (Yaml.make_seq [
        Yaml.make_str "5",
        Yaml.make_str "true",
        Yaml.make_str "null",
        Yaml.make_str "a: b",
        Yaml.make_str "- x",
        Yaml.make_str "yes",
    ])

#[test]
def test_roundtrip_integral_float : Bool :=
    parser_roundtrips (Yaml.make_float 3.0f64)

#[test]
def test_roundtrip_non_finite_float : Bool :=
    parser_roundtrips (Yaml.make_float (1.0f64 / 0.0f64)) &&
    parser_roundtrips (Yaml.make_float (0.0f64 - (1.0f64 / 0.0f64)))

#[test]
def test_roundtrip_string_with_newline : Bool :=
    parser_roundtrips (Yaml.make_str "line1\nline2")

#[test]
def test_roundtrip_empty_collections : Bool :=
    parser_roundtrips (Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.make_seq []), Pair.pair "b" (Yaml.make_mapping_pairs [])])
