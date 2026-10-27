/// Printer tests for `motes/yaml`: exact block and flow output, plus every
/// quoting trigger that keeps `parse (to_string y)` equal to `ok y`.
use init::number {}
use yaml::yaml {Yaml}

def printer_map_a_b : Yaml :=
    Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.int 2)]

#[test]
def test_print_null : Bool :=
    String.beq (Yaml.to_string Yaml.make_null) "null"

#[test]
def test_print_bool : Bool :=
    String.beq (Yaml.to_string (Yaml.make_bool true)) "true" &&
    String.beq (Yaml.to_string (Yaml.make_bool false)) "false"

#[test]
def test_print_int : Bool :=
    String.beq (Yaml.to_string (Yaml.make_int 42)) "42"

#[test]
def test_print_float_fraction : Bool :=
    String.beq (Yaml.to_string (Yaml.make_float 3.14f64)) "3.14"

/// `F64.to_string 3.0` is "3", which the reader would resolve as an int.
/// The printer appends `.0` so the shape survives a round trip.
#[test]
def test_print_float_integral_keeps_a_decimal_point : Bool :=
    String.beq (Yaml.to_string (Yaml.make_float 3.0f64)) "3.0"

/// The reader spells non-finite values the core-schema way, not the way
/// `F64.to_string` does ("inf"/"-inf"/"NaN").
#[test]
def test_print_float_non_finite : Bool :=
    String.beq (Yaml.to_string (Yaml.make_float (1.0f64 / 0.0f64))) ".inf" &&
    String.beq (Yaml.to_string (Yaml.make_float (0.0f64 - (1.0f64 / 0.0f64)))) "-.inf" &&
    String.beq (Yaml.to_string (Yaml.make_float (0.0f64 / 0.0f64))) ".nan"

#[test]
def test_print_plain_string : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "hello")) "hello"

#[test]
def test_print_empty_string_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "")) "\"\""

#[test]
def test_print_string_that_looks_like_a_bool_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "true")) "\"true\"" &&
    String.beq (Yaml.to_string (Yaml.make_str "null")) "\"null\""

#[test]
def test_print_string_that_looks_like_a_number_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "5")) "\"5\"" &&
    String.beq (Yaml.to_string (Yaml.make_str "1.5")) "\"1.5\""

#[test]
def test_print_string_with_colon_space_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "a: b")) "\"a: b\""

#[test]
def test_print_string_with_leading_indicator_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "- x")) "\"- x\""

#[test]
def test_print_string_with_hash_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "a#b")) "\"a#b\""

#[test]
def test_print_legacy_boolean_string_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "yes")) "\"yes\""

/// The reader rejects other radixes explicitly, so an unquoted `0x10`
/// string would be a parse error rather than a string.
#[test]
def test_print_other_radix_string_is_quoted : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "0x10")) "\"0x10\""

#[test]
def test_print_string_escapes_newline : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "a\nb")) "\"a\\nb\""

#[test]
def test_print_string_escapes_quote_and_backslash : Bool :=
    String.beq (Yaml.to_string (Yaml.make_str "a\"b")) "\"a\\\"b\"" &&
    String.beq (Yaml.to_string (Yaml.make_str "a\\b")) "\"a\\\\b\""

#[test]
def test_print_empty_sequence : Bool :=
    String.beq (Yaml.to_string (Yaml.make_seq [])) "[]"

#[test]
def test_print_empty_mapping : Bool :=
    String.beq (Yaml.to_string (Yaml.make_mapping_pairs [])) "{}"

#[test]
def test_print_mapping_sorted_flat : Bool :=
    String.beq (Yaml.to_string printer_map_a_b) "a: 1\nb: 2"

#[test]
def test_print_sequence_flat : Bool :=
    String.beq (Yaml.to_string (Yaml.make_seq [Yaml.int 1, Yaml.int 2])) "- 1\n- 2"

#[test]
def test_print_nested_mapping : Bool :=
    let inner : Yaml := printer_map_a_b in
    let outer : Yaml := Yaml.make_mapping_pairs [Pair.pair "outer" inner] in
    String.beq (Yaml.to_string outer) "outer:\n  a: 1\n  b: 2"

#[test]
def test_print_sequence_of_mappings_compact : Bool :=
    let item : Yaml := Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" (Yaml.int 2)] in
    String.beq (Yaml.to_string (Yaml.make_seq [item])) "- a: 1\n  b: 2"

#[test]
def test_print_nested_sequence : Bool :=
    let item : Yaml := Yaml.make_seq [Yaml.int 1, Yaml.int 2] in
    String.beq (Yaml.to_string (Yaml.make_seq [item])) "- - 1\n  - 2"

#[test]
def test_print_flow_scalar : Bool :=
    String.beq (Yaml.to_string_flow (Yaml.make_str "hi")) "hi"

#[test]
def test_print_flow_collections : Bool :=
    let inner : Yaml := Yaml.make_seq [Yaml.int 2, Yaml.int 3] in
    let flow : Yaml := Yaml.make_mapping_pairs [Pair.pair "a" (Yaml.int 1), Pair.pair "b" inner] in
    String.beq (Yaml.to_string_flow flow) "{a: 1, b: [2, 3]}"

#[test]
def test_print_flow_empty_collections : Bool :=
    String.beq (Yaml.to_string_flow (Yaml.make_seq [])) "[]" &&
    String.beq (Yaml.to_string_flow (Yaml.make_mapping_pairs [])) "{}"
