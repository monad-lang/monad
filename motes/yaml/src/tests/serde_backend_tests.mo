/// Tests for `motes/yaml/src/serde_backend.mo`: the derive macros against
/// the real `Yaml` format, mirroring `motes/json/src/tests/serde_backend_tests.mo`.
///
/// Two shape rules this file obeys:
///
/// * A file containing `reflect_type_info!` cannot use a top-level
///   `def x : T := { ... }` struct literal ("cannot infer the type of
///   `{ .. }`"), so every sample value is a local `let` inside its test.
/// * Every reference to a macro-generated `Type.serialize_yaml`/
///   `Type.deserialize_yaml` lives inside a `#[test]` def. A plain `def`
///   that names one fails the Rust host's macro meta-check (macros expand
///   one at a time there), and its type ANNOTATION naming the derived struct
///   fails lowering with `UnknownInductive`.
use init::number {}
use yaml::yaml {Yaml}
use yaml::serde_backend {derive_yaml_serialize, derive_yaml_deserialize}

struct YamlSerdePoint {
    x : I64,
    name : String,
}

derive_yaml_serialize! YamlSerdePoint
derive_yaml_deserialize! YamlSerdePoint

#[test]
def test_derive_yaml_serialize_shape : Bool :=
    let p : YamlSerdePoint := { x := 5, name := "hi" } in
    String.beq (Yaml.to_string (YamlSerdePoint.serialize_yaml p)) "name: hi\nx: 5"

#[test]
def test_derive_yaml_roundtrip : Bool :=
    let p : YamlSerdePoint := { x := 5, name := "hi" } in
    match YamlSerdePoint.deserialize_yaml (YamlSerdePoint.serialize_yaml p) {
        Result.ok p2 =>
            match p2 { YamlSerdePoint.mk x name => x == 5 && String.beq name "hi" },
        Result.err _ => false,
    }

#[test]
def test_derive_yaml_decodes_source_text : Bool :=
    let v : Yaml := Yaml.make_mapping_pairs [Pair.pair "x" (Yaml.make_int 7), Pair.pair "name" (Yaml.make_str "bob")] in
    match YamlSerdePoint.deserialize_yaml v {
        Result.ok p =>
            match p { YamlSerdePoint.mk x name => x == 7 && String.beq name "bob" },
        Result.err _ => false,
    }

/// Parsing helper for the end-to-end test. It names no derived type, so it is
/// safe as a plain `def` in a macro-bearing file; a parse failure becomes
/// `null`, which the decoder then rejects.
def yaml_serde_parse_or_null (s : String) : Yaml :=
    match Yaml.parse s {
        Result.ok v => v,
        Result.err _ => Yaml.make_null,
    }

/// The real pipeline: YAML source text -> `Yaml.parse` -> derived decoder.
#[test]
def test_derive_yaml_parses_source_text_then_decodes : Bool :=
    let v : Yaml := yaml_serde_parse_or_null "x: 7\nname: bob\n" in
    match YamlSerdePoint.deserialize_yaml v {
        Result.ok p =>
            match p { YamlSerdePoint.mk x name => x == 7 && String.beq name "bob" },
        Result.err _ => false,
    }

#[test]
def test_derive_yaml_missing_required_field_is_error : Bool :=
    let v : Yaml := Yaml.make_mapping_pairs [Pair.pair "x" (Yaml.make_int 1)] in
    match YamlSerdePoint.deserialize_yaml v {
        Result.ok _ => false,
        Result.err _ => true,
    }

struct YamlSerdeTagged {
    name : String,
    nickname : Option String,
    scores : List I64,
    origin : YamlSerdePoint,
}

derive_yaml_serialize! YamlSerdeTagged
derive_yaml_deserialize! YamlSerdeTagged

#[test]
def test_derive_yaml_option_none_roundtrip : Bool :=
    let origin : YamlSerdePoint := { x := 1, name := "o" } in
    let t : YamlSerdeTagged := { name := "a", nickname := Option.none, scores := [1, 2, 3], origin := origin } in
    match YamlSerdeTagged.deserialize_yaml (YamlSerdeTagged.serialize_yaml t) {
        Result.ok t2 =>
            match t2 {
                YamlSerdeTagged.mk name nickname scores origin2 =>
                    match nickname {
                        Option.some _ => false,
                        Option.none => String.beq name "a",
                    }
            },
        Result.err _ => false,
    }

#[test]
def test_derive_yaml_option_some_and_list_roundtrip : Bool :=
    let origin : YamlSerdePoint := { x := 1, name := "o" } in
    let t : YamlSerdeTagged := { name := "a", nickname := Option.some "nick", scores := [4, 5], origin := origin } in
    match YamlSerdeTagged.deserialize_yaml (YamlSerdeTagged.serialize_yaml t) {
        Result.ok t2 =>
            match t2 {
                YamlSerdeTagged.mk name nickname scores origin2 =>
                    let has_nick : Bool :=
                        match nickname { Option.some n => String.beq n "nick", Option.none => false } in
                    let has_scores : Bool :=
                        match scores {
                            List.cons a tail =>
                                match tail {
                                    List.cons b rest => a == 4 && b == 5 && List.is_empty rest,
                                    List.empty => false,
                                },
                            List.empty => false,
                        } in
                    Bool.and has_nick has_scores
            },
        Result.err _ => false,
    }

struct YamlSerdeDefaulted {
    name : String,
    pattern : String := "*",
}

derive_yaml_serialize! YamlSerdeDefaulted
derive_yaml_deserialize! YamlSerdeDefaulted

#[test]
def test_derive_yaml_missing_defaulted_field_uses_default : Bool :=
    let v : Yaml := Yaml.make_mapping_pairs [Pair.pair "name" (Yaml.make_str "foo")] in
    match YamlSerdeDefaulted.deserialize_yaml v {
        Result.ok d => match d { YamlSerdeDefaulted.mk name pattern => String.beq pattern "*" },
        Result.err _ => false,
    }

#[test]
def test_derive_yaml_present_defaulted_field_overrides : Bool :=
    let v : Yaml := Yaml.make_mapping_pairs [
        Pair.pair "name" (Yaml.make_str "foo"),
        Pair.pair "pattern" (Yaml.make_str "*.mo"),
    ] in
    match YamlSerdeDefaulted.deserialize_yaml v {
        Result.ok d => match d { YamlSerdeDefaulted.mk name pattern => String.beq pattern "*.mo" },
        Result.err _ => false,
    }

struct YamlSerdeRaw {
    label : String,
    payload : Yaml,
}

derive_yaml_serialize! YamlSerdeRaw
derive_yaml_deserialize! YamlSerdeRaw

#[test]
def test_derive_yaml_identity_passthrough_field : Bool :=
    let inner : Yaml := Yaml.make_seq [Yaml.make_int 1, Yaml.make_str "x"] in
    let w : YamlSerdeRaw := { label := "x", payload := inner } in
    match YamlSerdeRaw.deserialize_yaml (YamlSerdeRaw.serialize_yaml w) {
        Result.ok w2 =>
            match w2 { YamlSerdeRaw.mk label payload => Yaml.beq payload inner },
        Result.err _ => false,
    }
