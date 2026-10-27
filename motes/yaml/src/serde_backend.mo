/// `motes/serde`'s `Serializer`/`Deserializer` instances for `Yaml` -- the
/// backend `derive_yaml_serialize_meta`/`derive_yaml_deserialize_meta`-
/// generated code calls through, via the `yaml_ser_*`/`yaml_de_*` wrapper
/// functions below.
///
/// Mirrors `motes/json/src/serde_backend.mo` exactly, with the `"yaml"` tag
/// and `Expr.e_var "Yaml"`. The wrappers are not decoration: a macro-reified
/// `d_def` that calls a class method by its qualified name fails at run time
/// with `unresolved global`, while calling an ordinary wrapper function
/// works (`motes/serde/src/format.mo` records the probe).
///
/// Field types the derive layer understands: `String`, `I64`, `Bool`,
/// `Option X`, `List X`, nested derived structs, the format type itself
/// (`Yaml`), and defaults. An `F64` field is NOT derived (serde has no
/// `ser_float`); give such a type a hand-written codec.
use serde::format {Serializer, Deserializer}
use serde::derive {derive_serialize_meta, derive_deserialize_meta}
use std::map {Map, BTreeMap}
use yaml::yaml {
    Yaml, Yaml.make_null, Yaml.make_bool, Yaml.make_int, Yaml.make_str,
    Yaml.make_seq, Yaml.make_mapping, Yaml.get_bool, Yaml.get_int, Yaml.get_str,
    Yaml.get_seq, Yaml.get_mapping, Yaml.mapping_get,
}
use init::meta {TypeInfo, MetaDecl, Expr}

def yaml_pairs_to_mapping (fields : List (Pair String Yaml)) (acc : BTreeMap String Yaml) : BTreeMap String Yaml :=
    match fields {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair k v => yaml_pairs_to_mapping rest (Map.insert k v acc),
            },
    }

pub instance Serializer Yaml {
    def ser_null : Yaml := Yaml.make_null
    def ser_bool (b : Bool) : Yaml := Yaml.make_bool b
    def ser_int (i : I64) : Yaml := Yaml.make_int i
    def ser_string (s : String) : Yaml := Yaml.make_str s
    def ser_list (xs : List Yaml) : Yaml := Yaml.make_seq xs
    def ser_object (fields : List (Pair String Yaml)) : Yaml :=
        Yaml.make_mapping (yaml_pairs_to_mapping fields BTreeMap.empty)
}

pub instance Deserializer Yaml {
    def de_is_null (d : Yaml) : Bool :=
        match d { Yaml.null => true, _ => false }
    def de_get_bool (d : Yaml) : Result String Bool := Yaml.get_bool d
    def de_get_int (d : Yaml) : Result String I64 := Yaml.get_int d
    def de_get_string (d : Yaml) : Result String String := Yaml.get_str d
    def de_get_list (d : Yaml) : Result String (List Yaml) := Yaml.get_seq d
    def de_get_field (d : Yaml) (name : String) : Result String (Option Yaml) :=
        match Yaml.get_mapping d {
            Result.err e => Result.err e,
            Result.ok m => Result.ok (Yaml.mapping_get name m),
        }
}

// `derive.mo`'s generated code calls these, never `Serializer.*`/
// `Deserializer.*` directly.
pub def yaml_ser_null : Yaml := Serializer.ser_null
pub def yaml_ser_bool (b : Bool) : Yaml := Serializer.ser_bool b
pub def yaml_ser_int (i : I64) : Yaml := Serializer.ser_int i
pub def yaml_ser_string (s : String) : Yaml := Serializer.ser_string s
pub def yaml_ser_list (xs : List Yaml) : Yaml := Serializer.ser_list xs
pub def yaml_ser_object (fields : List (Pair String Yaml)) : Yaml := Serializer.ser_object fields

pub def yaml_de_is_null (d : Yaml) : Bool := Deserializer.de_is_null d
pub def yaml_de_get_bool (d : Yaml) : Result String Bool := Deserializer.de_get_bool d
pub def yaml_de_get_int (d : Yaml) : Result String I64 := Deserializer.de_get_int d
pub def yaml_de_get_string (d : Yaml) : Result String String := Deserializer.de_get_string d
pub def yaml_de_get_list (d : Yaml) : Result String (List Yaml) := Deserializer.de_get_list d
pub def yaml_de_get_field (d : Yaml) (name : String) : Result String (Option Yaml) := Deserializer.de_get_field d name

// The shared `derive_yaml_serialize!`/`derive_yaml_deserialize!` macros --
// EVERY consumer uses THESE, never a per-file copy: this is a
// whole-program-scope language, so two files declaring the same top-level
// macro name collide, and the failure mode is a wildly misleading unrelated
// panic, not a clean duplicate-name error. One `pub` definition here.
pub def derive_yaml_serialize_meta (info : TypeInfo) : List MetaDecl :=
    derive_serialize_meta "yaml" (Expr.e_var "Yaml") info

defmacro derive_yaml_serialize T := decls {
    reflect_type_info! T derive_yaml_serialize_meta
}

pub def derive_yaml_deserialize_meta (info : TypeInfo) : List MetaDecl :=
    derive_deserialize_meta "yaml" (Expr.e_var "Yaml") info

defmacro derive_yaml_deserialize T := decls {
    reflect_type_info! T derive_yaml_deserialize_meta
}
