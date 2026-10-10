/// `motes/serde`'s `Serializer`/`Deserializer` instances for `Json` --
/// the backend `derive_serialize_meta`/`derive_deserialize_meta`-
/// generated code (in a mote that depends on BOTH `json` and `serde`,
/// e.g. `motes/shuttle`) actually calls through, via the
/// `json_ser_*`/`json_de_*` wrapper functions below.
///
/// Deliberately separate from `class Json.Serializer`/`Json.Deserializer`
/// in `json.mo` -- those are a DIFFERENT, still-useful abstraction
/// ("serialize a value of type S to Json", one instance per VALUE type:
/// `Bool`, `I64`, `String`, `Person`, `List A`) from `serde`'s
/// `Serializer`/`Deserializer` ("build/read a Json value from primitive
/// pieces", exactly one instance total, indexed by the FORMAT). The two
/// are not redundant; `json.mo`'s stay as the direct hand-written-
/// instance API, this mote's `serde` instance is what the generic derive
/// mechanism needs.
use serde::format {Serializer, Deserializer}
use std::map {}
use json::json {
    Json, Json.make_null, Json.make_bool, Json.make_num_int, Json.make_str,
    Json.make_array, Json.make_object, Json.get_bool, Json.get_num,
    Json.get_num_i64, Json.get_str, Json.get_array, Json.get_object,
    Json.object_get,
}

def json_pairs_to_object (fields : List (Pair String Json)) (acc : BTreeMap String Json) : BTreeMap String Json :=
    match fields {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair k v => json_pairs_to_object rest (Map.insert k v acc)
            }
    }

instance Serializer Json {
    def ser_null : Json := Json.make_null
    def ser_bool (b : Bool) : Json := Json.make_bool b
    def ser_int (i : I64) : Json := Json.make_num_int i
    def ser_string (s : String) : Json := Json.make_str s
    def ser_list (xs : List Json) : Json := Json.make_array xs
    def ser_object (fields : List (Pair String Json)) : Json :=
        Json.make_object (json_pairs_to_object fields BTreeMap.empty)
}

instance Deserializer Json {
    def de_is_null (d : Json) : Bool :=
        match d { Json.null => true, _ => false }
    def de_get_bool (d : Json) : Result String Bool := Json.get_bool d
    def de_get_int (d : Json) : Result String I64 := Json.get_num_i64 (Json.get_num d)
    def de_get_string (d : Json) : Result String String := Json.get_str d
    def de_get_list (d : Json) : Result String (List Json) := Json.get_array d
    def de_get_field (d : Json) (name : String) : Result String (Option Json) :=
        match Json.get_object d {
            Result.err e => Result.err e,
            Result.ok obj => Result.ok (Json.object_get name obj),
        }
}

// `derive.mo`'s generated code calls these, never `Serializer.*`/
// `Deserializer.*` directly -- see `motes/serde/src/format.mo`'s note
// on why (a macro-REIFIED bare top-level `d_def` calling a class method
// directly fails at run time with `unresolved global`, even though the
// identical call, normally parsed, dispatches fine).
pub def json_ser_null : Json := Serializer.ser_null
pub def json_ser_bool (b : Bool) : Json := Serializer.ser_bool b
pub def json_ser_int (i : I64) : Json := Serializer.ser_int i
pub def json_ser_string (s : String) : Json := Serializer.ser_string s
pub def json_ser_list (xs : List Json) : Json := Serializer.ser_list xs
pub def json_ser_object (fields : List (Pair String Json)) : Json := Serializer.ser_object fields

pub def json_de_is_null (d : Json) : Bool := Deserializer.de_is_null d
pub def json_de_get_bool (d : Json) : Result String Bool := Deserializer.de_get_bool d
pub def json_de_get_int (d : Json) : Result String I64 := Deserializer.de_get_int d
pub def json_de_get_string (d : Json) : Result String String := Deserializer.de_get_string d
pub def json_de_get_list (d : Json) : Result String (List Json) := Deserializer.de_get_list d
pub def json_de_get_field (d : Json) (name : String) : Result String (Option Json) := Deserializer.de_get_field d name
