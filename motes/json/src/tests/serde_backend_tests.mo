use serde::derive {derive_serialize_meta, derive_deserialize_meta}
use init::meta {TypeInfo, Decl, Expr}
use json::json {Json}
use json::serde_backend {}

struct Point3 {
    x : I64,
    name : String,
}

def derive_json_serialize_meta (info : TypeInfo) : List Decl :=
    derive_serialize_meta "json" (Expr.e_var "Json") info

defmacro derive_json_serialize T := decls {
    reflect_type_info! T derive_json_serialize_meta
}

def derive_json_deserialize_meta (info : TypeInfo) : List Decl :=
    derive_deserialize_meta "json" (Expr.e_var "Json") info

defmacro derive_json_deserialize T := decls {
    reflect_type_info! T derive_json_deserialize_meta
}

derive_json_serialize! Point3
derive_json_deserialize! Point3

#[test]
def test_derive_json_serialize_shape : Bool :=
    let p : Point3 := { x := 5, name := "hi" } in
    Json.to_string (Point3.serialize_json p) == "{\"name\":\"hi\",\"x\":5}"

#[test]
def test_derive_json_roundtrip : Bool :=
    let p : Point3 := { x := 5, name := "hi" } in
    match Point3.deserialize_json (Point3.serialize_json p) {
        Result.ok p2 =>
            match p2 { Point3.mk x name => x == 5 && String.beq name "hi" },
        Result.err _ => false,
    }

struct WithRawJson {
    label : String,
    payload : Json,
}

derive_json_serialize! WithRawJson
derive_json_deserialize! WithRawJson

#[test]
def test_derive_json_identity_passthrough_field : Bool :=
    let inner : Json := Json.array [Json.num (Json.Number.int 1), Json.str "x"] in
    let w : WithRawJson := { label := "x", payload := inner } in
    match WithRawJson.deserialize_json (WithRawJson.serialize_json w) {
        Result.ok w2 =>
            match w2 { WithRawJson.mk label payload => Json.beq payload inner },
        Result.err _ => false,
    }
