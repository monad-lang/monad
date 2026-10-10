use json::json {Json}
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

struct Point3 {
    x : I64,
    name : String,
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
