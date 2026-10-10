use serde::derive {derive_serialize_meta, derive_deserialize_meta}
use init::meta {TypeInfo, Decl, Expr}
use serde::tests::toy_format {Toy}
use std::list {List.length}

// A top-level `def`/`defmacro` with a bare `{ field := val }` struct
// literal in its body fails to type-check -- "cannot infer the type of
// `{ .. }`" -- in any file that ALSO contains a `reflect_type_info!`
// macro invocation, EVEN with an explicit `def x : T := { .. }` return
// annotation right there (probed directly: reproduces with a trivial
// `derive_trivial! Point` macro and nothing else). A `let p : T := { .. }
// in ...` INSIDE a function body (here, every `#[test]`) does not hit
// this -- that's why every sample value below is a local `let`, not a
// shared top-level `def`.

struct Point {
    x : I64,
    y : I64,
}

def derive_toy_serialize_meta (info : TypeInfo) : List Decl :=
    derive_serialize_meta "toy" (Expr.e_var "Toy") info

defmacro derive_toy_serialize T := decls {
    reflect_type_info! T derive_toy_serialize_meta
}

def derive_toy_deserialize_meta (info : TypeInfo) : List Decl :=
    derive_deserialize_meta "toy" (Expr.e_var "Toy") info

defmacro derive_toy_deserialize T := decls {
    reflect_type_info! T derive_toy_deserialize_meta
}

derive_toy_serialize! Point
derive_toy_deserialize! Point

struct Tagged {
    name : String,
    nickname : Option String,
    scores : List I64,
    origin : Point,
}

derive_toy_serialize! Tagged
derive_toy_deserialize! Tagged

def toy_object_lookup (fields : List (Pair String Toy)) (name : String) : Option Toy :=
    match fields {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair k v => if String.beq k name then Option.some v else toy_object_lookup rest name
            }
    }

def toy_int_at (fields : List (Pair String Toy)) (name : String) (want : I64) : Bool :=
    match toy_object_lookup fields name {
        Option.some t =>
            match t {
                Toy.t_int n => n == want,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_derive_serialize_point_fields : Bool :=
    let p : Point := { x := 3, y := 4 } in
    match Point.serialize_toy p {
        Toy.t_object fields => toy_int_at fields "x" 3 && toy_int_at fields "y" 4,
        _ => false,
    }

#[test]
def test_derive_serialize_string_field : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.some "nick", scores := [1, 2, 3], origin := origin } in
    match Tagged.serialize_toy t {
        Toy.t_object fields =>
            match toy_object_lookup fields "name" {
                Option.some tv =>
                    match tv {
                        Toy.t_string s => String.beq s "a",
                        _ => false,
                    },
                Option.none => false,
            },
        _ => false,
    }

#[test]
def test_derive_serialize_option_some_field : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.some "nick", scores := [1, 2, 3], origin := origin } in
    match Tagged.serialize_toy t {
        Toy.t_object fields =>
            match toy_object_lookup fields "nickname" {
                Option.some tv =>
                    match tv {
                        Toy.t_string s => String.beq s "nick",
                        _ => false,
                    },
                Option.none => false,
            },
        _ => false,
    }

#[test]
def test_derive_serialize_option_none_field_is_null : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.none, scores := [1, 2, 3], origin := origin } in
    match Tagged.serialize_toy t {
        Toy.t_object fields =>
            match toy_object_lookup fields "nickname" {
                Option.some tv =>
                    match tv {
                        Toy.t_null => true,
                        _ => false,
                    },
                Option.none => false,
            },
        _ => false,
    }

def toy_list_length (fields : List (Pair String Toy)) (name : String) : I64 :=
    match toy_object_lookup fields name {
        Option.some t =>
            match t {
                Toy.t_list xs => List.length xs,
                _ => -1,
            },
        Option.none => -1,
    }

#[test]
def test_derive_serialize_list_field : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.some "nick", scores := [1, 2, 3], origin := origin } in
    match Tagged.serialize_toy t {
        Toy.t_object fields => toy_list_length fields "scores" == 3,
        _ => false,
    }

#[test]
def test_derive_serialize_nested_struct_field : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.some "nick", scores := [1, 2, 3], origin := origin } in
    match Tagged.serialize_toy t {
        Toy.t_object fields =>
            match toy_object_lookup fields "origin" {
                Option.some tv =>
                    match tv {
                        Toy.t_object origin_fields => toy_int_at origin_fields "x" 1 && toy_int_at origin_fields "y" 2,
                        _ => false,
                    },
                Option.none => false,
            },
        _ => false,
    }

#[test]
def test_derive_deserialize_roundtrip_point : Bool :=
    let p : Point := { x := 5, y := 6 } in
    match Point.deserialize_toy (Point.serialize_toy p) {
        Result.ok p2 =>
            match p2 { Point.mk x y => x == 5 && y == 6 },
        Result.err _ => false,
    }

#[test]
def test_derive_deserialize_roundtrip_tagged_with_nickname : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.some "nick", scores := [1, 2, 3], origin := origin } in
    match Tagged.deserialize_toy (Tagged.serialize_toy t) {
        Result.ok t2 =>
            match t2 {
                Tagged.mk name nickname scores origin2 =>
                    String.beq name "a" &&
                    (match nickname { Option.some n => String.beq n "nick", Option.none => false }) &&
                    List.length scores == 3
            },
        Result.err _ => false,
    }

#[test]
def test_derive_deserialize_roundtrip_tagged_without_nickname : Bool :=
    let origin : Point := { x := 1, y := 2 } in
    let t : Tagged := { name := "a", nickname := Option.none, scores := [1, 2, 3], origin := origin } in
    match Tagged.deserialize_toy (Tagged.serialize_toy t) {
        Result.ok t2 =>
            match t2 {
                Tagged.mk name nickname scores origin2 =>
                    match nickname { Option.some _ => false, Option.none => true }
            },
        Result.err _ => false,
    }

#[test]
def test_derive_deserialize_missing_required_field_is_error : Bool :=
    let obj : Toy := Toy.t_object [Pair.pair "y" (Toy.t_int 4)] in
    match Point.deserialize_toy obj {
        Result.ok _ => false,
        Result.err _ => true,
    }

struct WithDefault {
    name : String,
    include_pattern : String := "*",
}

derive_toy_serialize! WithDefault
derive_toy_deserialize! WithDefault

#[test]
def test_derive_deserialize_missing_defaulted_field_uses_default : Bool :=
    let obj : Toy := Toy.t_object [Pair.pair "name" (Toy.t_string "foo")] in
    match WithDefault.deserialize_toy obj {
        Result.ok w =>
            match w { WithDefault.mk name pattern => String.beq pattern "*" },
        Result.err _ => false,
    }

#[test]
def test_derive_deserialize_present_defaulted_field_overrides_default : Bool :=
    let obj : Toy := Toy.t_object [Pair.pair "name" (Toy.t_string "foo"), Pair.pair "include_pattern" (Toy.t_string "*.mo")] in
    match WithDefault.deserialize_toy obj {
        Result.ok w =>
            match w { WithDefault.mk name pattern => String.beq pattern "*.mo" },
        Result.err _ => false,
    }
