use serde::format {Serializer, Deserializer}

/// A toy format, in its own file/module -- just enough structure for
/// `derive_tests.mo` to assert against without pulling in `motes/json`.
pub type Toy {
    t_null,
    t_bool (b : Bool),
    t_int (i : I64),
    t_string (s : String),
    t_list (xs : List Toy),
    t_object (fields : List (Pair String Toy)),
}

pub instance Serializer Toy {
    def ser_null : Toy := Toy.t_null
    def ser_bool (b : Bool) : Toy := Toy.t_bool b
    def ser_int (i : I64) : Toy := Toy.t_int i
    def ser_string (s : String) : Toy := Toy.t_string s
    def ser_list (xs : List Toy) : Toy := Toy.t_list xs
    def ser_object (fields : List (Pair String Toy)) : Toy := Toy.t_object fields
}

pub instance Deserializer Toy {
    def de_is_null (d : Toy) : Bool :=
        match d { Toy.t_null => true, _ => false }
    def de_get_bool (d : Toy) : Result String Bool :=
        match d { Toy.t_bool b => Result.ok b, _ => Result.err "expected a bool" }
    def de_get_int (d : Toy) : Result String I64 :=
        match d { Toy.t_int i => Result.ok i, _ => Result.err "expected an int" }
    def de_get_string (d : Toy) : Result String String :=
        match d { Toy.t_string s => Result.ok s, _ => Result.err "expected a string" }
    def de_get_list (d : Toy) : Result String (List Toy) :=
        match d { Toy.t_list xs => Result.ok xs, _ => Result.err "expected a list" }
    def de_get_field (d : Toy) (name : String) : Result String (Option Toy) :=
        match d { Toy.t_object fields => Result.ok (toy_field_lookup fields name), _ => Result.err "expected an object" }
}

def toy_field_lookup (fields : List (Pair String Toy)) (name : String) : Option Toy :=
    match fields {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair k v => if String.beq k name then Option.some v else toy_field_lookup rest name
            }
    }

// `derive.mo`'s generated code calls these, never `Serializer.*`/
// `Deserializer.*` directly -- see `format.mo`'s note on why.
pub def toy_ser_null : Toy := Serializer.ser_null
pub def toy_ser_bool (b : Bool) : Toy := Serializer.ser_bool b
pub def toy_ser_int (i : I64) : Toy := Serializer.ser_int i
pub def toy_ser_string (s : String) : Toy := Serializer.ser_string s
pub def toy_ser_list (xs : List Toy) : Toy := Serializer.ser_list xs
pub def toy_ser_object (fields : List (Pair String Toy)) : Toy := Serializer.ser_object fields

pub def toy_de_is_null (d : Toy) : Bool := Deserializer.de_is_null d
pub def toy_de_get_bool (d : Toy) : Result String Bool := Deserializer.de_get_bool d
pub def toy_de_get_int (d : Toy) : Result String I64 := Deserializer.de_get_int d
pub def toy_de_get_string (d : Toy) : Result String String := Deserializer.de_get_string d
pub def toy_de_get_list (d : Toy) : Result String (List Toy) := Deserializer.de_get_list d
pub def toy_de_get_field (d : Toy) (name : String) : Result String (Option Toy) := Deserializer.de_get_field d name
