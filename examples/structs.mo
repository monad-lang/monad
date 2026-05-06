use io
open IO

// Basic struct definition
struct Point {
    x: I64,
    y: I64,
}

// Struct with default field value
struct Rect {
    w: I64,
    h: I64 := 100,
}

// Struct with linear field (must be consumed exactly once)
struct Buffer {
    !data: String,
    size: I64,
}

@[test]
def test_struct_construct_and_match : Bool :=
    let pt : Point := { x := 1, y := 2 } in
    match pt {
        mk x y => x + y == 3
    }

@[test]
def test_struct_default_value : Bool :=
    let r : Rect := { w := 50 } in
    match r {
        mk w h => h == 100
    }

@[test]
def test_struct_update : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { p1 with x := 10 } in
    match p2 {
        mk x y => x == 10 && y == 2
    }

@[test]
def test_struct_linear : Bool :=
    let buf : Buffer := { data := "hi", size := 2 } in
    match buf {
        mk data size => String.length data == size
    }

@[test]
def test_struct_wildcard : Bool :=
    let pt : Point := { x := 99, y := 0 } in
    match pt {
        mk x _ => x == 99
    }

@[test]
def test_struct_field_eq : Bool :=
    let pt : Point := { x := 5, y := 5 } in
    match pt {
        mk x y => x == y
    }

// Do notation works with a single expression
def print_point (pt : Point) : IO Unit {
    match pt {
        mk x y => println ("(" ++ I64.to_string x ++ ", " ++ I64.to_string y ++ ")")
    }
}

def main (args: List String) : IO Unit :=
    let p1 : Point := { x := 10, y := 20 } in
    let p2 : Point := { p1 with x := 30 } in
    print_point p1
    >>= fn _ =>
    print_point p2
