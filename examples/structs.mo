// TODO: see the matching TODO in examples/do_block.mo — `IO`/`println`
// are used below (via the companion `open IO {println}`, which is
// unaffected) but deliberately NOT listed in THIS `use`; naming anything
// here breaks implicit `Monad IO` instance lookup at runtime.
use io {}
open IO {println}

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

#[test]
def test_struct_construct_and_match : Bool :=
    let pt : Point := { x := 1, y := 2 } in
    match pt {
        mk x y => x + y == 3
    }

#[test]
def test_struct_default_value : Bool :=
    let r : Rect := { w := 50 } in
    match r {
        mk w h => h == 100
    }

#[test]
def test_struct_update : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { p1 with x := 10 } in
    match p2 {
        mk x y => x == 10 && y == 2
    }

#[test]
def test_struct_linear : Bool :=
    let buf : Buffer := { data := "hi", size := 2 } in
    match buf {
        mk data size => String.length data == size
    }

#[test]
def test_struct_wildcard : Bool :=
    let pt : Point := { x := 99, y := 0 } in
    match pt {
        mk x _ => x == 99
    }

#[test]
def test_struct_field_eq : Bool :=
    let pt : Point := { x := 5, y := 5 } in
    match pt {
        mk x y => x == y
    }

// Named-field construction sugar: `NAME { field := value, ... }` --
// order-independent keyword arguments, matched against NAME's own
// declared parameter names -- for both an ordinary `type`'s constructors
// and a `def`'s own parameters (the latter declarable as one brace block
// too, an alternative spelling of the usual separate parenthesized
// groups).
type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64),
}

def area (s : Shape) : I64 :=
    match s {
        circle r => r * r,
        rectangle w h => w * h
    }

// A def's own parameter list, written as one brace block instead of
// separate `(name : Type)` groups -- `scale` in the paren spelling would
// be `def scale (factor : I64) (p : I64) : I64 := ...`. `factor`'s `:=`
// default only works in this brace form; the paren form has none.
def scale {factor : I64 := 2, p : I64} : I64 := factor * p

#[test]
def test_named_call_constructor_reordered : Bool :=
    // `rectangle`'s own declared order is (width, height) -- given here
    // in the opposite order, matched by field name, not position.
    let r : Shape := Shape.rectangle { height := 3, width := 4 } in
    area r == 12

#[test]
def test_named_call_constructor_single_field : Bool :=
    let c : Shape := Shape.circle { radius := 5 } in
    area c == 25

#[test]
def test_named_call_def_target : Bool :=
    // `scale`'s own params (factor, p) given out of declared order.
    scale { p := 4, factor := 3 } == 12

#[test]
def test_named_call_def_target_uses_declared_default : Bool :=
    // `factor` omitted entirely -- falls back to its own `:= 2` default.
    scale { p := 4 } == 8

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
