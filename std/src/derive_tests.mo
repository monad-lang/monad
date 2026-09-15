/// End-to-end tests for `std/derive.mo`'s `derive_lens`/`derive_debug`/
/// `derive_beq`/`derive_bord` — run through the real `cargo run -- test
/// std/` pipeline (elaborate -> expand_macros -> type check -> eval), the
/// same way `init/optics_tests.mo` exercises hand-written lenses.
/// `derive_lens`/`derive_debug`/`derive_beq`/`derive_bord`/`lens_field`
/// are `use`d here (not redefined), proving decl-gen macros now resolve
/// cross-module.

use std.derive {derive_lens, derive_debug, derive_beq, derive_bord}
use init.optics {Lens, over, set, view}
use std.debug {Debug}

struct Point {
    x : I64,
    y : I64,
}

derive_lens! Point
derive_debug! Point
derive_beq! Point
derive_bord! Point

#[test]
def test_derive_lens_view_x : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    view Point.x pt == 3

#[test]
def test_derive_lens_view_y : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    view Point.y pt == 5

#[test]
def test_derive_lens_set_x : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := set Point.x 10 pt in
    view Point.x pt2 == 10 && view Point.y pt2 == 5

#[test]
def test_derive_lens_set_y : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := set Point.y 20 pt in
    view Point.x pt2 == 3 && view Point.y pt2 == 20

#[test]
def test_derive_lens_over_x : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := over Point.x (fn v => v + 1) pt in
    view Point.x pt2 == 4 && view Point.y pt2 == 5

#[test]
def test_derive_lens_set_then_view_roundtrip : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    view Point.x (set Point.x 42 pt) == 42

#[test]
def test_derive_debug_struct : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    Debug.debug pt == "Point { x: 3, y: 5 }"

#[test]
def test_derive_beq_equal : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 3, y := 5 } in
    p1 == p2

#[test]
def test_derive_beq_not_equal_first_field : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 4, y := 5 } in
    Bool.not (p1 == p2)

#[test]
def test_derive_beq_not_equal_second_field : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 3, y := 6 } in
    Bool.not (p1 == p2)

#[test]
def test_derive_bord_lt_first_field : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 4, y := 1 } in
    p1 < p2 && Bool.not (p2 < p1)

#[test]
def test_derive_bord_lt_falls_through_to_second_field : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 3, y := 6 } in
    p1 < p2 && p2 > p1

#[test]
def test_derive_bord_equal_is_neither_lt_nor_gt : Bool :=
    let p1 : Point := { x := 3, y := 5 } in
    let p2 : Point := { x := 3, y := 5 } in
    Bool.not (p1 < p2) && Bool.not (p1 > p2)

/// A single-constructor `type` (not `struct`) should also derive lenses —
/// `derive_lens` only requires exactly one constructor, not the `struct`
/// keyword specifically.
type Duo {
    mk (first : I64) (second : I64),
}

derive_lens! Duo

#[test]
def test_derive_lens_on_type_not_struct : Bool :=
    let p : Duo := Duo.mk 1 2 in
    view Duo.first p == 1 && view Duo.second p == 2

/// `derive_debug` on a multi-constructor `type` — one match arm (and one
/// `TypeName::CtorName` label) per constructor, including a zero-field one.
type Suit {
    hearts,
    spades,
    number (rank : I64),
}

derive_debug! Suit
derive_beq! Suit
derive_bord! Suit

#[test]
def test_derive_debug_zero_field_constructor : Bool :=
    Debug.debug Suit.hearts == "Suit::hearts"

#[test]
def test_derive_debug_multi_field_constructor : Bool :=
    Debug.debug (Suit.number 7) == "Suit::number { rank: 7 }"

#[test]
def test_derive_beq_same_constructor_zero_field : Bool :=
    Suit.hearts == Suit.hearts

#[test]
def test_derive_beq_same_constructor_with_field : Bool :=
    Suit.number 7 == Suit.number 7 && Bool.not (Suit.number 7 == Suit.number 8)

#[test]
def test_derive_beq_different_constructors : Bool :=
    Bool.not (Suit.hearts == Suit.spades)

/// Constructor declaration order is the sort order: hearts < spades < number.
#[test]
def test_derive_bord_constructor_declaration_order : Bool :=
    Suit.hearts < Suit.spades && Suit.spades < Suit.number 0 && Suit.number 0 > Suit.hearts

#[test]
def test_derive_bord_same_constructor_field_order : Bool :=
    Suit.number 3 < Suit.number 7 && Suit.number 7 > Suit.number 3

/// Regression test for `derive_bord`'s field-priority comparison order (see
/// `std/derive.mo`'s `lt_chain`/`gt_chain`): the FIRST-declared field that
/// disagrees must decide the whole comparison, not the last. `a`/`b`
/// disagree in opposite directions here (`a: 1 < 2` but `c: 100 > 1`) — if
/// a later field wrongly overrode an earlier decision, `p1 < p2` would come
/// out false.
struct Triple {
    a : I64,
    b : I64,
    c : I64,
}

derive_bord! Triple

#[test]
def test_derive_bord_first_deciding_field_wins_lexicographic_priority : Bool :=
    let p1 : Triple := { a := 1, b := 5, c := 100 } in
    let p2 : Triple := { a := 2, b := 5, c := 1 } in
    p1 < p2 && p2 > p1 && Bool.not (p1 > p2) && Bool.not (p2 < p1)
