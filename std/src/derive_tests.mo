/// End-to-end tests for `std/derive.mo`'s `derive_lens`/`derive_debug`/
/// `derive_beq`/`derive_bord`/`derive_copy`/`derive_clone` — run through the
/// real `cargo run -- test std/` pipeline (elaborate -> expand_macros -> type
/// check -> eval), the same way `init/optics_tests.mo` exercises hand-written
/// lenses. The `derive_*` macros are `use`d here (not redefined), proving
/// decl-gen macros resolve cross-module.

use lib::derive {
    derive_bord, derive_beq, derive_clone, derive_copy, derive_debug, derive_lens,
}
use init::optics {Lens, over, set, view}
use lib::debug {Debug}

struct Point {
    x : I64,
    y : I64,
}

derive_lens! Point
derive_debug! Point
derive_beq! Point
derive_bord! Point

/// `over` rebuilds the whole structure from a read of it, so it declares
/// `[Copy S]` and the checker enforces it at the call site. A derived lens
/// does not derive the instance: two `I64`s are a plain field-wise duplicate.
instance Copy Point {
    def copy (pt : Point) : Pair Point Point :=
        match pt {
            { x, y } =>
                let one : Point := { x := x, y := y } in
                let two : Point := { x := x, y := y } in
                Pair.pair one two,
        }
}

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

instance Copy Duo {
    def copy (d : Duo) : Pair Duo Duo := Pair.pair d d
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

instance Copy Triple {
    def copy (t : Triple) : Pair Triple Triple := Pair.pair t t
}

derive_bord! Triple

#[test]
def test_derive_bord_first_deciding_field_wins_lexicographic_priority : Bool :=
    let p1 : Triple := { a := 1, b := 5, c := 100 } in
    let p2 : Triple := { a := 2, b := 5, c := 1 } in
    p1 < p2 && p2 > p1 && Bool.not (p1 > p2) && Bool.not (p2 < p1)

/// `lte`/`gte` are derived as `not gt` / `not lt`, so they must agree with
/// `lt`/`gt` — including the both-equal case that neither `<` nor `>`
/// decides.
#[test]
def test_derive_bord_lte_gte_agree_with_lt_gt : Bool :=
    let p1 : Triple := { a := 1, b := 5, c := 100 } in
    let p2 : Triple := { a := 2, b := 5, c := 1 } in
    p1 <= p2 && p2 >= p1 && Bool.not (p2 <= p1) && Bool.not (p1 >= p2)
        && p1 <= p1 && p1 >= p1

/// Constructor declaration order must decide `<=`/`>=` the same way it
/// decides `<`/`>`.
#[test]
def test_derive_bord_lte_gte_constructor_order : Bool :=
    Suit.hearts <= Suit.spades && Suit.spades >= Suit.hearts
        && Bool.not (Suit.spades <= Suit.hearts)
        && Bool.not (Suit.hearts >= Suit.spades)
        && Suit.number 3 <= Suit.number 3

// ─── Copy / Clone ─────────────────────────────────────────────────────

/// `#[derive Copy Clone]` (the attribute, not a direct `derive_*!` call) on a
/// monomorphic struct. A derived `Copy` is what lets the affine rule use a
/// binder twice; the hand-written instances above never exercised that path.
#[derive Copy Clone]
struct Vec2 {
    x : I64,
    y : I64,
}

/// A derived multi-constructor sum, including a zero-field constructor.
#[derive Copy Clone]
type Shape {
    dot,
    seg (len : I64),
}

/// A recursive type: the derived instances must resolve `Copy Chain`/
/// `Clone Chain` while the instances are being checked. The constructors are
/// deliberately NOT called `nil`/`cons` — those collide with `List`'s bare
/// names in a pattern.
#[derive Copy Clone]
type Chain {
    chain_end,
    chain_link (head : I64) (tail : Chain),
}

/// Hygiene: the generated `copy` binders for field 0 would be `cp_a_0`/
/// `cp_b_0`, so a field literally named `cp_a_0` must not be shadowed.
#[derive Copy]
struct Weird {
    cp_a_0 : I64,
    x : I64,
}

/// The round-trip tests go through `Copy.dup` — an ordinary constrained def —
/// because a direct `Copy.copy x` falls back to the class's abstract signature
/// for a `#[derive]`'d instance (the documented promotion gap).
#[test]
def test_derive_copy_grants_omega : Bool :=
    let v : Vec2 := { x := 3, y := 5 } in
    let a : Vec2 := v in
    let b : Vec2 := v in
    I64.beq a.x b.x && I64.beq a.y 5

#[test]
def test_derive_copy_roundtrip : Bool :=
    let v : Vec2 := { x := 3, y := 5 } in
    let p : Pair Vec2 Vec2 := Copy.dup v in
    match p {
        Pair.pair a b =>
            match a {
                Vec2.mk ax ay =>
                    match b { Vec2.mk bx by => I64.beq ax bx && I64.beq ay 5 && I64.beq by 5 },
            },
    }

#[test]
def test_derive_copy_zero_field_ctor : Bool :=
    let d : Shape := Shape.dot in
    match Copy.dup d {
        Pair.pair a b =>
            match a {
                Shape.dot => match b { Shape.dot => true, Shape.seg _ => false },
                Shape.seg _ => false,
            },
    }

#[test]
def test_derive_copy_sum_ctor : Bool :=
    let s : Shape := Shape.seg 7 in
    match Copy.copy s {
        Pair.pair a b =>
            match a {
                Shape.seg n =>
                    match b { Shape.seg m => I64.beq n m, Shape.dot => false },
                Shape.dot => false,
            },
    }

#[test]
def test_derive_copy_recursive_type : Bool :=
    let c : Chain := Chain.chain_link 1 (Chain.chain_link 2 Chain.chain_end) in
    match Copy.dup c {
        Pair.pair a b =>
            match a {
                Chain.chain_link x xs =>
                    match b {
                        Chain.chain_link y ys =>
                            match xs {
                                Chain.chain_link h _ => I64.beq x y && I64.beq h 2,
                                Chain.chain_end => false,
                            },
                        Chain.chain_end => false,
                    },
                Chain.chain_end => false,
            },
    }

#[test]
def test_derive_copy_binder_hygiene : Bool :=
    let w : Weird := { cp_a_0 := 1, x := 2 } in
    match Copy.dup w {
        Pair.pair a b =>
            match a {
                Weird.mk ca cx => match b { Weird.mk cb cy => I64.beq ca 1 && I64.beq cy 2 },
            },
    }

#[test]
def test_derive_clone_struct_leaves_source_usable : Bool :=
    let v : Vec2 := { x := 3, y := 5 } in
    let c : Vec2 := Clone.clone (Shared.of v) in
    I64.beq c.x 3 && I64.beq c.y 5 && I64.beq v.x 3

#[test]
def test_derive_clone_zero_field_ctor : Bool :=
    let d : Shape := Shape.dot in
    match Clone.clone (Shared.of d) {
        Shape.dot => true,
        Shape.seg _ => false,
    }

#[test]
def test_derive_clone_sum_ctor : Bool :=
    match Clone.clone (Shared.of (Shape.seg 7)) {
        Shape.seg n => I64.beq n 7,
        Shape.dot => false,
    }

#[test]
def test_derive_clone_recursive_type : Bool :=
    let c : Chain := Chain.chain_link 1 (Chain.chain_link 2 Chain.chain_end) in
    match Clone.clone (Shared.of c) {
        Chain.chain_link x xs =>
            match xs {
                Chain.chain_link h _ => I64.beq x 1 && I64.beq h 2,
                Chain.chain_end => false,
            },
        Chain.chain_end => false,
    }
