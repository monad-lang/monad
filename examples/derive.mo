/// Derive Macros Example — BEq, BOrd, Debug, and Lens via `#[derive ...]`
///
/// Demonstrates deriving structural equality, ordering, a rust-style debug
/// representation, and per-field lenses for a struct and a plain
/// multi-constructor `type`, all with a single `#[derive ...]` attribute
/// per declaration. Each derive is a `.mo`-authored macro in
/// `std/derive.mo`, built on a handful of reflection intrinsics in the
/// compiler itself — see that file's doc comments for the full design.

// `derive_beq`/`derive_bord`/`derive_debug`/`derive_lens` are only ever
// invoked via the `#[derive BEq BOrd Debug Lens]` attribute below (macro
// dispatch by name string, not an ordinary term reference), so the
// checker's "unused import" analysis flags this line as a false
// positive — confirmed by removing it: `#[derive BEq]` then fails with
// "macro `derive_beq` not found". Keep this import despite the warning.
use std.derive {derive_beq, derive_bord, derive_debug, derive_lens}
use init.optics {Lens, set, view}
use std.debug {Debug}

#[derive BEq BOrd Debug Lens]
struct Point {
    x : I64,
    y : I64,
}

#[test]
def test_point_equality : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { x := 1, y := 2 } in
    let p3 : Point := { x := 1, y := 3 } in
    p1 == p2 && Bool.not (p1 == p3)

#[test]
def test_point_ordering : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { x := 1, y := 3 } in
    p1 < p2 && p2 > p1

#[test]
def test_point_debug : Bool :=
    let p : Point := { x := 1, y := 2 } in
    Debug.debug p == "Point { x: 1, y: 2 }"

#[test]
def test_point_lens : Bool :=
    let p : Point := { x := 1, y := 2 } in
    view Point.x p == 1 && view Point.y (set Point.y 9 p) == 9

/// Derives work on multi-constructor `type`s too — `BEq`/`BOrd`/`Debug`
/// cover every constructor; `Lens` is deliberately not requested here,
/// since a lens focuses on exactly one field of exactly one shape and
/// wouldn't apply to a sum type (see `init.optics`'s `Prism` instead).
#[derive BEq BOrd Debug]
type Suit {
    hearts,
    spades,
    number (rank : I64),
}

#[test]
def test_suit_equality : Bool :=
    Suit.number 7 == Suit.number 7 && Bool.not (Suit.hearts == Suit.spades)

#[test]
def test_suit_ordering_follows_declaration_order : Bool :=
    Suit.hearts < Suit.spades && Suit.spades < Suit.number 0

#[test]
def test_suit_debug : Bool :=
    Debug.debug Suit.hearts == "Suit::hearts" && Debug.debug (Suit.number 7) == "Suit::number { rank: 7 }"
