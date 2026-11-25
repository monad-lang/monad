/// Runtime tests for `init/src/linked.mo`.
///
/// Separate from `linked.mo` for the reason AGENTS.md gives: a `#[test]` in a
/// file pulled in by a re-export hub is undiscoverable, and `init/src/linked.mo`
/// is imported by name (`use init::linked {...}`), not re-exported.
///
/// These pin the pointer-swapping operations on a real runtime: the node
/// handles are reused in place, every cursor is consumed exactly once, and the
/// values come back in the order the relink intends. The *type-level* half
/// (no `Copy` of a `Link`, no two cursors, no `Shared`) is the checker's, and is
/// exercised by the same defs failing to compile if the rule is weakened.
///
/// Every operation is a pure linear mutation, so these are plain `let` chains.
/// The three lists built from an EMPTY list still annotate their binder
/// (`let l : Link I64 := ...`): `List.empty` gives inference nothing to solve
/// `A` from.
use init::linked {Link, Linked.from_list, Linked.length, Linked.reverse, Linked.swap_adjacent, Linked.to_list}

/// `[n, n-1, ..., 1]` — a descending list, so `reverse` has visible work.
#[terminating] // an index walk, not a structural one
def upto (n : I64) : List I64 :=
    if I64.lt n 1i64 then List.empty else List.cons n (upto (I64.sub n 1i64))

def same_i64s (xs : List I64) (ys : List I64) : Bool :=
    match xs {
        List.empty =>
            match ys {
                List.empty => true,
                List.cons _ _ => false,
            },
        List.cons x rest =>
            match ys {
                List.empty => false,
                List.cons y yrest => I64.beq x y && same_i64s rest yrest,
            },
    }

#[test]
def test_linked_roundtrip : Bool :=
    let l := Linked.from_list (upto 5i64) in
    let xs := Linked.to_list l in
    same_i64s xs (upto 5i64)

#[test]
def test_linked_empty_roundtrip : Bool :=
    let l : Link I64 := Linked.from_list List.empty in
    let xs := Linked.to_list l in
    same_i64s xs List.empty

#[test]
def test_linked_length : Bool :=
    let l := Linked.from_list (upto 7i64) in
    let n := Linked.length l in
    I64.beq n 7i64

#[test]
def test_linked_length_of_empty_is_zero : Bool :=
    let l : Link I64 := Linked.from_list List.empty in
    let n := Linked.length l in
    I64.beq n 0i64

// ── Pointer swapping ────────────────────────────────────────────────

#[test]
def test_linked_reverse_relinks_in_place : Bool :=
    let l := Linked.from_list (upto 4i64) in
    let r := Linked.reverse l in
    let xs := Linked.to_list r in
    same_i64s xs [1i64, 2i64, 3i64, 4i64]

#[test]
def test_linked_reverse_of_empty_is_empty : Bool :=
    let l : Link I64 := Linked.from_list List.empty in
    let r := Linked.reverse l in
    let xs := Linked.to_list r in
    same_i64s xs List.empty

#[test]
def test_linked_reverse_of_one_is_itself : Bool :=
    let l := Linked.from_list (upto 1i64) in
    let r := Linked.reverse l in
    let xs := Linked.to_list r in
    same_i64s xs [1i64]

/// The link swap is an involution: reversing twice is the identity, on a list
/// long enough that every node is relinked more than once.
#[test]
def test_linked_reverse_twice_is_identity : Bool :=
    let l := Linked.from_list (upto 16i64) in
    let r := Linked.reverse l in
    let rr := Linked.reverse r in
    let xs := Linked.to_list rr in
    same_i64s xs (upto 16i64)

#[test]
def test_linked_swap_adjacent_exchanges_the_first_two : Bool :=
    let l := Linked.from_list (upto 4i64) in
    let s := Linked.swap_adjacent l in
    let xs := Linked.to_list s in
    same_i64s xs [3i64, 4i64, 2i64, 1i64]

#[test]
def test_linked_swap_adjacent_of_one_is_itself : Bool :=
    let l := Linked.from_list (upto 1i64) in
    let s := Linked.swap_adjacent l in
    let xs := Linked.to_list s in
    same_i64s xs [1i64]

#[test]
def test_linked_swap_adjacent_of_empty_is_empty : Bool :=
    let l : Link I64 := Linked.from_list List.empty in
    let s := Linked.swap_adjacent l in
    let xs := Linked.to_list s in
    same_i64s xs List.empty
