/// Tests for `Clone` (`init/src/clone.mo`).
///
/// `Clone` carries no rule of its own — it is an ordinary class — so these
/// are behavioural: a clone is structurally equal to its source, cloning is
/// deep, and cloning does not consume the source (the same binder is cloned
/// twice). Independence of the two allocations is observable only through a
/// mutable cell, which `init/` may not name (`std/` owns `Ref`); that test
/// lives in `std/src/clone_tests.mo`.
use init::shared {Shared}
use init::list {List.get}

#[test]
def test_clone_a_pair_roundtrips : Bool :=
    let p : Pair I64 String := Pair.pair 7 "hi" in
    let q : Pair I64 String := Clone.clone (Shared.of p) in
    match q {
        Pair.pair n s => I64.beq n 7 && String.beq s "hi",
    }

#[test]
def test_clone_a_list_roundtrips : Bool :=
    let xs : List I64 := List.cons 7 List.empty in
    let ys : List I64 := Clone.clone (Shared.of xs) in
    match ys {
        List.cons h t => I64.beq h 7 && List.is_empty t,
        List.empty => false,
    }

#[test]
def test_clone_is_deep : Bool :=
    // The inner `List` is reachable only through the `Pair`; a clone that
    // stopped at the outer constructor would leave it shared.
    let xs : List I64 := List.cons 1 (List.cons 2 List.empty) in
    let p : Pair (List I64) I64 := Pair.pair xs 9 in
    let q : Pair (List I64) I64 := Clone.clone (Shared.of p) in
    match q {
        Pair.pair ys n =>
            match List.get 1 ys {
                Option.some inner => I64.beq inner 2 && I64.beq n 9,
                Option.none => false,
            },
    }

#[test]
def test_clone_does_not_consume_the_source : Bool :=
    // `Shared.of` is a read, so the same binder feeds both clones and the
    // result is two independent owned values. This is the sanctioned way to
    // get two owners of a non-`Copy` value.
    let xs : List I64 := List.cons 7 List.empty in
    let a : List I64 := Clone.clone (Shared.of xs) in
    let b : List I64 := Clone.clone (Shared.of xs) in
    Bool.not (List.is_empty a) && Bool.not (List.is_empty b)

#[test]
def test_clone_an_option_roundtrips : Bool :=
    let o : Option String := Option.some "x" in
    let c : Option String := Clone.clone (Shared.of o) in
    match c {
        Option.some s => String.beq s "x",
        Option.none => false,
    }

#[test]
def test_clone_a_result_roundtrips : Bool :=
    let r : Result String I64 := Result.ok 3 in
    let c : Result String I64 := Clone.clone (Shared.of r) in
    match c {
        Result.ok n => I64.beq n 3,
        Result.err _ => false,
    }
