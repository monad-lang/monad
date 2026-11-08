/// Ownership drop-glue fixture (ownership-regions-memory O4).
///
/// The two types below are monomorphic, non-`Copy` and have no nullary
/// constructor, so the ownership verdict classifies them Owned: under
/// `MONAD_OWNERSHIP=1` their cells come from `monad_owned_alloc` and are
/// returned by generated drop glue. Under the default build they are
/// Region, nothing is freed, and these tests assert only the values.
///
/// `init` is `[affine] mode = "error"`, which is what the ownership gate
/// requires, so this file is the one place the feature can be exercised with
/// `monad test` (its test binary's exit runs the MONAD_ALLOC_STATS=1
/// printer, where `owned-constructors` and `owned-frees` must balance).
type OwnedBox {
    box (x : I64),
}

type OwnedPair {
    pair (a : OwnedBox) (b : I64),
}

/// `b` is never used, so the caller transfers ownership and this def drops
/// it at its own exit.
def consume_unused (b : OwnedBox) : I64 :=
    40

/// The `let` binder is unused and its initializer is a fresh constructor
/// allocation, so it is dropped at this def's exit.
def unused_fresh_let : I64 :=
    let unused : OwnedBox := OwnedBox.box 9 in
    40

/// Dropping the pair recurses into its Owned `a` field before freeing the
/// pair's own cell.
def discard_pair (p : OwnedPair) : I64 :=
    7

/// N allocations, each consumed by a callee that drops it. Tail-recursive,
/// so the def itself is TCO-rewritten and emits no drops of its own -- the
/// frees all happen in `consume_unused`.
#[partial]
def consume_loop (n : I64) (acc : I64) : I64 :=
    if I64.lt n 1
    then acc
    else consume_loop (n - 1) (acc + consume_unused (OwnedBox.box n))

#[test]
def test_unused_owned_param_is_consumed : Bool :=
    I64.beq (consume_unused (OwnedBox.box 7)) 40

#[test]
def test_unused_fresh_let_is_dropped : Bool :=
    I64.beq unused_fresh_let 40

#[test]
def test_owned_pair_drops_its_owned_field : Bool :=
    I64.beq (discard_pair (OwnedPair.pair (OwnedBox.box 1) 2)) 7

#[test]
def test_owned_allocation_loop : Bool :=
    I64.beq (consume_loop 100 0) 4000
