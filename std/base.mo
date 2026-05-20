// Standard library: Core type classes
//
// Provides:
//   - Ordering type (lt, eq, gt)
//   - Ord A — total ordering (uses BEq from prelude)
//   - Hashable A — hash to U64
//   - Semigroup A — associative combine
//   - Monoid A — Semigroup with empty
//   - Default A — default value
//   - Enum A — enumerable types
//   - Bounded A — bounded types
//
// Note: BEq (boolean equality, Sort 1 / Type) is the computational
// equality type class from the prelude. Eq (propositional equality,
// Sort 0 / Prop) is for proofs and invariants — do NOT use Eq for
// runtime comparison.

type Ordering {
    lt,
    eq,
    gt
}

open Ordering

/// Total ordering with three-way comparison.
class [BEq A] Ord A {
    def compare : A -> A -> Ordering
}

/// Types that can be hashed to U64.
class Hashable A {
    def hash : A -> U64
}

/// Associative binary operation.
class Semigroup A {
    def combine : A -> A -> A
}

/// Semigroup with an identity element.
class [Semigroup A] Monoid A {
    def empty : A
}

/// Types with a default value.
class Default A {
    def default : A
}

/// Enumerable types with successor, predecessor, and conversion to/from Nat.
class Enum A {
    def succ : A -> A
    def pred : A -> A
    def to_nat : A -> Nat
    def from_nat : Nat -> A
}

/// Types with minimum and maximum bounds.
class [Enum A] Bounded A {
    def min_bound : A
    def max_bound : A
}

// ---------- Instances ----------

instance BEq Ordering {
    def beq (a b : Ordering) : Bool :=
        match a {
            lt => match b {
                lt => true,
                eq => false,
                gt => false
            },
            eq => match b {
                lt => false,
                eq => true,
                gt => false
            },
            gt => match b {
                lt => false,
                eq => false,
                gt => true
            }
        }
}

instance Ord Ordering {
    def compare (a b : Ordering) : Ordering :=
        match a {
            lt => match b {
                lt => eq,
                eq => lt,
                gt => lt
            },
            eq => match b {
                lt => gt,
                eq => eq,
                gt => lt
            },
            gt => match b {
                lt => gt,
                eq => gt,
                gt => eq
            }
        }
}

instance Semigroup String {
    def combine (a b : String) : String := a ++ b
}

// Monoid String and Default Bool deferred: compiler bug with
// class methods returning bare type params (e.g. `def empty : A`).
// See known limitation below.

// ---------- Known Limitations ----------
// Class methods returning bare type parameters (e.g. Monoid.empty : A,
// Default.default : A, Bounded.min_bound : A) fail type checking in
// instance bodies. The class method type gets forall-wrapped as
// {A : Type} -> A, and match_resolve_type's early return for ID types
// returns the forall unwrapped, failing downstream type unification.
// Workaround: instances for Monoid, Default, Bounded must be deferred
// until this is fixed in the type checker.

// ---------- Tests ----------

use std.test

@[test]
def test_beq_ordering_lt_lt : Bool :=
    BEq.beq lt lt

@[test]
def test_beq_ordering_eq_eq : Bool :=
    BEq.beq eq eq

@[test]
def test_beq_ordering_gt_gt : Bool :=
    BEq.beq gt gt

@[test]
def test_beq_ordering_lt_eq : Bool :=
    Bool.not (BEq.beq lt eq)

@[test]
def test_beq_ordering_lt_gt : Bool :=
    Bool.not (BEq.beq lt gt)

@[test]
def test_beq_ordering_eq_gt : Bool :=
    Bool.not (BEq.beq eq gt)

@[test]
def test_ord_lt_lt_eq : Bool :=
    match Ord.compare lt eq {
        lt => true,
        eq => false,
        gt => false
    }

@[test]
def test_ord_lt_eq_gt : Bool :=
    match Ord.compare eq gt {
        lt => true,
        eq => false,
        gt => false
    }

@[test]
def test_ord_lt_lt_gt : Bool :=
    match Ord.compare lt gt {
        lt => true,
        eq => false,
        gt => false
    }

@[test]
def test_ord_gt_eq_lt : Bool :=
    match Ord.compare eq lt {
        lt => false,
        eq => false,
        gt => true
    }

@[test]
def test_ord_gt_gt_eq : Bool :=
    match Ord.compare gt eq {
        lt => false,
        eq => false,
        gt => true
    }

@[test]
def test_ord_eq_eq_eq : Bool :=
    match Ord.compare eq eq {
        lt => false,
        eq => true,
        gt => false
    }

@[test]
def test_semigroup_string_concat : Bool :=
    let result : String := Semigroup.combine "hello" "world" in
    result == "helloworld"

@[test]
def test_semigroup_string_empty_left : Bool :=
    let result : String := Semigroup.combine "" "world" in
    result == "world"

@[test]
def test_semigroup_string_empty_right : Bool :=
    let result : String := Semigroup.combine "hello" "" in
    result == "hello"

@[test]
def test_semigroup_string_assoc : Bool :=
    let a : String := "a" in
    let b : String := "b" in
    let c : String := "c" in
    let left : String := Semigroup.combine (Semigroup.combine a b) c in
    let right : String := Semigroup.combine a (Semigroup.combine b c) in
    left == right
