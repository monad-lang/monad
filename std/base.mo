// Standard library: Core type classes
//
// Provides:
//   - Ordering type (lt, eq, gt)
//   - Ord A — total ordering (uses BEq from prelude)
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

open Ordering {eq, gt, lt}

/// Total ordering with three-way comparison.
class [BEq A] Ord A {
    def compare : A -> A -> Ordering
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

instance Monoid String {
    def empty : String := ""
}

instance Default Bool {
    def default : Bool := false
}

instance Default I64 {
    def default : I64 := 0
}

instance Enum Ordering {
    def succ (o : Ordering) : Ordering :=
        if BEq.beq o lt then eq
        else if BEq.beq o eq then gt
        else lt

    def pred (o : Ordering) : Ordering :=
        if BEq.beq o lt then gt
        else if BEq.beq o eq then lt
        else eq

    def to_nat (o : Ordering) : Nat :=
        if BEq.beq o lt then Nat.zero
        else if BEq.beq o eq then Nat.succ Nat.zero
        else Nat.succ (Nat.succ Nat.zero)

    def from_nat (n : Nat) : Ordering :=
        if Nat.eq n Nat.zero then lt
        else if Nat.eq n (Nat.succ Nat.zero) then eq
        else gt
}

instance Bounded Ordering {
    def min_bound : Ordering := lt
    def max_bound : Ordering := gt
}

instance Ord I64 {
    def compare (a b : I64) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord Bool {
    def compare (a b : Bool) : Ordering :=
        if a == b then eq
        else if a then gt
        else lt
}

instance Ord U8 {
    def compare (a b : U8) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord I8 {
    def compare (a b : I8) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord I16 {
    def compare (a b : I16) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord I32 {
    def compare (a b : I32) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord U16 {
    def compare (a b : U16) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord U32 {
    def compare (a b : U32) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord U64 {
    def compare (a b : U64) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord F32 {
    def compare (a b : F32) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

instance Ord F64 {
    def compare (a b : F64) : Ordering :=
        if a == b then eq
        else if BOrd.lt a b then lt
        else gt
}

def ordering_show (o : Ordering) : String :=
    if BEq.beq o lt then "lt"
    else if BEq.beq o eq then "eq"
    else "gt"

// ---------- Tests ----------


#[test]
def test_beq_ordering_lt_lt : Bool :=
    BEq.beq lt lt

#[test]
def test_beq_ordering_eq_eq : Bool :=
    BEq.beq eq eq

#[test]
def test_beq_ordering_gt_gt : Bool :=
    BEq.beq gt gt

#[test]
def test_beq_ordering_lt_eq : Bool :=
    Bool.not (BEq.beq lt eq)

#[test]
def test_beq_ordering_lt_gt : Bool :=
    Bool.not (BEq.beq lt gt)

#[test]
def test_beq_ordering_eq_gt : Bool :=
    Bool.not (BEq.beq eq gt)

#[test]
def test_ord_lt_lt_eq : Bool :=
    match Ord.compare lt eq {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_lt_eq_gt : Bool :=
    match Ord.compare eq gt {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_lt_lt_gt : Bool :=
    match Ord.compare lt gt {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_gt_eq_lt : Bool :=
    match Ord.compare eq lt {
        lt => false,
        eq => false,
        gt => true
    }

#[test]
def test_ord_gt_gt_eq : Bool :=
    match Ord.compare gt eq {
        lt => false,
        eq => false,
        gt => true
    }

#[test]
def test_ord_eq_eq_eq : Bool :=
    match Ord.compare eq eq {
        lt => false,
        eq => true,
        gt => false
    }

#[test]
def test_semigroup_string_concat : Bool :=
    let result : String := Semigroup.combine "hello" "world" in
    result == "helloworld"

#[test]
def test_semigroup_string_empty_left : Bool :=
    let result : String := Semigroup.combine "" "world" in
    result == "world"

#[test]
def test_semigroup_string_empty_right : Bool :=
    let result : String := Semigroup.combine "hello" "" in
    result == "hello"

#[test]
def test_semigroup_string_assoc : Bool :=
    let a : String := "a" in
    let b : String := "b" in
    let c : String := "c" in
    let left : String := Semigroup.combine (Semigroup.combine a b) c in
    let right : String := Semigroup.combine a (Semigroup.combine b c) in
    left == right

#[test]
def test_monoid_empty_string : Bool :=
    let empty_str : String := Monoid.empty in
    empty_str == ""

#[test]
def test_default_bool : Bool :=
    Default.default == false

#[test]
def test_default_i64 : Bool :=
    Default.default == 0i64

#[test]
def test_default_i64_ne_not_false : Bool :=
    Bool.not (Default.default == 1i64)

#[test]
def test_enum_succ : Bool :=
    let s1 := Enum.succ lt in
    let s2 := Enum.succ eq in
    let s3 := Enum.succ gt in
    BEq.beq s1 eq && BEq.beq s2 gt && BEq.beq s3 lt

#[test]
def test_enum_pred : Bool :=
    let p1 := Enum.pred gt in
    let p2 := Enum.pred lt in
    let p3 := Enum.pred eq in
    BEq.beq p1 eq && BEq.beq p2 gt && BEq.beq p3 lt

#[test]
def test_enum_to_nat : Bool :=
    let n0 := Enum.to_nat lt in
    let n1 := Enum.to_nat eq in
    let n2 := Enum.to_nat gt in
    let zero := Nat.zero in
    let one := Nat.succ Nat.zero in
    let two := Nat.succ (Nat.succ Nat.zero) in
    Nat.eq n0 zero && Nat.eq n1 one && Nat.eq n2 two

#[test]
def test_enum_from_nat : Bool :=
    let f0 := Enum.from_nat Nat.zero in
    let f1 := Enum.from_nat (Nat.succ Nat.zero) in
    BEq.beq f0 lt && BEq.beq f1 eq

#[test]
def test_bounded_min : Bool :=
    BEq.beq Bounded.min_bound lt

#[test]
def test_bounded_max : Bool :=
    BEq.beq Bounded.max_bound gt

#[test]
def test_ord_i64_lt : Bool :=
    match Ord.compare 1i64 5i64 {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_i64_eq : Bool :=
    match Ord.compare 42i64 42i64 {
        lt => false,
        eq => true,
        gt => false
    }

#[test]
def test_ord_i64_gt : Bool :=
    match Ord.compare 10i64 3i64 {
        lt => false,
        eq => false,
        gt => true
    }

#[test]
def test_ord_bool_false_true : Bool :=
    match Ord.compare false true {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_bool_true_false : Bool :=
    match Ord.compare true false {
        lt => false,
        eq => false,
        gt => true
    }

#[test]
def test_ord_bool_true_true : Bool :=
    match Ord.compare true true {
        lt => false,
        eq => true,
        gt => false
    }

#[test]
def test_ord_u8_lt : Bool :=
    match Ord.compare 1u8 5u8 {
        lt => true,
        eq => false,
        gt => false
    }

#[test]
def test_ord_u8_eq : Bool :=
    match Ord.compare 42u8 42u8 {
        lt => false,
        eq => true,
        gt => false
    }

#[test]
def test_ord_u8_gt : Bool :=
    match Ord.compare 10u8 3u8 {
        lt => false,
        eq => false,
        gt => true
    }

#[test]
def test_ordering_show_lt : Bool :=
    ordering_show lt == "lt"

#[test]
def test_ordering_show_eq : Bool :=
    ordering_show eq == "eq"

#[test]
def test_ordering_show_gt : Bool :=
    ordering_show gt == "gt"

#[test]
def test_ord_i8_lt : Bool :=
    BEq.beq (Ord.compare 0i8 5i8) lt

#[test]
def test_ord_i8_eq : Bool :=
    BEq.beq (Ord.compare 5i8 5i8) eq

#[test]
def test_ord_i8_gt : Bool :=
    BEq.beq (Ord.compare 5i8 0i8) gt

#[test]
def test_ord_u16_lt : Bool :=
    BEq.beq (Ord.compare 0u16 5u16) lt

#[test]
def test_ord_u16_gt : Bool :=
    BEq.beq (Ord.compare 5u16 0u16) gt

#[test]
def test_ord_f64_lt : Bool :=
    BEq.beq (Ord.compare 0.0f64 5.0f64) lt

#[test]
def test_ord_f64_gt : Bool :=
    BEq.beq (Ord.compare 5.0f64 0.0f64) gt
