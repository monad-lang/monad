/// Character classes as sorted, disjoint, non-adjacent inclusive ranges
/// `(lo, hi)` of scalar values (or bytes, under `(?-u)`).
///
/// Every operation is a single merge pass over its inputs; none assumes
/// more than the representation invariant, which each one re-establishes.
use unicode::lookup {Unicode.union_ranges}
use std::list {List.filter, List.sort_by}

/// The largest scalar value.
pub def max_scalar : I64 := 1114111

/// The largest byte.
pub def max_byte : I64 := 255

def by_lo (a : Pair I64 I64) (b : Pair I64 I64) : Bool := I64.lt a.first b.first

/// Normalize any list of ranges (unsorted, overlapping, `lo > hi` dropped).
pub def class_of_list (rs : List (Pair I64 I64)) : List (Pair I64 I64) :=
    Unicode.union_ranges (List.sort_by by_lo (List.filter valid rs)) List.empty

def valid (r : Pair I64 I64) : Bool := Bool.not (I64.lt r.second r.first)

pub def class_union (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) : List (Pair I64 I64) :=
    Unicode.union_ranges a b

/// The complement within `[0, max]`.
pub def class_negate (a : List (Pair I64 I64)) (max : I64) : List (Pair I64 I64) :=
    List.reverse (negate_go a 0 max List.empty)

#[terminating]
def negate_go (rs : List (Pair I64 I64)) (next : I64) (max : I64) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match rs {
        List.empty => if I64.lt max next then acc else List.cons (Pair.pair next max) acc,
        List.cons r rest =>
            if I64.lt max r.first then negate_go List.empty next max acc
            else negate_go rest (r.second + 1) max
                (if I64.lt next r.first then List.cons (Pair.pair next (r.first - 1)) acc else acc),
    }

pub def class_intersect (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) : List (Pair I64 I64) :=
    List.reverse (intersect_go a b List.empty)

/// Two cursors; the range that ends first advances.
#[terminating]
def intersect_go (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match a {
        List.empty => acc,
        List.cons x xs =>
            match b {
                List.empty => acc,
                List.cons y ys =>
                    let lo : I64 := if I64.lt x.first y.first then y.first else x.first in
                    let hi : I64 := if I64.lt x.second y.second then x.second else y.second in
                    let acc2 : List (Pair I64 I64) := if I64.lt hi lo then acc else List.cons (Pair.pair lo hi) acc in
                    if I64.lt x.second y.second then intersect_go xs (List.cons y ys) acc2
                    else intersect_go (List.cons x xs) ys acc2,
            },
    }

pub def class_difference (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) : List (Pair I64 I64) :=
    class_intersect a (class_negate b max_scalar)

pub def class_symmetric_difference (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) : List (Pair I64 I64) :=
    class_difference (class_union a b) (class_intersect a b)

pub def class_contains (a : List (Pair I64 I64)) (c : I64) : Bool :=
    match a {
        List.empty => false,
        List.cons r rest =>
            if I64.lt c r.first then false
            else if I64.lt r.second c then class_contains rest c
            else true,
    }

/// Close the class under simple case folding: every scalar in it brings
/// the other members of its orbit. `entries` is
/// `Unicode.simple_fold_entries` (ascending by scalar), walked once
/// alongside the class.
pub def class_case_fold (a : List (Pair I64 I64)) (entries : List (Pair I64 (List I64))) : List (Pair I64 I64) :=
    class_union a (class_of_list (fold_go a entries List.empty))

#[terminating]
def fold_go (a : List (Pair I64 I64)) (entries : List (Pair I64 (List I64))) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match a {
        List.empty => acc,
        List.cons r rest =>
            match entries {
                List.empty => acc,
                List.cons e more =>
                    if I64.lt e.first r.first then fold_go (List.cons r rest) more acc
                    else if I64.lt r.second e.first then fold_go rest (List.cons e more) acc
                    else fold_go (List.cons r rest) more (List.append (List.map point e.second) acc),
            },
    }

def point (c : I64) : Pair I64 I64 := Pair.pair c c

/// Total width of a class: how many scalars it holds.
pub def class_size (a : List (Pair I64 I64)) : I64 :=
    match a {
        List.empty => 0,
        List.cons r rest => (r.second - r.first + 1) + class_size rest,
    }
