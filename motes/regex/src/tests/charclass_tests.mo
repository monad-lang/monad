/// Class algebra against brute-force membership over a small universe:
/// every operation must agree with its set definition on every point.
use regex::charclass {
    class_of_list, class_union, class_intersect, class_difference, class_symmetric_difference,
    class_negate, class_contains, class_case_fold,
}

def universe : I64 := 40

def a_set : List (Pair I64 I64) := class_of_list [Pair.pair 3 9, Pair.pair 15 15, Pair.pair 20 30, Pair.pair 8 12]
def b_set : List (Pair I64 I64) := class_of_list [Pair.pair 0 4, Pair.pair 10 22, Pair.pair 31 31]

/// `op` agrees with `pred` on every point of [0, universe].
#[terminating]
def agrees (rs : List (Pair I64 I64)) (pred : I64 -> Bool) (i : I64) : Bool :=
    if I64.lt universe i then true
    else Bool.not (bool_ne (class_contains rs i) (pred i)) && agrees rs pred (i + 1)

def bool_ne (x : Bool) (y : Bool) : Bool := if x then Bool.not y else y

def in_a (i : I64) : Bool := class_contains a_set i
def in_b (i : I64) : Bool := class_contains b_set i

/// Sorted, disjoint and non-adjacent.
#[terminating]
def normalized (rs : List (Pair I64 I64)) : Bool :=
    match rs {
        List.empty => true,
        List.cons r rest =>
            Bool.not (I64.lt r.second r.first)
                && (match rest {
                    List.cons n _ => I64.lt (r.second + 1) n.first && normalized rest,
                    List.empty => true,
                }),
    }

#[test]
def test_of_list_normalizes : Bool :=
    normalized a_set && I64.beq (List.length a_set) 3

#[test]
def test_union : Bool :=
    normalized (class_union a_set b_set) && agrees (class_union a_set b_set) (fn (i : I64) => in_a i || in_b i) 0

#[test]
def test_intersect : Bool :=
    normalized (class_intersect a_set b_set) && agrees (class_intersect a_set b_set) (fn (i : I64) => in_a i && in_b i) 0

#[test]
def test_difference : Bool :=
    agrees (class_difference a_set b_set) (fn (i : I64) => in_a i && Bool.not (in_b i)) 0

#[test]
def test_symmetric_difference : Bool :=
    agrees (class_symmetric_difference a_set b_set) (fn (i : I64) => bool_ne (in_a i) (in_b i)) 0

#[test]
def test_negate : Bool :=
    normalized (class_negate a_set universe) && agrees (class_negate a_set universe) (fn (i : I64) => Bool.not (in_a i)) 0
        && I64.beq (List.length (class_negate List.empty 10)) 1

#[test]
def test_case_fold : Bool :=
    let entries : List (Pair I64 (List I64)) := [Pair.pair 65 [97], Pair.pair 75 [107, 8490], Pair.pair 97 [65]] in
    let folded : List (Pair I64 (List I64)) := entries in
    class_contains (class_case_fold [Pair.pair 75 75] folded) 8490
        && class_contains (class_case_fold [Pair.pair 60 70] folded) 97
        && Bool.not (class_contains (class_case_fold [Pair.pair 60 70] folded) 107)
