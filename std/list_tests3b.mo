use std.test
use std.list

// Filter tests (continued)

def is_even_fn (x : I64) : Bool :=
    x == 2 || x == 4 || x == 6

@[test]
def test_list_filter_even : Bool :=
    let xs : List I64 := [1, 2, 3, 4, 5, 6] in
    let evens := List.filter is_even_fn xs in
    BEq.beq evens [2, 4, 6]

@[test]
def test_list_filter_empty : Bool :=
    let filtered := List.filter (fn x => true) ([] : List I64) in
    BEq.beq filtered ([] : List I64)

// Sum tests (concrete lists only — empty list triggers
// List.* prefix + concrete type unification bug)

@[test]
def test_list_sum_one : Bool :=
    List.sum [42] == 42

@[test]
def test_list_sum_multi : Bool :=
    List.sum [1, 2, 3, 4] == 10

@[test]
def test_list_sum_negative : Bool :=
    List.sum [5, -3, 2] == 4
