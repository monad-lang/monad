use std.test
use std.list

// Append tests (continued)

@[test]
def test_list_append_empty_right : Bool :=
    let xs : List I64 := [1, 2] in
    BEq.beq (xs ++ ([] : List I64)) xs

@[test]
def test_list_append_empty_both : Bool :=
    let xs : List I64 := [] in
    let ys : List I64 := [] in
    BEq.beq (xs ++ ys) xs

// Length tests

@[test]
def test_list_length_empty : Bool :=
    List.length ([] : List I64) == 0

@[test]
def test_list_length_one : Bool :=
    List.length [42] == 1

@[test]
def test_list_length_three : Bool :=
    List.length [1, 2, 3] == 3

// Filter tests

@[test]
def test_list_filter_all_pass : Bool :=
    let xs : List I64 := [1, 2, 3] in
    let filtered := List.filter (fn x => true) xs in
    BEq.beq filtered xs

@[test]
def test_list_filter_none_pass : Bool :=
    let xs : List I64 := [1, 2, 3] in
    let filtered := List.filter (fn x => false) xs in
    BEq.beq filtered ([] : List I64)
