use std.test
use init
use io
open IO

// Bool tests

@[test]
def test_bool_true : Bool :=
    if true then true else false

@[test]
def test_bool_false : Bool :=
    if false then false else true

@[test]
def test_bool_not_true : Bool :=
    if not true then false else true

@[test]
def test_bool_not_false : Bool :=
    if not false then true else false

@[test]
def test_bool_and : Bool :=
    true && true

@[test]
def test_bool_and_false : Bool :=
    if true && false then false else true

@[test]
def test_bool_or : Bool :=
    if false || true then true else false

@[test]
def test_bool_or_false : Bool :=
    if false || false then false else true

// I64 tests

@[test]
def test_i64_add : Bool :=
    1 + 2 == 3

@[test]
def test_i64_sub : Bool :=
    5 - 3 == 2

@[test]
def test_i64_mul : Bool :=
    4 * 3 == 12

@[test]
def test_i64_div : Bool :=
    10 / 2 == 5

@[test]
def test_i64_add_zero : Bool :=
    0 + 0 == 0

@[test]
def test_i64_mul_zero : Bool :=
    42 * 0 == 0

@[test]
def test_i64_sub_order : Bool :=
    10 - 3 == 7

// List tests

def empty_list : List I64 :=
    List.empty

@[test]
def test_list_empty : Bool :=
    match empty_list {
        empty => true,
        cons _ _ => false
    }

@[test]
def test_list_not_empty : Bool :=
    not (List.is_empty [1, 2, 3])

def first_of_empty : Option I64 :=
    List.first List.empty

@[test]
def test_list_first_none : Bool :=
    match first_of_empty {
        some _ => false,
        none => true
    }

@[test]
def test_list_single : Bool :=
    not (List.is_empty [42])

// Option tests

def none_opt : Option I64 :=
    none

@[test]
def test_option_none : Bool :=
    match none_opt {
        some _ => false,
        none => true
    }

@[test]
def test_option_get_or_default_some : Bool :=
    Option.get_or_default 0 (some 42) == 42

@[test]
def test_option_get_or_default_none : Bool :=
    Option.get_or_default 99 none_opt == 99

// Result tests

def err_val : Result String I64 :=
    err "fail"

@[test]
def test_result_err : Bool :=
    match err_val {
        ok _ => false,
        err _ => true
    }

// String tests

@[test]
def test_string_length : Bool :=
    String.length "hello" == 5

@[test]
def test_string_empty_length : Bool :=
    String.length "" == 0

@[test]
def test_string_is_empty : Bool :=
    String.is_empty ""

@[test]
def test_string_not_empty : Bool :=
    not (String.is_empty "hello")

// Nat tests

@[test]
def test_nat_zero : Bool :=
    match Nat.zero {
        zero => true,
        succ _ => false
    }

@[test]
def test_nat_succ : Bool :=
    match Nat.succ Nat.zero {
        zero => false,
        succ n => match n {
            zero => true,
            succ _ => false
        }
    }

// Operator tests

@[test]
def test_pipe_forward : Bool :=
    5 |> fn x => x + 1 |> fn x => x == 6

def double (x : I64) : I64 :=
    x * 2

@[test]
def test_apply_back : Bool :=
    double 3 == 6

// Unit tests

@[test]
def test_unit : Bool :=
    match unit {
        unit => true
    }
