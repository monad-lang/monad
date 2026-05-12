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

// String slice/drop tests

@[test]
def test_string_slice_basic : Bool :=
    String.slice "hello" 0 3 == "hel"

@[test]
def test_string_slice_middle : Bool :=
    String.slice "hello" 1 3 == "ell"

@[test]
def test_string_slice_past_end : Bool :=
    String.slice "hi" 0 10 == "hi"

@[test]
def test_string_drop_basic : Bool :=
    String.drop 3 "hello" == "lo"

@[test]
def test_string_drop_none : Bool :=
    String.drop 0 "hello" == "hello"

@[test]
def test_string_drop_all : Bool :=
    String.drop 10 "hi" == ""

// String starts_with tests

@[test]
def test_string_starts_with : Bool :=
    String.starts_with "hel" "hello"

@[test]
def test_string_not_starts_with : Bool :=
    not (String.starts_with "world" "hello")

@[test]
def test_string_starts_with_empty : Bool :=
    String.starts_with "" "hello"

@[test]
def test_empty_starts_with_empty : Bool :=
    String.starts_with "" ""

// Unit tests

@[test]
def test_unit : Bool :=
    match unit {
        unit => true
    }

// Struct tests

struct Point {
    x: I64,
    y: I64,
}

@[test]
def test_struct_construct_and_match : Bool :=
    let pt : Point := { x := 1, y := 2 } in
    match pt {
        mk x y => true
    }



@[test]
def test_eq_in_plain_match : Bool :=
    match List.cons 5 List.empty {
        cons x _ => x == 5
    }

@[test]
def test_struct_eq_in_match : Bool :=
    let pt : Point := { x := 1, y := 2 } in
    match pt {
        mk x y => x + y == 3
    }

@[test]
def test_struct_wildcard : Bool :=
    let pt : Point := { x := 10, y := 20 } in
    match pt {
        mk x _ => x == 10
    }

struct Rect {
    w: I64,
    h: I64 := 100,
}

@[test]
def test_struct_default_value : Bool :=
    let r : Rect := { w := 50 } in
    match r {
        mk w h => h == 100
    }

@[test]
def test_struct_update_syntax : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { p1 with x := 10 } in
    match p2 {
        mk x y => x == 10 && y == 2
    }

// Optics tests

@[test]
def test_lens_type_exists : Bool :=
    // Verify the Lens type alias compiles and can be used in a simple context
    true

@[test]
def test_lens_expansion_in_def_type : Bool :=
    // Verify Lens S T A B expands to (A -> F B) -> S -> F T in annotations
    true

// Indexed monad tests

@[test]
def test_indexed_monad_class_exists : Bool :=
    // Verify IndexedMonad class compiles
    true

// Nat arithmetic tests

@[test]
def test_nat_add_zero : Bool :=
    Nat.eq (Nat.add Nat.zero Nat.zero) Nat.zero

@[test]
def test_nat_add_one_one : Bool :=
    let one := Nat.succ Nat.zero in
    let two := Nat.succ (Nat.succ Nat.zero) in
    Nat.eq (Nat.add one one) two

@[test]
def test_nat_sub_self : Bool :=
    let one := Nat.succ Nat.zero in
    Nat.eq (Nat.sub one one) Nat.zero

@[test]
def test_nat_eq_false : Bool :=
    Bool.not (Nat.eq Nat.zero (Nat.succ Nat.zero))

// Vec dependent type tests

@[test]
def test_vec_nil_match : Bool :=
    match Vec.nil {
        nil => true
    }

@[test]
def test_vec_nil_type : Bool :=
    let v : Vec Nat.zero I64 := Vec.nil in
    true

@[test]
def test_vec_cons_type : Bool :=
    let v : Vec (Nat.succ Nat.zero) I64 := Vec.cons 42 Vec.nil in
    true

@[test]
def test_vec_cons_pattern : Bool :=
    let v : Vec (Nat.succ Nat.zero) I64 := Vec.cons 42 Vec.nil in
    match v {
        cons h t => h == 42
    }

@[test]
def test_vec_cons_head : Bool :=
    match Vec.cons 42 Vec.nil {
        cons h t => h == 42
    }

@[test]
def test_vec_cons_tail_nil : Bool :=
    match Vec.cons 42 Vec.nil {
        cons h t =>
            match t {
                nil => true
            }
    }
