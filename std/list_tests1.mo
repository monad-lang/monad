use std.test
use std.list

// Show tests

@[test]
def test_show_string : Bool :=
    Show.show "hello" == "hello"

@[test]
def test_show_i64 : Bool :=
    Show.show 42 == "42"

@[test]
def test_show_i64_zero : Bool :=
    Show.show 0 == "0"

@[test]
def test_show_i64_negative : Bool :=
    Show.show (-1) == "-1"

@[test]
def test_show_bool_true : Bool :=
    Show.show true == "true"

@[test]
def test_show_bool_false : Bool :=
    Show.show false == "false"

@[test]
def test_show_list_i64 : Bool :=
    Show.show ([1, 2, 3] : List I64) == "[1, 2, 3]"

@[test]
def test_show_list_empty : Bool :=
    Show.show ([] : List I64) == "[]"

@[test]
def test_show_list_single : Bool :=
    Show.show [42] == "[42]"

// list_show helper (bypasses BLOCKER #8)

@[test]
def test_list_show_empty : Bool :=
    list_show I64.to_string ([] : List I64) == "[]"

@[test]
def test_list_show_single : Bool :=
    list_show I64.to_string [42] == "[42]"

@[test]
def test_list_show_multi : Bool :=
    list_show I64.to_string [1, 2, 3] == "[1, 2, 3]"

def show_bool_fn (b: Bool) : String :=
    if b then "T" else "F"

@[test]
def test_list_show_bool : Bool :=
    list_show show_bool_fn [true, false, true] == "[T, F, T]"
