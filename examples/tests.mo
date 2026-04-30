use std.test
use io
open IO

@[test]
def test_addition : Bool :=
    1 + 2 == 3

@[test]
def test_subtraction : Bool :=
    5 - 3 == 2

@[test]
def test_bool : Bool :=
    true && true

@[test]
def test_list : Bool :=
    not (List.is_empty [1, 2, 3])

@[test]
def test_failing : Bool :=
    false

def main (args: List String) : IO Unit :=
    println "not a test"
