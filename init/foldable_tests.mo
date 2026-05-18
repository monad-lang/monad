use std.test
use init.foldable

def multiply (x : I64) (y : I64) : I64 := x * y

@[test]
def test_semigroup_string : Bool :=
  let s : String := Semigroup.combine "hello" "world" in
  s == "helloworld"

@[test]
def test_semigroup_list : Bool :=
  let a : List I64 := [1, 2] in
  let b : List I64 := [3, 4] in
  let c : List I64 := Semigroup.combine a b in
  match c {
    cons h _ => h == 1,
    empty => false
  }

@[test]
def test_monoid_string_empty : Bool :=
  let e : String := Monoid.mempty unit in
  String.is_empty e

@[test]
def test_monoid_list_empty : Bool :=
  let e : List I64 := Monoid.mempty unit in
  List.is_empty e

@[test]
def test_foldr_sum : Bool :=
  let res : I64 := Foldable.foldr (fn x acc => x + acc) 0 [1, 2, 3] in
  res == 6

@[test]
def test_foldr_product : Bool :=
  let res : I64 := Foldable.foldr multiply 1 [2, 3, 4] in
  res == 24

@[test]
def test_foldr_concat : Bool :=
  let res : String := Foldable.foldr (fn a acc => String.concat a acc) "" ["a", "b"] in
  res == "ab"

@[test]
def test_foldr_empty : Bool :=
  Foldable.foldr (fn x acc => x + acc) 0 [] == 0

@[test]
def test_foldr_option_some : Bool :=
  Foldable.foldr (fn x acc => x + acc) 0 (some 42) == 42

@[test]
def test_foldr_option_none : Bool :=
  Foldable.foldr (fn x acc => x + acc) 0 none == 0

@[test]
def test_foldl_sum : Bool :=
  Foldable.foldl (fn acc x => acc + x) 0 [1, 2, 3] == 6

@[test]
def test_foldl_option_some : Bool :=
  Foldable.foldl (fn acc x => acc + x) 0 (some 42) == 42

@[test]
def test_foldl_option_none : Bool :=
  Foldable.foldl (fn acc x => acc + x) 0 none == 0

@[test]
def test_foldr_foldl_equiv : Bool :=
  let fr : I64 := Foldable.foldr (fn x acc => x + acc) 0 [1, 2, 3] in
  let fl : I64 := Foldable.foldl (fn acc x => acc + x) 0 [1, 2, 3] in
  fr == fl
