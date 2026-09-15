use std.test {}
use init.foldable {Monoid, Semigroup}

#[test]
def test_semigroup_string : Bool :=
  let s : String := Semigroup.combine "hello" "world" in
  s == "helloworld"

#[test]
def test_semigroup_list : Bool :=
  let a : List I64 := [1, 2] in
  let b : List I64 := [3, 4] in
  let c : List I64 := Semigroup.combine a b in
  match c {
    cons h _ => h == 1,
    empty => false
  }

#[test]
def test_monoid_string_empty : Bool :=
  let e : String := Monoid.mempty unit in
  String.is_empty e

#[test]
def test_monoid_list_empty : Bool :=
  let e : List I64 := Monoid.mempty unit in
  List.is_empty e
