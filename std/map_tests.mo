use std.test
use std.map

@[test]
def test_empty_to_list : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  List.is_empty (BTreeMap.to_list m)

@[test]
def test_fold_empty : Bool :=
  let m : BTreeMap I64 I64 := Map.empty in
  BEq.beq (BTreeMap.fold (fn (acc: I64) (k: I64) (v: I64) => acc + v) 0 m) 0
