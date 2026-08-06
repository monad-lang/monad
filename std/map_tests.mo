// TODO: `BTreeMap`/`empty`/`fold`/`to_list` are all used throughout this
// file (bare type annotations and `Map`-class method calls) but are
// deliberately NOT listed here. Explicitly naming ANY of `std.map`'s
// `Map`-class-instance-related exports here exposes a pre-existing latent
// bug in instance/dictionary resolution for `instance [BOrd K] Map
// BTreeMap {...}` (methods resolve to the wrong dictionary at runtime —
// "expected function found: K -> V -> M K V -> M K V" — even though
// type-checking succeeds); everything below remains available regardless
// via the same always-on mechanism that lets any top-level type/def
// resolve without being explicitly `use`d. Fix properly and restore an
// explicit name list once the underlying bug is fixed.
use std.map {}
use std.list {all, length}

#[test]
def test_empty_to_list : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  List.is_empty (BTreeMap.to_list m)

#[test]
def test_fold_empty : Bool :=
  let m : BTreeMap I64 I64 := Map.empty in
  BEq.beq (BTreeMap.fold (fn (acc: I64) (k: I64) (v: I64) => acc + v) 0 m) 0

// TODO fix
// @[test]
// def test_empty_beq : Bool :=
//   let m : BTreeMap I64 String := Map.empty in
//   m == Map.empty

// ─── Insert / rotation regression tests ───
//
// These target a real data-loss bug found in BTreeMap.rotate_ll / rotate_rr:
// both descended one level too deep into the rotated child's own children,
// silently dropping the child itself. Fixed by promoting the immediate child
// directly (standard AVL single rotation). The bug was invisible until a
// rotation actually fired, which the previous test suite never triggered.

def map_has_key (key : String) (m : BTreeMap String I64) : Bool :=
  match Map.lookup key m {
    Option.some _ => true,
    Option.none => false
  }

def map_has_all_keys (keys : List String) (m : BTreeMap String I64) : Bool :=
  List.all (fn k => map_has_key k m) keys

def map_insert_all (keys : List String) (m : BTreeMap String I64) : BTreeMap String I64 :=
  match keys {
    List.empty => m,
    List.cons k rest => map_insert_all rest (Map.insert k 0 m)
  }

def map_delete_all (keys : List String) (m : BTreeMap String I64) : BTreeMap String I64 :=
  match keys {
    List.empty => m,
    List.cons k rest => map_delete_all rest (Map.delete k m)
  }

#[test]
def test_insert_avl_drop_repro : Bool :=
  let m1 : BTreeMap String I64 := Map.insert "d" 4 Map.empty in
  let m2 := Map.insert "c" 3 m1 in
  let m3 := Map.insert "b" 2 m2 in
  let m4 := Map.insert "a" 1 m3 in
  BEq.beq (List.length (BTreeMap.to_list m4)) 4 &&
  map_has_all_keys ["a", "b", "c", "d"] m4

def int_map_has_all_keys (keys : List I64) (m : BTreeMap I64 I64) : Bool :=
  List.all (fn k => match Map.lookup k m { Option.some _ => true, Option.none => false }) keys

#[test]
def test_insert_rotate_rr : Bool :=
  let m1 : BTreeMap I64 I64 := Map.insert 1 1 Map.empty in
  let m2 := Map.insert 2 2 m1 in
  let m3 := Map.insert 3 3 m2 in
  BEq.beq (List.length (BTreeMap.to_list m3)) 3 &&
  int_map_has_all_keys [1, 2, 3] m3

#[test]
def test_insert_rotate_ll : Bool :=
  let m1 : BTreeMap I64 I64 := Map.insert 3 3 Map.empty in
  let m2 := Map.insert 2 2 m1 in
  let m3 := Map.insert 1 1 m2 in
  BEq.beq (List.length (BTreeMap.to_list m3)) 3 &&
  int_map_has_all_keys [1, 2, 3] m3

#[test]
def test_insert_rotate_lr : Bool :=
  let m1 : BTreeMap I64 I64 := Map.insert 3 3 Map.empty in
  let m2 := Map.insert 1 1 m1 in
  let m3 := Map.insert 2 2 m2 in
  BEq.beq (List.length (BTreeMap.to_list m3)) 3 &&
  int_map_has_all_keys [1, 2, 3] m3

#[test]
def test_insert_rotate_rl : Bool :=
  let m1 : BTreeMap I64 I64 := Map.insert 1 1 Map.empty in
  let m2 := Map.insert 3 3 m1 in
  let m3 := Map.insert 2 2 m2 in
  BEq.beq (List.length (BTreeMap.to_list m3)) 3 &&
  int_map_has_all_keys [1, 2, 3] m3

#[test]
def test_insert_many_unsorted : Bool :=
  let keys := ["m", "b", "x", "a", "z", "k", "d", "q", "c", "y", "n", "e"] in
  let m := map_insert_all keys (Map.empty : BTreeMap String I64) in
  BEq.beq (List.length (BTreeMap.to_list m)) (List.length keys) &&
  map_has_all_keys keys m

// ─── Delete regression tests ───
//
// Map.delete's two-children case had a separate bug: it replaced the deleted
// node with `right`'s own root key/value instead of the true in-order
// successor, and discarded the rest of `right` (`rr`) entirely. Fixed using
// the existing BTreeMap.min_node helper plus a recursive Map.delete call.

#[test]
def test_delete_leaf : Bool :=
  let m1 : BTreeMap String I64 := Map.insert "b" 2 Map.empty in
  let m2 := Map.insert "a" 1 m1 in
  let m3 := Map.insert "c" 3 m2 in
  let m4 := Map.delete "a" m3 in
  BEq.beq (List.length (BTreeMap.to_list m4)) 2 &&
  map_has_all_keys ["b", "c"] m4 &&
  Bool.not (map_has_key "a" m4)

#[test]
def test_delete_one_child : Bool :=
  let m1 : BTreeMap String I64 := Map.insert "c" 3 Map.empty in
  let m2 := Map.insert "b" 2 m1 in
  let m3 := Map.insert "a" 1 m2 in
  let m4 := Map.delete "c" m3 in
  BEq.beq (List.length (BTreeMap.to_list m4)) 2 &&
  map_has_all_keys ["a", "b"] m4 &&
  Bool.not (map_has_key "c" m4)

#[test]
def test_delete_two_children : Bool :=
  let keys := ["d", "b", "f", "a", "c", "e", "g"] in
  let m := map_insert_all keys (Map.empty : BTreeMap String I64) in
  let m2 := Map.delete "d" m in
  BEq.beq (List.length (BTreeMap.to_list m2)) 6 &&
  map_has_all_keys ["a", "b", "c", "e", "f", "g"] m2 &&
  Bool.not (map_has_key "d" m2)

#[test]
def test_insert_then_delete_all : Bool :=
  let insert_keys := ["m", "b", "x", "a", "z", "k", "d", "q", "c", "y", "n", "e"] in
  let delete_keys := ["e", "n", "y", "c", "q", "d", "k", "z", "a", "x", "b", "m"] in
  let m := map_insert_all insert_keys (Map.empty : BTreeMap String I64) in
  let m2 := map_delete_all delete_keys m in
  List.is_empty (BTreeMap.to_list m2)
