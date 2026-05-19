use std.test
use std.map

/// Verify Map.empty and Map.insert type-check and evaluate.
@[test]
def test_map_empty_insert_typecheck : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  let m : BTreeMap I64 String := Map.insert 1 "one" m in
  true

/// Verify Map.lookup evaluates correctly after insert.
@[test]
def test_map_insert_lookup : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  let m : BTreeMap I64 String := Map.insert 1 "one" m in
  match Map.lookup 1 m {
    Option.some v => v == "one",
    _ => false
  }

/// Verify that looking up a missing key returns none.
@[test]
def test_map_lookup_missing : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  let m : BTreeMap I64 String := Map.insert 1 "one" m in
  match Map.lookup 2 m {
    Option.none => true,
    _ => false
  }

/// Verify that delete removes a key.
@[test]
def test_map_delete : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  let m : BTreeMap I64 String := Map.insert 1 "one" m in
  let m : BTreeMap I64 String := Map.insert 2 "two" m in
  let m : BTreeMap I64 String := Map.delete 1 m in
  match Map.lookup 1 m {
    Option.none => true,
    _ => false
  }

/// ─── HashMap tests ──────────────────────────────────────────

/// Verify HashMap.empty and HashMap.insert type-check and evaluate.
@[test]
def test_hashmap_empty_insert : Bool :=
  let m : HashMap I64 String := Map.empty in
  let m : HashMap I64 String := Map.insert 1 "one" m in
  true

/// Verify HashMap.lookup returns correct value after insert.
@[test]
def test_hashmap_insert_lookup : Bool :=
  let m : HashMap I64 String := Map.empty in
  let m : HashMap I64 String := Map.insert 1 "one" m in
  match Map.lookup 1 m {
    Option.some v => v == "one",
    _ => false
  }

/// Verify HashMap.lookup returns none for missing key.
@[test]
def test_hashmap_lookup_missing : Bool :=
  let m : HashMap I64 String := Map.empty in
  let m : HashMap I64 String := Map.insert 1 "one" m in
  match Map.lookup 2 m {
    Option.none => true,
    _ => false
  }

/// Verify HashMap.delete removes a key.
@[test]
def test_hashmap_delete : Bool :=
  let m : HashMap I64 String := Map.empty in
  let m : HashMap I64 String := Map.insert 1 "one" m in
  let m : HashMap I64 String := Map.insert 2 "two" m in
  let m : HashMap I64 String := Map.delete 1 m in
  match Map.lookup 1 m {
    Option.none => true,
    _ => false
  }
