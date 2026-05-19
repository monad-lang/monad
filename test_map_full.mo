use std.test
use std.map

/// Verify Map.empty and Map.insert type-check without error.
@[test]
def test_map_empty_insert_typecheck : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  let m : BTreeMap I64 String := Map.insert 1 "one" m in
  true

/// Verify Map.lookup type-checks without error.
@[test]
def test_map_lookup_typecheck : Bool :=
  let m : BTreeMap I64 String := Map.empty in
  match Map.lookup 1 m {
    Option.some v => v == "one",
    _ => true
  }
