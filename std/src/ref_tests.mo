/// `Ref` interpreter tests: round-trip, atomic update, counter, and modify.

use std::ref {
  Ref.new, Ref.get, Ref.set, Ref.update, Ref.add_i64, Ref.modify,
}

#[test]
def test_ref_roundtrip : IO Bool := do {
  let r <- Ref.new 41;
  let v <- Ref.get r;
  return (v == 41)
}

#[test]
def test_ref_set : IO Bool := do {
  let r <- Ref.new 1;
  Ref.set r 9;
  let v <- Ref.get r;
  return (v == 9)
}

#[test]
def test_ref_update_returns_and_stores : IO Bool := do {
  let r <- Ref.new 1;
  let v <- Ref.update r (fn (x : I64) => I64.add x 1);
  let stored <- Ref.get r;
  return (v == 2 && stored == 2)
}

#[test]
def test_ref_add_counter : IO Bool := do {
  let r <- Ref.new 0;
  let a <- Ref.add_i64 r 5;
  let b <- Ref.add_i64 r 3;
  return (a == 5 && b == 8)
}

#[test]
def test_ref_modify_discards_result : IO Bool := do {
  let r <- Ref.new "a";
  Ref.modify r (fn (s : String) => String.concat s "b");
  let v <- Ref.get r;
  return (String.beq v "ab")
}
