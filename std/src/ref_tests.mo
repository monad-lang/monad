/// `Ref` tests: round-trip, atomic update, counter, modify, an update that
/// touches its own Ref, and concurrent updates.

use std::ref {
  Ref, Ref.new, Ref.get, Ref.set, Ref.update, Ref.add_i64, Ref.modify,
}
use std::concurrent::fiber {forkIO}
use std::concurrent::combine {all}

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

/// `add_i64` wraps at the I64 boundary on both backends (signed overflow is
/// UB in the compiled runtime; the interpreter already wraps).
#[test]
def test_ref_add_wraps : IO Bool := do {
  let r <- Ref.new 9223372036854775807i64;
  let v <- Ref.add_i64 r 1;
  return (v == -9223372036854775808i64)
}

/// `f` reads the Ref it is updating. Compiled IO natives run when they are
/// evaluated, so this used to deadlock on a lock held across `f`.
def peek_then_inc (r : Ref I64) (x : I64) : I64 :=
  let _ := Ref.get r in I64.add x 1

#[test]
def test_ref_update_may_touch_its_ref : IO Bool := do {
  let r <- Ref.new 1;
  let v <- Ref.update r (peek_then_inc r);
  let stored <- Ref.get r;
  return (v == 2 && stored == 2)
}

#[terminating]
def units (n : I64) : List Unit :=
  match n == 0 {
    true => List.empty,
    false => List.cons unit (units (I64.sub n 1))
  }

def run_each (steps : List (Unit -> IO Unit)) : IO Unit :=
  match steps {
    List.empty => IO.pure unit,
    List.cons step rest => do {
      step unit;
      run_each rest
    }
  }

def inc_times (r : Ref I64) (n : I64) : IO Unit :=
  run_each (List.map
    (fn (_ : Unit) => fn (_ : Unit) => Ref.modify r (fn (x : I64) => I64.add x 1))
    (units n))

/// Eight fibers (OS threads, compiled) race their updates; none is lost.
#[test]
def test_ref_update_concurrent_counter : IO Bool := do {
  let r <- Ref.new 0;
  let a <- forkIO (fn (_ : Unit) => inc_times r 500);
  let b <- forkIO (fn (_ : Unit) => inc_times r 500);
  let c <- forkIO (fn (_ : Unit) => inc_times r 500);
  let d <- forkIO (fn (_ : Unit) => inc_times r 500);
  let e <- forkIO (fn (_ : Unit) => inc_times r 500);
  let f <- forkIO (fn (_ : Unit) => inc_times r 500);
  let g <- forkIO (fn (_ : Unit) => inc_times r 500);
  let h <- forkIO (fn (_ : Unit) => inc_times r 500);
  let done <- all [a, b, c, d, e, f, g, h];
  let v <- Ref.get r;
  return (Result.is_ok done && v == 4000)
}
