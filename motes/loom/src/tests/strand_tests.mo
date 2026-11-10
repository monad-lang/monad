/// `Strand`/`Disposer` -- Loom Phase 2: LIFO teardown, the index
/// transition, and a failing disposer that does not stop the rest.
use loom::strand {
    Strand, StrandRun, Pending, Active, Disposed,
    Strand.run, Strand.bracket, Strand.pending, Strand.sealed, Strand.dispose,
}
use loom::disposer {Disposer}
use std::ref {Ref, Ref.new, Ref.get, Ref.modify}
use std::list {List.length, List.intercalate}

def note (r : Ref (List String)) (s : String) : IO Unit :=
    Ref.modify r (fn (xs : List String) => List.append xs [s])

def silent_sink : String -> IO Unit :=
    fn (_ : String) => IO.pure unit

def ok_unit : IO (Result String Unit) :=
    IO.pure (Result.ok unit)

/// One bracketed resource whose teardown records `name`.
def unit_bracket (r : Ref (List String)) (name : String) : Strand Active Active Unit :=
    Strand.bracket (fn (_ : Unit) => IO.pure unit) (fn (_ : Unit) => do {
        note r name;
        ok_unit
    })

/// Three mounts composed with the companion `Monad (Strand I I)` instance.
def three (r : Ref (List String)) : Strand Active Active Unit :=
    Monad.bind (unit_bracket r "a") (fn (_ : Unit) =>
        Monad.bind (unit_bracket r "b") (fn (_ : Unit) => unit_bracket r "c"))

#[test]
def test_disposal_is_lifo : IO Bool := do {
    let r <- Ref.new List.empty;
    let pr <- Strand.run (three r);
    let _ <- Strand.dispose silent_sink (StrandRun.disposers pr);
    let xs <- Ref.get r;
    return (String.beq (List.intercalate "," xs) "c,b,a")
}

/// A disposer that fails mid-stack reports its error and does not stop the
/// rest; the second strand's teardown runs first.
#[test]
def test_a_failing_disposer_does_not_stop_the_rest : IO Bool := do {
    let r <- Ref.new List.empty;
    let bad : Strand Active Active Unit :=
        Strand.bracket (fn (_ : Unit) => IO.pure unit) (fn (_ : Unit) => IO.pure (Result.err "boom"));
    let good : Strand Active Active Unit := unit_bracket r "good";
    let pr <- Strand.run (Monad.bind bad (fn (_ : Unit) => good));
    let _ <- Strand.dispose (fn (e : String) => note r e) (StrandRun.disposers pr);
    let xs <- Ref.get r;
    return (I64.beq (List.length xs) 2
        && String.beq (List.intercalate "," xs) "good,boom")
}

def pure_active (a : A) : Strand Active Active A :=
    Monad.pure a

/// `Pending -> Active` through `IndexedMonad.bind`: the transition is
/// compile-time, the value is the runtime check.
#[test]
def test_the_index_transition_composes : IO Bool := do {
    let p : Strand Pending Active I64 := Strand.pending (fn (_ : Unit) => IO.pure (StrandRun.run_result 42 List.empty));
    let s : Strand Pending Active I64 := IndexedMonad.bind p (fn (n : I64) => pure_active (n + 1));
    let pr <- Strand.run s;
    return (I64.beq (StrandRun.value pr) 43 && I64.beq (List.length (StrandRun.disposers pr)) 0)
}

/// `Active -> Disposed`: `sealed` runs the stack it carries.
#[test]
def test_sealed_disposes : IO Bool := do {
    let r <- Ref.new List.empty;
    let d : Disposer := { run := fn (_ : Unit) => do { note r "sealed"; ok_unit } };
    let ds : List Disposer := List.cons d List.empty;
    let s : Strand Active Disposed Unit := Strand.sealed silent_sink ds;
    let _ <- Strand.run s;
    let xs <- Ref.get r;
    return (String.beq (List.intercalate "," xs) "sealed")
}

#[test]
def test_pure_registers_no_disposers : IO Bool := do {
    let s : Strand Active Active I64 := Monad.pure 7;
    let pr <- Strand.run s;
    return (I64.beq (StrandRun.value pr) 7 && I64.beq (List.length (StrandRun.disposers pr)) 0)
}
