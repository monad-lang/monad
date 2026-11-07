/// View-type safety rules through the REAL load + check path, with
/// `init::view`'s `Cell` in scope.
///
/// `lang/src/module.mo`'s `classified_probe` builds its scope from the raw
/// parsed decls, so it cannot see `init::view` and uses local `#[linear]`
/// fixtures instead. These fixtures go through `elaborate_loaded_modules`
/// exactly as `monad check` does, which is what exercises the do-bind
/// type attribution (`usage.mo`'s `init_payload_type`) -- the path that
/// makes `let c <- Cell.new 1` a checked linear binder rather than a hole.
use lib::typecheck_harness {check_source_diags, diags_contain}

/// `let c <- Cell.new 1` leaves the binder's WRITTEN type a hole. The
/// collector attributes it from the initializer's `IO (Cell A)` payload,
/// so a second use is rejected. Without that attribution every do-bound
/// Cell would fail open and double-use would be accepted.
#[test]
def test_a_do_bound_cell_cannot_be_used_twice : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def bad : IO Unit := do {\n"
        ++ "  let c <- Cell.new 1;\n"
        ++ "  let _ <- Cell.free c;\n"
        ++ "  let _ <- Cell.free c;\n"
        ++ "  return unit\n"
        ++ "}\n";
    let diags <- check_source_diags src "do_bind_twice";
    return (diags_contain "is used 2 times" diags)
}

/// The acceptance twin: one use, after an intervening do-bind. That use is
/// inside a `Monad.bind` continuation lambda, which is NOT a closure -- the
/// capture rule must not fire on it.
#[test]
def test_a_do_bound_cell_may_be_used_after_an_intervening_bind : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def good : IO Unit := do {\n"
        ++ "  let c <- Cell.new 1;\n"
        ++ "  let _ <- IO.println \"a\";\n"
        ++ "  let _ <- Cell.free c;\n"
        ++ "  return unit\n"
        ++ "}\n";
    let diags <- check_source_diags src "do_bind_good";
    return (List.is_empty diags)
}

#[test]
def test_a_cell_captured_by_a_real_closure_is_rejected : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def bad (c : Cell I64) : I64 :=\n"
        ++ "  let f := fn (u : Unit) => c in 0\n";
    let diags <- check_source_diags src "capture";
    return (diags_contain "is captured by a closure" diags)
}

/// `Ref (Cell A)`'s head is `Ref`, not linear, so the direct rule does not
/// fire. Wrapping the Ref in `Shared` is the same hazard one level down:
/// `Shared` is `Copy`, and `Ref.get` twice would yield two Cells.
#[test]
def test_a_ref_holding_a_cell_may_not_be_shared : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "use init::shared {Shared}\n"
        ++ "use std::ref {Ref}\n"
        ++ "def bad (r : Ref (Cell I64)) : Unit := let s := Shared.of r in unit\n";
    let diags <- check_source_diags src "ref_shared";
    return (diags_contain "is stored in a re-readable container" diags)
}

#[test]
def test_a_copy_instance_for_a_cell_is_rejected : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "instance Copy (Cell I64) {\n"
        ++ "  def copy (c : Cell I64) : Pair (Cell I64) (Cell I64) := Pair.pair c c\n"
        ++ "}\n";
    let diags <- check_source_diags src "copy_instance";
    return (diags_contain "not allowed for the linear or proof type" diags)
}

// ── Slot: the state-in-the-type handle ──────────────────────────────

/// A `Slot` is `#[linear]`, so dropping one is `linear_unused` (the same
/// rule that makes a leaked Cell an error once `#[linear]` is on it).
#[test]
def test_a_dropped_slot_is_never_used : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full I64) : I64 := 0\n";
    let diags <- check_source_diags src "slot_dropped";
    return (diags_contain "never used" diags)
}

#[test]
def test_a_slot_cannot_be_used_twice : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full I64) : IO Unit := do {\n"
        ++ "  let _ <- Slot.take s;\n"
        ++ "  let _ <- Slot.take s;\n"
        ++ "  return unit\n"
        ++ "}\n";
    let diags <- check_source_diags src "slot_twice";
    return (diags_contain "is used 2 times" diags)
}

/// `Slot.free` consumes an EMPTY slot only; freeing a full one does not
/// typecheck (a linear payload must be moved out first).
#[test]
def test_a_full_slot_cannot_be_freed : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full I64) : IO Unit := Slot.free s\n";
    let diags <- check_source_diags src "slot_free_full";
    return (diags_contain "expected (Slot Empty I64), found (Slot Full I64)" diags)
}

#[test]
def test_a_slot_captured_by_a_closure_is_rejected : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full I64) : I64 :=\n"
        ++ "  let f := fn (u : Unit) => s in 0\n";
    let diags <- check_source_diags src "slot_capture";
    return (diags_contain "is captured by a closure" diags)
}

#[test]
def test_a_copy_instance_for_a_slot_is_rejected : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "instance Copy (Slot Full I64) {\n"
        ++ "  def copy (s : Slot Full I64) : Pair (Slot Full I64) (Slot Full I64) := Pair.pair s s\n"
        ++ "}\n";
    let diags <- check_source_diags src "slot_copy";
    return (diags_contain "is not allowed for the linear or proof type" diags)
}
