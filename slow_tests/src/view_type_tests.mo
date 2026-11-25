/// View-type safety rules through the REAL load + check path, with
/// `init::view`'s `Cell` in scope.
///
/// `lang/src/module.mo`'s `classified_probe` builds its scope from the raw
/// parsed decls, so it cannot see `init::view` and uses local `#[linear]`
/// fixtures instead. These fixtures go through `elaborate_loaded_modules`
/// exactly as `monad check` does, which is what exercises the plain-`let`
/// type attribution (`usage.mo`'s `init_value_type`) -- the path that makes
/// `let c := Cell.new 1` a checked linear binder rather than a hole.
use lib::typecheck_harness {check_source_diags, diags_contain}

/// `let c := Cell.new 1` leaves the binder's WRITTEN type a hole. The
/// collector attributes it from the initializer's value type (`Cell A`
/// mentions a linear type), so a second use is rejected. Without that
/// attribution every let-bound Cell would fail open and double use would
/// be accepted.
#[test]
def test_a_let_bound_cell_cannot_be_used_twice : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def bad : Unit :=\n"
        ++ "  let c := Cell.new 1 in\n"
        ++ "  let _ := Cell.free c in\n"
        ++ "  let _ := Cell.free c in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "let_bind_twice";
    return (diags_contain "is used 2 times" diags)
}

/// The acceptance twin: one use.
#[test]
def test_a_let_bound_cell_may_be_used_once : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def good : Unit :=\n"
        ++ "  let c := Cell.new 1 in\n"
        ++ "  Cell.free c\n";
    let diags <- check_source_diags src "let_bind_good";
    return (List.is_empty diags)
}

/// ...and weakening is not a licence: a linear binder may not be dropped.
#[test]
def test_a_let_bound_cell_must_be_used : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def bad : Unit :=\n"
        ++ "  let c := Cell.new 1 in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "let_bind_unused";
    return (diags_contain "never used" diags)
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
        ++ "def bad (s : Slot Full I64) : Unit :=\n"
        ++ "  let _ := Slot.take s in\n"
        ++ "  let _ := Slot.take s in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "slot_twice";
    return (diags_contain "is used 2 times" diags)
}

/// `Slot.free` consumes an EMPTY slot only; freeing a full one does not
/// typecheck (a linear payload must be moved out first).
#[test]
def test_a_full_slot_cannot_be_freed : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full I64) : Unit := Slot.free s\n";
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

// ── The linked list (`init/src/linked.mo`) ─────────────────────────
//
// The list is the "pointer swapping without pointers" demonstration: a node is
// a linear `Slot`, so a cursor is a handle that cannot be copied. These pins
// are what makes the demonstration a *safety* claim rather than a style.

/// A list handle is consumed by a walk; two walks need two handles.
#[test]
def test_a_link_cannot_be_walked_twice : IO Bool := do {
    let src : String :=
        "use init::linked {Link, Linked.to_list}\n"
        ++ "def bad (l : Link I64) : Unit :=\n"
        ++ "  let _ := Linked.to_list l in\n"
        ++ "  let _ := Linked.to_list l in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "link_twice";
    return (diags_contain "is used 2 times" diags)
}

/// ...and a *node* is one handle too: emptying it twice is a use-after-move,
/// which is exactly the two-cursors bug a C list cannot catch.
#[test]
def test_a_node_cannot_be_taken_twice : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "use init::linked {Link}\n"
        ++ "def bad (l : Link I64) : Unit :=\n"
        ++ "  match l {\n"
        ++ "    Link.node s =>\n"
        ++ "      let _ := Slot.take s in\n"
        ++ "      let _ := Slot.take s in\n"
        ++ "      unit,\n"
        ++ "    Link.nil => unit,\n"
        ++ "  }\n";
    let diags <- check_source_diags src "node_twice";
    return (diags_contain "is used 2 times" diags)
}

/// A list handle may not be lent: `Shared` is `Copy`, and two readers would
/// both reach the same nodes.
#[test]
def test_a_link_may_not_be_shared : IO Bool := do {
    let src : String :=
        "use init::linked {Link}\n"
        ++ "def bad (l : Link I64) : Unit :=\n"
        ++ "  let _ := Shared.of l in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "link_shared";
    return (diags_contain "re-readable container" diags)
}

/// The acceptance twin: a reverse followed by a fold-out is well typed.
#[test]
def test_a_link_reverse_and_fold_out_is_accepted : IO Bool := do {
    let src : String :=
        "use init::linked {Link, Linked.from_list, Linked.reverse, Linked.to_list}\n"
        ++ "def good : Unit :=\n"
        ++ "  let l := Linked.from_list [1, 2, 3] in\n"
        ++ "  let r := Linked.reverse l in\n"
        ++ "  let _ := Linked.to_list r in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "link_good";
    return (List.is_empty diags)
}

// ── The swap functions (`init/src/view.mo`) ────────────────────────

/// A swap exchanges two handles; it cannot be run on ONE handle twice, because
/// the second use would need a second `Cell` from the same allocation.
#[test]
def test_a_cell_swap_needs_two_distinct_cells : IO Bool := do {
    let src : String :=
        "use init::view {Cell}\n"
        ++ "def bad (c : Cell I64) : Unit :=\n"
        ++ "  let _ := Cell.swap c c in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "cell_swap_alias";
    return (diags_contain "is used 2 times" diags)
}

#[test]
def test_a_slot_swap_needs_two_distinct_slots : IO Bool := do {
    let src : String :=
        "use init::view {Full, Slot}\n"
        ++ "def bad (s : Slot Full (List I64)) : Unit :=\n"
        ++ "  let _ := Slot.swap s s in\n"
        ++ "  unit\n";
    let diags <- check_source_diags src "slot_swap_alias";
    return (diags_contain "is used 2 times" diags)
}

// ─── P12: a global value may not be linear ──────────────────────────

/// A nullary def is a VALUE, not a function: the source can only name it,
/// so every reference would be the same handle (and the Rust host would
/// memoise it while compiled code re-runs it). The old guard was that a
/// view handle could only be produced in `IO`; a pure `Cell.new` removes it.
#[test]
def test_a_global_linear_value_is_rejected : IO Bool := do {
    let src : String :=
        "#[linear] type L { l_mk }\n"
        ++ "def c : L := L.mk\n";
    let diags <- check_source_diags src "global_linear";
    return (diags_contain "cannot be a global value" diags)
}

/// The twin: one parameter makes it a function, and each application makes
/// its own value.
#[test]
def test_a_linear_producing_function_is_accepted : IO Bool := do {
    let src : String :=
        "#[linear] type L { l_mk }\n"
        ++ "def mk (u : Unit) : L := L.mk\n";
    let diags <- check_source_diags src "linear_function";
    return (List.is_empty diags)
}
