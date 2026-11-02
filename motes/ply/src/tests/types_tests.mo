// Phase 0's derive gate: every `#[derive BEq]` in `types.mo` resolves and
// behaves structurally. The plan's Phase 0 gate asks for exactly this ("every
// `#[derive BEq]` resolves"), and a derive that silently failed to expand
// would still let `monad check` pass -- so the check needs a witness that the
// generated `==` exists and answers.
//
// `Selection` and `Change` are structs (derived field-wise `BEq`); `Mode` is
// an inductive (derived constructor-index + field-wise `BEq`).
//
// One comparison per test on purpose: these types are affine (no `Copy`
// instance), so a single binding compared against two different values draws
// the "used 2 times but is affine" warning. Comparing exactly one pair keeps
// each binding used once.

use lib::types {Selection, Change, Mode}

#[test]
def selection_beq_equal : Bool :=
    let a : Selection := { anchor := 1, head := 2 } in
    let b : Selection := { anchor := 1, head := 2 } in
    a == b

#[test]
def selection_beq_differs_on_anchor : Bool :=
    let a : Selection := { anchor := 1, head := 2 } in
    let c : Selection := { anchor := 0, head := 2 } in
    Bool.not (a == c)

#[test]
def selection_beq_differs_on_head : Bool :=
    let a : Selection := { anchor := 1, head := 2 } in
    let c : Selection := { anchor := 1, head := 3 } in
    Bool.not (a == c)

#[test]
def change_beq_equal : Bool :=
    let a : Change := { start := 0, stop := 3, text := "abc" } in
    let b : Change := { start := 0, stop := 3, text := "abc" } in
    a == b

#[test]
def change_beq_differs_on_text : Bool :=
    let a : Change := { start := 0, stop := 3, text := "abc" } in
    let c : Change := { start := 0, stop := 3, text := "abd" } in
    Bool.not (a == c)

#[test]
def mode_beq_same_constructor : Bool :=
    let a : Mode := Mode.insert in
    let b : Mode := Mode.insert in
    a == b

#[test]
def mode_beq_distinguishes_constructors : Bool :=
    let a : Mode := Mode.insert in
    let b : Mode := Mode.normal in
    Bool.not (a == b)

#[test]
def mode_beq_compares_payloads : Bool :=
    let a : Mode := Mode.command "w" in
    let c : Mode := Mode.command "q" in
    Bool.not (a == c)
