/// Runtime tests for `init/src/view.mo`'s `Cell`.
///
/// Separate from `view.mo` because a `#[test]` in a file re-exported by
/// `init/src/lib.mo` is undiscoverable (AGENTS.md's testing section);
/// `view.mo` is deliberately NOT re-exported, and these live here.
///
/// The type-level half (linearity, no Copy, no capture, no Shared) is
/// asserted by `lang/src/module.mo`'s e2e fixtures; these pin the four
/// natives round-tripping on a real runtime.
use init::view {Cell, Empty, Full, Slot}

def finish_with_42 (p : Pair I64 (Cell I64)) : Bool :=
    match p {
        Pair.pair w c => let _ := Cell.free c in I64.beq w 42,
    }

def read_again (c : Cell I64) : Bool :=
    let p := Cell.get c in finish_with_42 p

def write_again (p : Pair I64 (Cell I64)) : Bool :=
    match p {
        Pair.pair v c => let c2 := Cell.set c (I64.add v 1) in read_again c2,
    }

#[test]
def test_cell_roundtrip : Bool :=
    let c0 := Cell.new 41 in
    let p := Cell.get c0 in
    write_again p

/// The FUSED shape: every continuation consumes the accessor's result
/// immediately, so codegen lowers the whole flow to one function and no
/// `Pair` box (`try_compile_view_bind_db`). The escaping tests above
/// stay the control -- they must keep the boxed path working.
#[test]
def test_cell_fused_roundtrip : Bool :=
    let c0 := Cell.new 41 in
    let p := Cell.get c0 in
    match p {
        Pair.pair x c1 =>
            let c2 := Cell.set c1 (I64.add x 1) in
            let p2 := Cell.get c2 in
            match p2 {
                Pair.pair y c3 => let _ := Cell.free c3 in I64.beq y 42,
            },
    }

#[test]
def test_cell_holds_a_string : Bool :=
    // `String` is `Copy` and a bare pointer, so the Cell block must stay
    // GC-scanned (a `monad_alloc_atomic` block would let Boehm collect
    // these bytes).
    let c := Cell.new "hi" in
    let p := Cell.get c in
    match p {
        Pair.pair s c2 => let _ := Cell.free c2 in String.beq s "hi",
    }

// ── Slot ────────────────────────────────────────────────────────────

/// empty -> fill -> take -> fill -> take -> free. The state is in the type,
/// so each step is a different `Slot` instantiation.
#[test]
def test_slot_roundtrip : Bool :=
    let s0 : Slot Empty I64 := Slot.empty in
    let s1 := Slot.fill s0 41 in
    let p1 := Slot.take s1 in
    match p1 {
        Pair.pair v s2 =>
            let ok1 := I64.beq v 41 in
            let s3 := Slot.fill s2 42 in
            let p2 := Slot.take s3 in
            match p2 {
                Pair.pair w s4 => let _ := Slot.free s4 in ok1 && I64.beq w 42,
            },
    }

/// `peek` reads a `Copy` payload without emptying the slot, so a following
/// `take` still finds it.
#[test]
def test_slot_peek_keeps_the_value : Bool :=
    let s0 := Slot.new 7 in
    let p1 := Slot.peek s0 in
    match p1 {
        Pair.pair a s1 =>
            let ok1 := I64.beq a 7 in
            let p2 := Slot.take s1 in
            match p2 {
                Pair.pair b s2 => let _ := Slot.free s2 in ok1 && I64.beq b 7,
            },
    }

/// The point of `Slot` over `Cell`: a NON-`Copy` payload moves in and out.
/// `List I64` has no `Copy` instance, so `Cell` cannot hold it.
#[test]
def test_slot_moves_a_non_copy_payload : Bool :=
    let xs : List I64 := [1, 2, 3] in
    let s0 := Slot.new xs in
    let p := Slot.take s0 in
    match p {
        Pair.pair ys s1 =>
            let _ := Slot.free s1 in
            match List.get 0 ys {
                Option.some a => I64.beq a 1,
                Option.none => false,
            },
    }

/// A fresh empty slot can be consumed directly; this is the shape
/// `Slot.empty`'s `A` annotation is for.
#[test]
def test_slot_empty_can_be_freed : Bool :=
    let s : Slot Empty I64 := Slot.empty in
    let _ := Slot.free s in
    true

// ── Swap ────────────────────────────────────────────────────────────

def cell_swap_read (a : Cell I64) (b : Cell I64) : Bool :=
    let pa := Cell.get a in
    match pa {
        Pair.pair va a2 => cell_swap_read_b va a2 b,
    }

def cell_swap_read_b (va : I64) (a2 : Cell I64) (b : Cell I64) : Bool :=
    let _ := Cell.free a2 in
    let pb := Cell.get b in
    match pb {
        Pair.pair vb b2 => cell_swap_read_done va vb b2,
    }

def cell_swap_read_done (va : I64) (vb : I64) (b2 : Cell I64) : Bool :=
    let _ := Cell.free b2 in
    I64.beq va 42 && I64.beq vb 41

#[test]
def test_cell_swap_exchanges_payloads : Bool :=
    let a := Cell.new 41 in
    let b := Cell.new 42 in
    let p := Cell.swap a b in
    match p {
        Pair.pair a2 b2 => cell_swap_read a2 b2,
    }

/// A `String` payload goes through the same swap (both cells stay
/// GC-scanned).
#[test]
def test_cell_swap_exchanges_strings : Bool :=
    let a := Cell.new "left" in
    let b := Cell.new "right" in
    let p := Cell.swap a b in
    match p {
        Pair.pair a2 b2 => cell_swap_strings_read a2 b2,
    }

def cell_swap_strings_read (a : Cell String) (b : Cell String) : Bool :=
    let pa := Cell.get a in
    match pa {
        Pair.pair va a2 => cell_swap_strings_b va a2 b,
    }

def cell_swap_strings_b (va : String) (a2 : Cell String) (b : Cell String) : Bool :=
    let _ := Cell.free a2 in
    let pb := Cell.get b in
    match pb {
        Pair.pair vb b2 => cell_swap_strings_done va vb b2,
    }

def cell_swap_strings_done (va : String) (vb : String) (b2 : Cell String) : Bool :=
    let _ := Cell.free b2 in
    String.beq va "right" && String.beq vb "left"

def slot_swap_read (a : Slot Full (List I64)) (b : Slot Full (List I64)) : Bool :=
    let pa := Slot.take a in
    match pa {
        Pair.pair va ea => slot_swap_read_b va ea b,
    }

def slot_swap_read_b (va : List I64) (ea : Slot Empty (List I64)) (b : Slot Full (List I64)) : Bool :=
    let _ := Slot.free ea in
    let pb := Slot.take b in
    match pb {
        Pair.pair vb eb => slot_swap_read_done va vb eb,
    }

def slot_swap_read_done (va : List I64) (vb : List I64) (eb : Slot Empty (List I64)) : Bool :=
    let _ := Slot.free eb in
    I64.beq (List.length va) 1i64 && I64.beq (List.length vb) 2i64

/// The point of `Slot.swap` over `Cell.swap`: neither payload is `Copy`, so
/// nothing is duplicated — the two lists move between the handles.
#[test]
def test_slot_swap_moves_non_copy_payloads : Bool :=
    let a := Slot.new [1, 2] in
    let b := Slot.new [3] in
    let p := Slot.swap a b in
    match p {
        Pair.pair a2 b2 => slot_swap_read a2 b2,
    }
