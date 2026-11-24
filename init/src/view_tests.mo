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

def finish_with_42 (p : Pair I64 (Cell I64)) : IO Bool :=
    match p {
        Pair.pair w c => do {
            let _ <- Cell.free c;
            return (I64.beq w 42)
        },
    }

def read_again (c : Cell I64) : IO Bool := do {
    let p <- Cell.get c;
    finish_with_42 p
}

def write_again (p : Pair I64 (Cell I64)) : IO Bool :=
    match p {
        Pair.pair v c => do {
            let c2 <- Cell.set c (I64.add v 1);
            read_again c2
        },
    }

#[test]
def test_cell_roundtrip : IO Bool := do {
    let c0 <- Cell.new 41;
    let p <- Cell.get c0;
    write_again p
}

/// The FUSED shape: every continuation consumes the accessor's result
/// immediately, so codegen lowers the whole flow to one function and no
/// `Pair`/`IO` box (`try_compile_view_bind_db`). The escaping tests
/// above stay the control -- they must keep the boxed path working.
#[test]
def test_cell_fused_roundtrip : IO Bool := do {
    let c0 <- Cell.new 41;
    let p <- Cell.get c0;
    match p {
        Pair.pair x c1 => do {
            let c2 <- Cell.set c1 (I64.add x 1);
            let p2 <- Cell.get c2;
            match p2 {
                Pair.pair y c3 => do {
                    let _ <- Cell.free c3;
                    return (I64.beq y 42)
                },
            }
        },
    }
}

#[test]
def test_cell_holds_a_string : IO Bool := do {
    // `String` is `Copy` and a bare pointer, so the Cell block must stay
    // GC-scanned (a `monad_alloc_atomic` block would let Boehm collect
    // these bytes).
    let c <- Cell.new "hi";
    let p <- Cell.get c;
    match p {
        Pair.pair s c2 => do {
            let _ <- Cell.free c2;
            return (String.beq s "hi")
        },
    }
}

// ── Slot ────────────────────────────────────────────────────────────

/// empty -> fill -> take -> fill -> take -> free. The state is in the type,
/// so each step is a different `Slot` instantiation.
#[test]
def test_slot_roundtrip : IO Bool := do {
    let s0 : Slot Empty I64 <- Slot.empty;
    let s1 <- Slot.fill s0 41;
    let p1 <- Slot.take s1;
    match p1 {
        Pair.pair v s2 => do {
            let ok1 := I64.beq v 41;
            let s3 <- Slot.fill s2 42;
            let p2 <- Slot.take s3;
            match p2 {
                Pair.pair w s4 => do {
                    let _ <- Slot.free s4;
                    return (ok1 && I64.beq w 42)
                },
            }
        },
    }
}

/// `peek` reads a `Copy` payload without emptying the slot, so a following
/// `take` still finds it.
#[test]
def test_slot_peek_keeps_the_value : IO Bool := do {
    let s0 <- Slot.new 7;
    let p1 <- Slot.peek s0;
    match p1 {
        Pair.pair a s1 => do {
            let ok1 := I64.beq a 7;
            let p2 <- Slot.take s1;
            match p2 {
                Pair.pair b s2 => do {
                    let _ <- Slot.free s2;
                    return (ok1 && I64.beq b 7)
                },
            }
        },
    }
}

/// The point of `Slot` over `Cell`: a NON-`Copy` payload moves in and out.
/// `List I64` has no `Copy` instance, so `Cell` cannot hold it.
#[test]
def test_slot_moves_a_non_copy_payload : IO Bool := do {
    let xs : List I64 := [1, 2, 3];
    let s0 <- Slot.new xs;
    let p <- Slot.take s0;
    match p {
        Pair.pair ys s1 => do {
            let _ <- Slot.free s1;
            return (match List.get 0 ys {
                Option.some a => I64.beq a 1,
                Option.none => false,
            })
        },
    }
}

/// A fresh empty slot can be consumed directly; this is the shape
/// `Slot.empty`'s `A` annotation is for.
#[test]
def test_slot_empty_can_be_freed : IO Bool := do {
    let s : Slot Empty I64 <- Slot.empty;
    let _ <- Slot.free s;
    return true
}

// ── Swap ────────────────────────────────────────────────────────────

def cell_swap_read (a : Cell I64) (b : Cell I64) : IO Bool := do {
    let pa <- Cell.get a;
    match pa {
        Pair.pair va a2 => cell_swap_read_b va a2 b,
    }
}

def cell_swap_read_b (va : I64) (a2 : Cell I64) (b : Cell I64) : IO Bool := do {
    let _ <- Cell.free a2;
    let pb <- Cell.get b;
    match pb {
        Pair.pair vb b2 => cell_swap_read_done va vb b2,
    }
}

def cell_swap_read_done (va : I64) (vb : I64) (b2 : Cell I64) : IO Bool := do {
    let _ <- Cell.free b2;
    return (I64.beq va 42 && I64.beq vb 41)
}

#[test]
def test_cell_swap_exchanges_payloads : IO Bool := do {
    let a <- Cell.new 41;
    let b <- Cell.new 42;
    let p <- Cell.swap a b;
    match p {
        Pair.pair a2 b2 => cell_swap_read a2 b2,
    }
}

/// A `String` payload goes through the same swap (both cells stay
/// GC-scanned).
#[test]
def test_cell_swap_exchanges_strings : IO Bool := do {
    let a <- Cell.new "left";
    let b <- Cell.new "right";
    let p <- Cell.swap a b;
    match p {
        Pair.pair a2 b2 => cell_swap_strings_read a2 b2,
    }
}

def cell_swap_strings_read (a : Cell String) (b : Cell String) : IO Bool := do {
    let pa <- Cell.get a;
    match pa {
        Pair.pair va a2 => cell_swap_strings_b va a2 b,
    }
}

def cell_swap_strings_b (va : String) (a2 : Cell String) (b : Cell String) : IO Bool := do {
    let _ <- Cell.free a2;
    let pb <- Cell.get b;
    match pb {
        Pair.pair vb b2 => cell_swap_strings_done va vb b2,
    }
}

def cell_swap_strings_done (va : String) (vb : String) (b2 : Cell String) : IO Bool := do {
    let _ <- Cell.free b2;
    return (String.beq va "right" && String.beq vb "left")
}

def slot_swap_read (a : Slot Full (List I64)) (b : Slot Full (List I64)) : IO Bool := do {
    let pa <- Slot.take a;
    match pa {
        Pair.pair va ea => slot_swap_read_b va ea b,
    }
}

def slot_swap_read_b (va : List I64) (ea : Slot Empty (List I64)) (b : Slot Full (List I64)) : IO Bool := do {
    let _ <- Slot.free ea;
    let pb <- Slot.take b;
    match pb {
        Pair.pair vb eb => slot_swap_read_done va vb eb,
    }
}

def slot_swap_read_done (va : List I64) (vb : List I64) (eb : Slot Empty (List I64)) : IO Bool := do {
    let _ <- Slot.free eb;
    return (I64.beq (List.length va) 1i64 && I64.beq (List.length vb) 2i64)
}

/// The point of `Slot.swap` over `Cell.swap`: neither payload is `Copy`, so
/// nothing is duplicated — the two lists move between the handles.
#[test]
def test_slot_swap_moves_non_copy_payloads : IO Bool := do {
    let a <- Slot.new [1, 2];
    let b <- Slot.new [3];
    let p <- Slot.swap a b;
    match p {
        Pair.pair a2 b2 => slot_swap_read a2 b2,
    }
}
