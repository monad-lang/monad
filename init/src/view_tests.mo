/// Runtime tests for `init/src/view.mo`'s `Cell`.
///
/// Separate from `view.mo` because a `#[test]` in a file re-exported by
/// `init/src/lib.mo` is undiscoverable (AGENTS.md's testing section);
/// `view.mo` is deliberately NOT re-exported, and these live here.
///
/// The type-level half (linearity, no Copy, no capture, no Shared) is
/// asserted by `lang/src/module.mo`'s e2e fixtures; these pin the four
/// natives round-tripping on a real runtime.
use init::view {Cell}

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
