/// Runtime tests for `init/src/view.mo`'s `Cell`.
///
/// Separate from `view.mo` because a `#[test]` in a file re-exported by
/// `init/src/lib.mo` is undiscoverable (AGENTS.md's testing section);
/// `view.mo` is deliberately NOT re-exported, and these live here.
///
/// The type-level half (linearity, no Copy, no capture, no Shared) is
/// asserted by `lang/src/module.mo`'s e2e fixtures; these pin the four
/// natives round-tripping on a real runtime.
use init::view {Cell, Empty, Full, Slice, SliceError, Slot}

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

// ── Slice ────────────────────────────────────────────────────────────

def slice_free_and (s : Slice 3 I64) (answer : Bool) : Bool :=
    let _ := Slice.free s in answer

def slice_length_is (s : Slice 3 I64) (want : I64) : Bool :=
    match Slice.length s {
        Pair.pair n s1 => slice_free_and s1 (I64.beq n want),
    }

#[test]
def test_slice_of_list_reports_its_length : Bool :=
    match Slice.of_list [10, 20, 30] 3 {
        Result.ok s => slice_length_is s 3,
        Result.err _e => false,
    }

/// The index is a runtime-checked contract: a list that does not have it
/// is refused, with the actual length.
#[test]
def test_slice_of_list_rejects_a_wrong_length : Bool :=
    match Slice.of_list [1, 2, 3] 2 {
        Result.ok s => let _ := Slice.free s in false,
        Result.err e => I64.beq e.actual 3,
    }

def slice_read_zero_then_one (first : I64) (s : Slice 3 I64) : Bool :=
    match Slice.get s 1 {
        Result.ok p => match p {
            Pair.pair v s1 => slice_free_and s1 (I64.beq first 10 && I64.beq v 20),
        },
        Result.err s1 => slice_free_and s1 false,
    }

#[test]
def test_slice_get_reads_elements : Bool :=
    match Slice.of_list [10, 20, 30] 3 {
        Result.ok s => match Slice.get s 0 {
            Result.ok p => match p {
                Pair.pair first s1 => slice_read_zero_then_one first s1,
            },
            Result.err s1 => slice_free_and s1 false,
        },
        Result.err _e => false,
    }

def slice_read_after_set (s : Slice 3 I64) : Bool :=
    match Slice.get s 1 {
        Result.ok p => match p {
            Pair.pair v s1 => slice_free_and s1 (I64.beq v 99),
        },
        Result.err s1 => slice_free_and s1 false,
    }

#[test]
def test_slice_set_writes_through : Bool :=
    match Slice.of_list [1, 2, 3] 3 {
        Result.ok s => match Slice.set s 1 99 {
            Result.ok s1 => slice_read_after_set s1,
            Result.err s1 => slice_free_and s1 false,
        },
        Result.err _e => false,
    }

/// An out-of-range read is an error carrying the handle, not a lost
/// slice: the error arm can still free it.
#[test]
def test_slice_get_out_of_range_keeps_the_handle : Bool :=
    match Slice.of_list [1, 2, 3] 3 {
        Result.ok s => match Slice.get s 3 {
            Result.ok p => match p {
                Pair.pair _v s1 => slice_free_and s1 false,
            },
            Result.err s1 => slice_free_and s1 true,
        },
        Result.err _e => false,
    }

#[test]
def test_slice_set_out_of_range_keeps_the_handle : Bool :=
    match Slice.of_list [1, 2, 3] 3 {
        Result.ok s => match Slice.set s 3 99 {
            Result.ok s1 => slice_free_and s1 false,
            Result.err s1 => slice_free_and s1 true,
        },
        Result.err _e => false,
    }

def split_half_lengths (s : Slice 4 I64) : Bool :=
    match Slice.length s {
        Pair.pair n s1 => slice_free_and4 s1 (I64.beq n 4),
    }

def slice_free_and4 (s : Slice 4 I64) (answer : Bool) : Bool :=
    let _ := Slice.free s in answer

/// The halves are indexed: `split_at 2` on `Slice 4` gives two
/// `Slice 2`s (the right half is `Nat.sub 4 2`, which reduces).
#[test]
def test_slice_split_halves_are_indexed : Bool :=
    match Slice.of_list [1, 2, 3, 4] 4 {
        Result.ok s => match Slice.split_at s 2 {
            Result.ok p => match p {
                Pair.pair l r =>
                    let pl := Slice.length l in
                    match pl {
                        Pair.pair llen l1 =>
                            let pr := Slice.length r in
                            match pr {
                                Pair.pair rlen r1 =>
                                    let _a := Slice.free l1 in
                                    let _b := Slice.free r1 in
                                    I64.beq llen 2 && I64.beq rlen 2,
                            },
                    },
            },
            Result.err s1 => slice_free_and4 s1 false,
        },
        Result.err _e => false,
    }

/// The halves see the SAME elements: reading the left half's last element
/// and the right half's first shows the split point. The right half's type
/// is spelled `Nat.sub 4 2` because that is what `split_at` gives it; the
/// self-hosted checker reduces it to `2`, and the spelling is what the
/// Rust host (which has no `Nat` reduction) matches.
#[test]
def test_slice_split_ranges_are_disjoint : Bool :=
    match Slice.of_list [1, 2, 3, 4] 4 {
        Result.ok s => match Slice.split_at s 2 {
            Result.ok p => match p {
                Pair.pair l r => split_read_ends l r,
            },
            Result.err s1 => slice_free_and4 s1 false,
        },
        Result.err _e => false,
    }

def split_read_ends (l : Slice 2 I64) (r : Slice (Nat.sub 4 2) I64) : Bool :=
    match Slice.get l 1 {
        Result.ok p => match p {
            Pair.pair lv l1 => split_read_right r lv,
        },
        Result.err l1 => let _a := Slice.free l1 in let _b := Slice.free r in false,
    }

def split_read_right (r : Slice (Nat.sub 4 2) I64) (lv : I64) : Bool :=
    match Slice.get r 0 {
        Result.ok p => match p {
            Pair.pair rv r1 => let _a := Slice.free r1 in I64.beq lv 2 && I64.beq rv 3,
        },
        Result.err r1 => let _a := Slice.free r1 in false,
    }

def slice_free_and_string (s : Slice 3 String) (answer : Bool) : Bool :=
    let _ := Slice.free s in answer

/// A `String` element: the backing array must stay GC-SCANNED, or Boehm
/// collects the bytes the elements point at.
#[test]
def test_slice_holds_strings : Bool :=
    match Slice.of_list ["a", "bb", "ccc"] 3 {
        Result.ok s => match Slice.get s 2 {
            Result.ok p => match p {
                Pair.pair v s1 => slice_free_and_string s1 (String.beq v "ccc"),
            },
            Result.err s1 => slice_free_and_string s1 false,
        },
        Result.err _e => false,
    }
