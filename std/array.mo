/// Standard library: `Array A` -- the O(1)-indexed sequence `std/` did
/// not have.
///
/// **Why this exists.** Nothing in `std/` offered indexed access, so
/// code that wants one routes around the gap: `std/map.mo`'s `HashMap`
/// carries a hand-written `Buckets16` (sixteen named fields with
/// `get_bucket`/`set_bucket` dispatching on an index) precisely because
/// there was no array to hold buckets in, and the DWARF work's
/// offset->line resolution could not use the obvious line-start index
/// with binary search.
///
/// **Representation.** An `Array A` IS its backing constructor: one
/// `Array.mk` whose fields are the elements. That is not an
/// implementation detail this module hides for fun -- it is what makes
/// the natives work on both runtimes without monomorphisation. The Rust
/// host holds a value as `Value::Con { tag, args: Vec<Value> }` and the
/// compiled backend as `Constructor { header, tag, field_count,
/// fields[] }` (`lang/codegen/runtime.c`); both are already
/// GC-managed, indexable, boxed-element vectors with a runtime length,
/// and neither records element types. So `array_*` is generic in `A`
/// for free.
///
/// **Persistent core, mutable builder.** `Array A` is immutable: `set`
/// must copy, which is O(n), so bulk construction goes through
/// `ArrayBuilder A` (filled in place under `IO`, then frozen) and
/// everything after the freeze is O(1) reads on a value pure code can
/// hold.
///
/// **One cost differs by runtime, deliberately.**
/// `Array.set_in_place` is O(1) compiled and O(n) interpreted. A
/// `Value::Con`'s fields are behind an `Arc` shared with the
/// environment slot the builder was read from, so the host copies on
/// write (`Arc::make_mut`) where `monad_set_field` writes the real
/// object. Both are CORRECT; only the cost differs. Under the
/// interpreter, prefer `Array.from_list`/`set` folds.
use std.list {List}

/// The backing constructor. `mk` takes no declared fields: its arity is
/// whatever `array_new`/`array_freeze` allocated it with, which is the
/// array's length. Do not construct one directly -- `Array.new` is the
/// entry point, and a hand-built `Array.mk` has length 0.
type Array A {
    mk,
}

/// A partially-filled `Array` under construction. The same
/// representation as `Array` -- a distinct type only so the type
/// checker keeps the mutable and immutable halves apart, which is what
/// makes `freeze` meaningful.
type ArrayBuilder A {
    mk,
}

#[native array_new]
def Array.new (n : I64) (fill : A) : Array A

#[native array_len]
def Array.length (a : Array A) : I64

/// `Option`, not a panic: an out-of-range read must not be undefined
/// behaviour in the compiled backend, and `String.get`
/// (`init/string.mo`) already returns `Option U8` for the same reason.
#[native array_get]
def Array.get (a : Array A) (i : I64) : Option A

/// The persistent set: copy-then-write, O(n), input untouched. An
/// out-of-range index returns the array unchanged -- the total
/// counterpart of `get`'s `Option.none`.
#[native array_with]
def Array.set (a : Array A) (i : I64) (v : A) : Array A

/// Builder fill. O(1) compiled, O(n) interpreted -- see this module's
/// own doc comment.
#[native array_set_in_place]
def Array.set_in_place (b : ArrayBuilder A) (i : I64) (v : A) : IO Unit

/// COPIES rather than casting. A cast would leave the builder aliasing
/// a value pure code believes is frozen, and a later `set_in_place`
/// would mutate it -- the one way this design can produce a wrong
/// answer rather than a slow one.
#[native array_freeze]
def Array.freeze (b : ArrayBuilder A) : IO (Array A)

/// A fresh `ArrayBuilder` of `n` slots, every one holding `fill`.
/// Shares `array_new`'s implementation -- the two types have the same
/// representation, and the distinction exists so the type checker keeps
/// the mutable and immutable halves apart (see this module's doc
/// comment).
#[native array_new]
def Array.builder (n : I64) (fill : A) : ArrayBuilder A

def Array.is_empty (a : Array A) : Bool := I64.beq (Array.length a) 0

/// `get` with a caller-supplied answer for an out-of-range index, for
/// the common case where the bound is already known good.
def Array.get_or (a : Array A) (i : I64) (fallback : A) : A :=
    match Array.get a i {
        Option.some v => v,
        Option.none => fallback,
    }

/// The empty list case cannot call `Array.new 0 fill` -- there is no
/// element of `A` to hand it, and `Array.new` needs one even at length
/// 0. `array_new` reads its fill only when the length is positive, so
/// the head element is available in exactly the case it is needed.
def Array.from_list (xs : List A) : Array A :=
    match xs {
        List.empty => Array.empty,
        List.cons x rest =>
            let n : I64 := List.length xs in
            let arr : Array A := Array.new n x in
            Array.fill_from arr 1 rest,
    }

/// The length-0 array. Nullary, so it needs no element of `A` at all --
/// `Array.mk` with zero fields IS the empty array, which is why the
/// constructor is declared with none.
def Array.empty : Array A := Array.mk

/// `from_list`'s worker: walk the tail writing each element at the next
/// index. Persistent `set` rather than the builder, so this behaves
/// identically on both runtimes (see the module doc comment).
#[partial]
def Array.fill_from (acc : Array A) (i : I64) (rest : List A) : Array A :=
    match rest {
        List.empty => acc,
        List.cons x more => Array.fill_from (Array.set acc i x) (i + 1) more,
    }

def Array.to_list (a : Array A) : List A := Array.to_list_from a 0

#[partial]
def Array.to_list_from (a : Array A) (i : I64) : List A :=
    if I64.lt i (Array.length a)
    then match Array.get a i {
        Option.some v => List.cons v (Array.to_list_from a (i + 1)),
        Option.none => List.empty,
    }
    else List.empty

def Array.map (f : A -> B) (a : Array A) : Array B :=
    Array.from_list (List.map f (Array.to_list a))

/// Its own recursion rather than `Foldable.foldl` over `to_list`: the
/// class method needs its instance in scope at the call site, and
/// indexing directly is both simpler and avoids building the
/// intermediate list.
def Array.foldl (f : B -> A -> B) (init : B) (a : Array A) : B :=
    Array.foldl_from f init a 0

#[partial]
def Array.foldl_from (f : B -> A -> B) (acc : B) (a : Array A) (i : I64) : B :=
    if I64.lt i (Array.length a)
    then match Array.get a i {
        Option.some v => Array.foldl_from f (f acc v) a (i + 1),
        Option.none => acc,
    }
    else acc

/// One element longer, with `v` at the end. O(n) -- an array is not a
/// growable buffer; build with `from_list` where the whole contents are
/// known.
def Array.push (a : Array A) (v : A) : Array A :=
    Array.from_list (List.append (Array.to_list a) (List.cons v List.empty))

// --- Tests ----------------------------------------------------------
//
// These run under `monad-rs test`, which is the RUST HOST only. The
// compiled-backend half of each native is covered separately by
// `slow_tests/codegen_wired_natives_e2e_tests.mo` -- that split is
// exactly how a half-wired native hides (a native can pass every test
// here and still be wired nowhere in codegen).

#[test]
def test_array_new_and_length : Bool :=
    let a : Array I64 := Array.new 3 7 in
    I64.beq (Array.length a) 3

#[test]
def test_array_new_fills : Bool :=
    let a : Array I64 := Array.new 3 7 in
    match Array.get a 1 {
        Option.some v => I64.beq v 7,
        Option.none => false,
    }

#[test]
def test_array_empty_has_length_zero : Bool :=
    let a : Array I64 := Array.empty in
    I64.beq (Array.length a) 0

/// Every out-of-range read is `Option.none`, never a panic and never a
/// wild read: below zero, exactly at `len`, and past `len`.
#[test]
def test_array_get_bounds : Bool :=
    let a : Array I64 := Array.new 2 5 in
    let below := match Array.get a (0 - 1) { Option.some _ => false, Option.none => true } in
    let at_len := match Array.get a 2 { Option.some _ => false, Option.none => true } in
    let past := match Array.get a 99 { Option.some _ => false, Option.none => true } in
    below && at_len && past

#[test]
def test_array_set_writes : Bool :=
    let a : Array I64 := Array.new 3 0 in
    let b : Array I64 := Array.set a 1 42 in
    match Array.get b 1 {
        Option.some v => I64.beq v 42,
        Option.none => false,
    }

/// `set` is PERSISTENT: the input array must be unchanged. Without
/// this, an implementation that writes through and returns the same
/// object passes everything else.
#[test]
def test_array_set_does_not_mutate_input : Bool :=
    let a : Array I64 := Array.new 3 0 in
    let _b : Array I64 := Array.set a 1 42 in
    match Array.get a 1 {
        Option.some v => I64.beq v 0,
        Option.none => false,
    }

/// An out-of-range `set` returns the array unchanged rather than
/// growing it or corrupting memory.
#[test]
def test_array_set_out_of_range_is_identity : Bool :=
    let a : Array I64 := Array.new 2 1 in
    let b : Array I64 := Array.set a 9 42 in
    I64.beq (Array.length b) 2

#[test]
def test_array_from_list_round_trips : Bool :=
    let xs : List I64 := List.cons 1 (List.cons 2 (List.cons 3 List.empty)) in
    let a : Array I64 := Array.from_list xs in
    let back : List I64 := Array.to_list a in
    I64.beq (Array.length a) 3 && I64.beq (List.length back) 3

#[test]
def test_array_from_list_preserves_order : Bool :=
    let xs : List I64 := List.cons 10 (List.cons 20 (List.cons 30 List.empty)) in
    let a : Array I64 := Array.from_list xs in
    let first := match Array.get a 0 { Option.some v => I64.beq v 10, Option.none => false } in
    let mid := match Array.get a 1 { Option.some v => I64.beq v 20, Option.none => false } in
    let last := match Array.get a 2 { Option.some v => I64.beq v 30, Option.none => false } in
    first && mid && last

#[test]
def test_array_from_empty_list : Bool :=
    let xs : List I64 := List.empty in
    let a : Array I64 := Array.from_list xs in
    I64.beq (Array.length a) 0

/// Elements are untyped at runtime, so the same natives serve any `A`
/// -- this is the polymorphism the whole design rests on, asserted
/// rather than assumed.
#[test]
def test_array_holds_strings : Bool :=
    let a : Array String := Array.new 2 "x" in
    let b : Array String := Array.set a 1 "y" in
    match Array.get b 1 {
        Option.some v => String.beq v "y",
        Option.none => false,
    }

#[test]
def test_array_foldl_sums : Bool :=
    let xs : List I64 := List.cons 1 (List.cons 2 (List.cons 3 List.empty)) in
    let a : Array I64 := Array.from_list xs in
    I64.beq (Array.foldl (fn acc x => acc + x) 0 a) 6

#[test]
def test_array_is_empty : Bool :=
    let e : Array I64 := Array.empty in
    let full : Array I64 := Array.new 1 0 in
    Array.is_empty e && Bool.not (Array.is_empty full)

#[test]
def test_array_get_or_falls_back : Bool :=
    let a : Array I64 := Array.new 1 5 in
    I64.beq (Array.get_or a 0 99) 5 && I64.beq (Array.get_or a 7 99) 99

#[test]
def test_array_push_appends : Bool :=
    let a : Array I64 := Array.new 1 1 in
    let b : Array I64 := Array.push a 2 in
    let grew := I64.beq (Array.length b) 2 in
    let tail := match Array.get b 1 { Option.some v => I64.beq v 2, Option.none => false } in
    grew && tail

#[test]
def test_array_map : Bool :=
    let xs : List I64 := List.cons 1 (List.cons 2 List.empty) in
    let a : Array I64 := Array.from_list xs in
    let b : Array I64 := Array.map (fn x => I64.add x 100) a in
    match Array.get b 1 {
        Option.some v => I64.beq v 102,
        Option.none => false,
    }
