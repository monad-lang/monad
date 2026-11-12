/// A read-only table with O(1) reads, built in linear time.
///
/// `Array.from_list` fills with copying `Array.set`s, so it is quadratic
/// (the Phase 0 spike measured 5.4 µs per element at 4096). A table is
/// chunks of at most 64 elements: each chunk costs at most 64^2/2 copies
/// (32 per element), and the outer array holds n/64 chunks.
use std::array {Array}
use std::list {}

pub type RxTable A {
    mk (chunks : Array (Array A)) (len : I64),
}

def chunk_size : I64 := 64

pub def table_of_list {A : Type} (xs : List A) : RxTable A :=
    RxTable.mk (Array.from_list (List.map Array.from_list (split_chunks xs List.empty 0 List.empty))) (List.length xs)

#[terminating]
def split_chunks {A : Type} (xs : List A) (cur : List A) (k : I64) (acc : List (List A)) : List (List A) :=
    match xs {
        List.empty => List.reverse (flush cur acc),
        List.cons x more =>
            if I64.beq k chunk_size then split_chunks more (List.cons x List.empty) 1 (flush cur acc)
            else split_chunks more (List.cons x cur) (k + 1) acc,
    }

def flush {A : Type} (cur : List A) (acc : List (List A)) : List (List A) :=
    if List.is_empty cur then acc else List.cons (List.reverse cur) acc

/// The element at `i`, or `fallback` out of range.
pub def table_get {A : Type} (t : RxTable A) (i : I64) (fallback : A) : A :=
    match t {
        RxTable.mk chunks _ => Array.get_or (Array.get_or chunks (I64.shr i 6) Array.empty) (I64.and i 63) fallback,
    }

/// `t` with element `i` replaced: one chunk and the outer array are
/// copied. Out of range, `t` is returned unchanged.
pub def table_set {A : Type} (t : RxTable A) (i : I64) (v : A) : RxTable A :=
    match t {
        RxTable.mk chunks len =>
            if I64.lt i 0 || I64.lt (len - 1) i then RxTable.mk chunks len
            else
                let ci : I64 := I64.shr i 6 in
                RxTable.mk (Array.set chunks ci (Array.set (Array.get_or chunks ci Array.empty) (I64.and i 63) v)) len,
    }

/// `t` with `v` appended.
pub def table_push {A : Type} (t : RxTable A) (v : A) : RxTable A :=
    match t {
        RxTable.mk chunks len =>
            let ci : I64 := I64.shr len 6 in
            if I64.beq (I64.and len 63) 0 then RxTable.mk (Array.push chunks (Array.new 1 v)) (len + 1)
            else RxTable.mk (Array.set chunks ci (Array.push (Array.get_or chunks ci Array.empty) v)) (len + 1),
    }

pub def table_len {A : Type} (t : RxTable A) : I64 :=
    match t {
        RxTable.mk _ len => len,
    }
