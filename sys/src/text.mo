/// Byte-level helpers for the floor's packed payloads. Pure: no IO, no
/// natives, so it is the one part of `sys` that can be tested without a
/// platform.

/// Split on ASCII space, dropping empty fields (the C packs single spaces,
/// but a stray trailing one must not yield a phantom field).
pub def Text.words (s : String) : List String :=
    Text.words_go s 0 0 (String.length s) List.empty

#[terminating]
def Text.words_go (s : String) (i : I64) (start : I64) (n : I64) (acc : List String) : List String :=
    if I64.lt i n
    then
        if Text.is_space (String.get s i)
        then Text.words_go s (i + 1) (i + 1) n (Text.push s start i acc)
        else Text.words_go s (i + 1) start n acc
    else List.reverse (Text.push s start n acc)

def Text.is_space (b : Option U8) : Bool :=
    match b {
        Option.some c => I64.beq (U8.to_i64 c) 32,
        Option.none => false,
    }

def Text.push (s : String) (start : I64) (stop : I64) (acc : List String) : List String :=
    if I64.lt start stop then List.cons (String.slice s start (stop - start)) acc else acc

/// A decimal `I64`, or `Result.err` naming the offending text.
pub def Text.parse_i64 (s : String) : Result String I64 :=
    let n : I64 := String.length s in
    if I64.lt n 1 then Result.err "empty number"
    else Text.parse_digits s 0 n 1 0

#[terminating]
def Text.parse_digits (s : String) (i : I64) (n : I64) (sign : I64) (acc : I64) : Result String I64 :=
    if I64.beq i n
    then Result.ok (sign * acc)
    else match String.get s i {
        Option.some c =>
            // One read of the byte: `c` is affine.
            let cv : I64 := U8.to_i64 c in
            let d : I64 := cv - 48 in
            // A leading '-' is byte 45; comparing the DIGIT would read a
            // leading '3' as a sign (measured: "33188" parsed as -3188).
            if I64.beq i 0 && I64.beq cv 45 && I64.gt n 1
            then Text.parse_digits s (i + 1) n (0 - 1) 0
            else if I64.lt d 0 || I64.gt d 9
            then Result.err ("not a number: " ++ s)
            else Text.parse_digits s (i + 1) n sign (acc * 10 + d),
        Option.none => Result.err ("not a number: " ++ s),
    }

/// Split on one byte value (NUL for the floor's list-of-names encoding),
/// dropping empty fields so a trailing separator yields no phantom entry.
pub def Text.split_byte (s : String) (sep : U8) : List String :=
    Text.split_byte_go s sep 0 0 (String.length s) List.empty

#[terminating]
def Text.split_byte_go (s : String) (sep : U8) (i : I64) (start : I64) (n : I64) (acc : List String) : List String :=
    if I64.lt i n
    then
        if Text.is_byte (String.get s i) sep
        then Text.split_byte_go s sep (i + 1) (i + 1) n (Text.push s start i acc)
        else Text.split_byte_go s sep (i + 1) start n acc
    else List.reverse (Text.push s start n acc)

def Text.is_byte (b : Option U8) (want : U8) : Bool :=
    match b {
        Option.some c => U8.beq c want,
        Option.none => false,
    }

/// Ascending byte order. Insertion sort: directory listings are small, and
/// this keeps the floor on `init` alone (`List.sort_by` lives in `std`).
/// Sorting HERE rather than in either backend is what makes a compiled
/// binary and the interpreter agree: readdir order is filesystem-dependent.
pub def Text.sort (xs : List String) : List String :=
    Text.sort_insert xs List.empty

#[terminating]
def Text.sort_insert (xs : List String) (acc : List String) : List String :=
    match xs {
        List.empty => acc,
        List.cons x rest => Text.sort_insert rest (Text.insert x acc),
    }

#[terminating]
def Text.insert (x : String) (sorted : List String) : List String :=
    match sorted {
        List.empty => List.cons x List.empty,
        List.cons y rest =>
            if String.lt x y
            then List.cons x (List.cons y rest)
            else List.cons y (Text.insert x rest),
    }
