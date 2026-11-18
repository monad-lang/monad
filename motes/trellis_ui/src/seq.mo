// Stack-safe list walks for graph-sized lists.
//
// The browser's call stack is far smaller than a native one, and a plain
// recursive walk spends one frame per element: the type checker's graph has
// 70k lines and 63k edges, and `List.map`/`List.filter` (not tail calls) or
// a walk the self-tail-call rewrite does not catch overflows it. Every walk
// here folds in CHUNKS: an inner recursion over at most `chunk` elements,
// an outer one over the chunks, so the depth is about `n / chunk + chunk`
// whatever the length.
//
// Use these for anything that scales with the graph (declarations, edges,
// lines of the graph file); small lists keep the ordinary helpers.

def chunk : I64 := 512

/// A chunk's result: the accumulator so far, then the elements left.
/// A `type`, not a `struct`: parameterized structs do not parse (and a
/// generic `Pair B (List A)` pattern is mis-typed by the checker).
type SeqChunk (A : Type) (B : Type) {
    seq_chunk (B) (List A),
}

/// Fold up to `n` elements; the rest of the list comes back with the result.
#[terminating]
def fold_some {A : Type} {B : Type} (f : B -> A -> B) (xs : List A) (n : I64) (acc : B) : SeqChunk A B :=
    match xs {
        List.empty => SeqChunk.seq_chunk acc List.empty,
        List.cons x more => if n <= 0 then SeqChunk.seq_chunk acc xs else fold_some f more (n - 1) (f acc x),
    }

def part_acc {A : Type} {B : Type} (p : SeqChunk A B) : B := match p { SeqChunk.seq_chunk a _ => a }

def part_rest {A : Type} {B : Type} (p : SeqChunk A B) : List A := match p { SeqChunk.seq_chunk _ r => r }

/// A left fold whose stack depth does not grow with the list.
#[terminating]
pub def Seq.fold {A : Type} {B : Type} (f : B -> A -> B) (acc : B) (xs : List A) : B :=
    let part : SeqChunk A B := fold_some f xs chunk acc in
    let rest : List A := part_rest part in
    if List.is_empty rest then part_acc part else Seq.fold f (part_acc part) rest

pub def Seq.reverse {A : Type} (xs : List A) : List A :=
    Seq.fold (fn (acc : List A) (x : A) => List.cons x acc) List.empty xs

pub def Seq.map {A : Type} {B : Type} (f : A -> B) (xs : List A) : List B :=
    Seq.reverse (Seq.fold (fn (acc : List B) (x : A) => List.cons (f x) acc) List.empty xs)

pub def Seq.filter {A : Type} (keep : A -> Bool) (xs : List A) : List A :=
    Seq.reverse (Seq.fold (fn (acc : List A) (x : A) => if keep x then List.cons x acc else acc) List.empty xs)

pub def Seq.length {A : Type} (xs : List A) : I64 := Seq.fold (fn (n : I64) (_x : A) => n + 1) 0 xs

pub def Seq.any {A : Type} (p : A -> Bool) (xs : List A) : Bool :=
    Seq.fold (fn (found : Bool) (x : A) => found || p x) false xs

pub def Seq.find {A : Type} (p : A -> Bool) (xs : List A) : Option A :=
    Seq.fold (fn (found : Option A) (x : A) => match found { Option.some _ => found,
        Option.none => if p x then Option.some x else Option.none }) Option.none xs

/// `a` then `b`.
pub def Seq.append {A : Type} (a : List A) (b : List A) : List A :=
    Seq.fold (fn (acc : List A) (x : A) => List.cons x acc) b (Seq.reverse a)

// ─── Lines ───

struct LineState {
    rest : String,
    lines : List String,
    done : Bool,
}

def take_line (st : LineState) (_i : I64) : LineState :=
    if st.done then st
    else
        match String.byte_index_of st.rest "\n" {
            Option.none => { rest := "", lines := List.cons st.rest st.lines, done := true },
            Option.some i =>
                { rest := String.drop (i + 1) st.rest, lines := List.cons (String.slice st.rest 0 i) st.lines,
                    done := false },
        }

#[terminating]
def lines_loop (st : LineState) : LineState :=
    let next : LineState := fold_ticks st chunk in
    if next.done then next else lines_loop next

#[terminating]
def fold_ticks (st : LineState) (n : I64) : LineState :=
    if n <= 0 || st.done then st else fold_ticks (take_line st n) (n - 1)

/// `text` split at `\n`, stack-safely (`String.split` recurses per piece).
pub def Seq.lines (text : String) : List String :=
    let start : LineState := { rest := text, lines := List.empty, done := false } in
    let finished : LineState := lines_loop start in
    Seq.reverse finished.lines
