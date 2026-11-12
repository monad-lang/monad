/// The Thompson NFA: HIR compiled to byte-level states in a frozen table.
///
/// Compilation is continuation-passing: `compile h next` builds `h`'s
/// states so that finishing `h` continues at state `next`, and returns
/// `h`'s entry state. A loop needs its own id before its body exists, so
/// ids are reserved first and defined later; definitions accumulate as
/// `(id, state)` pairs and are sorted into the table once at the end.
///
/// A class compiles through a byte trie of its UTF-8 sequences, so each
/// byte position of a class is ONE `sparse` state: a Pike VM thread
/// entering `\w` explores one state, not one per sequence.
use lib::hir {RxHir, RxLook}
use lib::utf8 {class_utf8_sequences}
use lib::table {RxTable, table_of_list}
use std::list {List.sort_by}

/// One byte-range transition.
pub struct RxTrans {
    lo : I64,
    hi : I64,
    next : I64,
}

pub type RxState {
    byte_range (lo : I64) (hi : I64) (next : I64),
    sparse (trans : List RxTrans),
    /// Alternatives in priority order.
    union (alts : List I64),
    capture (slot : I64) (next : I64),
    look (kind : RxLook) (next : I64),
    goto (next : I64),
    accept,
    dead,
}

/// A compiled program.
pub struct RxProg {
    states : RxTable RxState,
    start : I64,
    len : I64,
    /// 2 * (capture groups + 1).
    slots : I64,
    /// Whether any state is a Unicode word-boundary look.
    needs_word : Bool,
}

struct RxB {
    next_id : I64,
    defs : List (Pair I64 RxState),
    needs_word : Bool,
}

def add (b : RxB) (st : RxState) : Pair I64 RxB :=
    Pair.pair b.next_id { b with next_id := b.next_id + 1, defs := List.cons (Pair.pair b.next_id st) b.defs }

def reserve (b : RxB) : Pair I64 RxB :=
    Pair.pair b.next_id { b with next_id := b.next_id + 1 }

def define (b : RxB) (id : I64) (st : RxState) : RxB :=
    { b with defs := List.cons (Pair.pair id st) b.defs }

// ─── Size estimate (G2) ───

/// An upper estimate of the state count, saturating just past `limit` so
/// a pattern like `(a{100}){100}{100}` is refused before it is built.
#[terminating]
pub def estimate (h : RxHir) (limit : I64) : I64 :=
    match h {
        RxHir.empty => 0,
        RxHir.cset ranges bytes => if bytes then 1 else 4 * List.length ranges + 1,
        RxHir.look _ => 1,
        RxHir.capture _ sub => cap (estimate sub limit + 2) limit,
        RxHir.concat items => sum_estimates items limit 0,
        RxHir.alternation items => cap (sum_estimates items limit 0 + 1) limit,
        RxHir.repetition min max _ sub =>
            let copies : I64 := match max { Option.some m => m, Option.none => min + 1 } in
            cap (mul_cap (estimate sub limit + 1) (if I64.lt copies 1 then 1 else copies) limit) limit,
    }

#[terminating]
def sum_estimates (items : List RxHir) (limit : I64) (acc : I64) : I64 :=
    match items {
        List.empty => acc,
        List.cons h rest => sum_estimates rest limit (cap (acc + estimate h limit) limit),
    }

def cap (n : I64) (limit : I64) : I64 := if I64.lt limit n then limit + 1 else n

def mul_cap (a : I64) (b : I64) (limit : I64) : I64 :=
    if I64.lt 0 a && I64.lt (I64.div (limit + 1) a) b then limit + 1 else a * b

// ─── Compilation ───

/// The whole program: capture slot 0, the pattern, slot 1, accept.
pub def compile_prog (h : RxHir) (captures : I64) : RxProg :=
    let b0 : RxB := { next_id := 0, defs := List.empty, needs_word := false } in
    match add b0 RxState.accept {
        Pair.pair acc b1 =>
            match add b1 (RxState.capture 1 acc) {
                Pair.pair end_cap b2 =>
                    match compile h end_cap b2 {
                        Pair.pair body b3 =>
                            match add b3 (RxState.capture 0 body) {
                                Pair.pair start b4 => freeze b4 start captures,
                            },
                    },
            },
    }

def freeze (b : RxB) (start : I64) (captures : I64) : RxProg :=
    let sorted : List (Pair I64 RxState) := List.sort_by def_lt b.defs in
    {
        states := table_of_list (List.map (fn (d : Pair I64 RxState) => d.second) sorted),
        start := start,
        len := b.next_id,
        slots := 2 * (captures + 1),
        needs_word := b.needs_word,
    }

def def_lt (a : Pair I64 RxState) (b : Pair I64 RxState) : Bool := I64.lt a.first b.first

#[terminating]
def compile (h : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match h {
        RxHir.empty => Pair.pair next b,
        RxHir.cset ranges bytes => if bytes then compile_bytes ranges next b else compile_scalars ranges next b,
        RxHir.look kind => add (note_look kind b) (RxState.look kind next),
        RxHir.capture idx sub => compile_capture idx sub next b,
        RxHir.concat items => compile_concat (List.reverse items) next b,
        RxHir.alternation items => compile_alts items next b List.empty,
        RxHir.repetition min max greedy sub => compile_rep min max greedy sub next b,
    }

def note_look (kind : RxLook) (b : RxB) : RxB :=
    match kind {
        RxLook.word_unicode => { b with needs_word := true },
        RxLook.not_word_unicode => { b with needs_word := true },
        _ => b,
    }

#[terminating]
def compile_capture (idx : I64) (sub : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match add b (RxState.capture (2 * idx + 1) next) {
        Pair.pair close b2 =>
            match compile sub close b2 {
                Pair.pair body b3 => add b3 (RxState.capture (2 * idx) body),
            },
    }

/// `items` reversed: the last item continues at `next`.
#[terminating]
def compile_concat (items : List RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match items {
        List.empty => Pair.pair next b,
        List.cons h rest =>
            match compile h next b {
                Pair.pair entry b2 => compile_concat rest entry b2,
            },
    }

#[terminating]
def compile_alts (items : List RxHir) (next : I64) (b : RxB) (entries : List I64) : Pair I64 RxB :=
    match items {
        List.empty => add b (RxState.union (List.reverse entries)),
        List.cons h rest =>
            match compile h next b {
                Pair.pair entry b2 => compile_alts rest next b2 (List.cons entry entries),
            },
    }

def choice (greedy : Bool) (body : I64) (skip : I64) : RxState :=
    if greedy then RxState.union [body, skip] else RxState.union [skip, body]

/// `x{min,max}`: `min` copies, then either a loop (`max` unbounded) or
/// `max - min` nested optionals, each of which skips to `next`.
#[terminating]
def compile_rep (min : I64) (max : Option I64) (greedy : Bool) (sub : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match max {
        Option.none =>
            if I64.beq min 0 then compile_star greedy sub next b
            else
                match compile_plus greedy sub next b {
                    Pair.pair entry b2 => compile_copies (min - 1) sub entry b2,
                },
        Option.some m =>
            match compile_optionals (m - min) greedy sub next next b {
                Pair.pair entry b2 => compile_copies min sub entry b2,
            },
    }

#[terminating]
def compile_star (greedy : Bool) (sub : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match reserve b {
        Pair.pair loop b2 =>
            match compile sub loop b2 {
                Pair.pair body b3 => Pair.pair loop (define b3 loop (choice greedy body next)),
            },
    }

/// `x+`: the body, then a choice back to it or on to `next`.
#[terminating]
def compile_plus (greedy : Bool) (sub : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    match reserve b {
        Pair.pair loop b2 =>
            match compile sub loop b2 {
                Pair.pair body b3 => Pair.pair body (define b3 loop (choice greedy body next)),
            },
    }

#[terminating]
def compile_copies (n : I64) (sub : RxHir) (next : I64) (b : RxB) : Pair I64 RxB :=
    if I64.lt 0 n then
        match compile sub next b {
            Pair.pair entry b2 => compile_copies (n - 1) sub entry b2,
        }
    else Pair.pair next b

/// `k` nested optionals: `(x(x(x)?)?)?`, every skip going to `exit`.
#[terminating]
def compile_optionals (k : I64) (greedy : Bool) (sub : RxHir) (cur : I64) (exit : I64) (b : RxB) : Pair I64 RxB :=
    if I64.lt 0 k then
        match compile sub cur b {
            Pair.pair body b2 =>
                match add b2 (choice greedy body exit) {
                    Pair.pair u b3 => compile_optionals (k - 1) greedy sub u exit b3,
                },
        }
    else Pair.pair cur b

// ─── Classes ───

def compile_bytes (ranges : List (Pair I64 I64)) (next : I64) (b : RxB) : Pair I64 RxB :=
    match ranges {
        List.empty => add b RxState.dead,
        List.cons r rest =>
            if List.is_empty rest then add b (RxState.byte_range r.first r.second next)
            else add b (RxState.sparse (List.map (fn (x : Pair I64 I64) => trans x.first x.second next) ranges)),
    }

def trans (lo : I64) (hi : I64) (next : I64) : RxTrans :=
    let t : RxTrans := { lo := lo, hi := hi, next := next } in t

/// A byte trie: each edge is one byte range. The sequences of a class are
/// prefix-free, so a leaf is exactly the end of a sequence.
type RxTrie {
    node (edges : List RxEdge),
}

struct RxEdge {
    lo : I64,
    hi : I64,
    child : RxTrie,
}

def compile_scalars (ranges : List (Pair I64 I64)) (next : I64) (b : RxB) : Pair I64 RxB :=
    match ranges {
        List.empty => add b RxState.dead,
        _ => compile_trie (build_trie (class_utf8_sequences ranges)) next b,
    }

def build_trie (seqs : List (List (Pair I64 I64))) : RxTrie :=
    insert_all seqs (RxTrie.node List.empty)

#[terminating]
def insert_all (seqs : List (List (Pair I64 I64))) (t : RxTrie) : RxTrie :=
    match seqs {
        List.empty => t,
        List.cons s rest => insert_all rest (insert_seq s t),
    }

#[terminating]
def insert_seq (seq : List (Pair I64 I64)) (t : RxTrie) : RxTrie :=
    match seq {
        List.empty => t,
        List.cons r rest =>
            match t {
                RxTrie.node edges => RxTrie.node (insert_edge r.first r.second rest edges),
            },
    }

/// Sequences arrive ascending, so a shared prefix is always the LAST edge;
/// edges are kept newest-first and reversed when compiled.
#[terminating]
def insert_edge (lo : I64) (hi : I64) (rest : List (Pair I64 I64)) (edges : List RxEdge) : List RxEdge :=
    match edges {
        List.cons e older =>
            if I64.beq e.lo lo && I64.beq e.hi hi then
                List.cons (edge lo hi (insert_seq rest e.child)) older
            else List.cons (edge lo hi (insert_seq rest (RxTrie.node List.empty))) (List.cons e older),
        List.empty => List.cons (edge lo hi (insert_seq rest (RxTrie.node List.empty))) List.empty,
    }

def edge (lo : I64) (hi : I64) (child : RxTrie) : RxEdge :=
    let e : RxEdge := { lo := lo, hi := hi, child := child } in e

#[terminating]
def compile_trie (t : RxTrie) (next : I64) (b : RxB) : Pair I64 RxB :=
    match t {
        RxTrie.node edges =>
            if List.is_empty edges then Pair.pair next b
            else compile_edges (List.reverse edges) next b List.empty,
    }

#[terminating]
def compile_edges (edges : List RxEdge) (next : I64) (b : RxB) (acc : List RxTrans) : Pair I64 RxB :=
    match edges {
        List.empty =>
            match acc {
                List.cons t rest =>
                    if List.is_empty rest then add b (RxState.byte_range t.lo t.hi t.next)
                    else add b (RxState.sparse (List.reverse acc)),
                List.empty => add b RxState.dead,
            },
        List.cons e rest =>
            match compile_trie e.child next b {
                Pair.pair target b2 => compile_edges rest next b2 (List.cons (trans e.lo e.hi target) acc),
            },
    }
