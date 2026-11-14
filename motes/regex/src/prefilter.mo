/// Literal scanning over a `List U8` cursor: the whole search for a
/// literal pattern, and the skip loop the lazy DFA uses while it sits in
/// its start state.
use lib::literal {mask_has}
use std::array {Array}
use std::list {}

/// Where a scan stopped.
pub struct RxSkip {
    rest : List U8,
    pos : I64,
}

/// Skip bytes outside `mask`: stops at the first byte in it, or at the
/// end. The measure is the bytes left.
#[terminating]
pub def skip_to_mask (mask : Array I64) (rest : List U8) (pos : I64) : RxSkip :=
    match rest {
        List.empty =>
            let s : RxSkip := { rest := rest, pos := pos } in s,
        List.cons b more =>
            if mask_has mask (U8.to_i64 b) then
                let s : RxSkip := { rest := List.cons b more, pos := pos } in s
            else skip_to_mask mask more (I64.add pos 1),
    }

/// The leftmost-first literal match from `pos` on: at each position the
/// literals are tried in priority order. O(n * total literal length).
#[terminating]
pub def scan_literals (lits : List (List I64)) (mask : Array I64) (rest : List U8) (pos : I64) : Option (Pair I64 I64) :=
    let s : RxSkip := skip_to_mask mask rest pos in
    match s.rest {
        List.empty => Option.none,
        List.cons _ more =>
            match first_at lits s.rest {
                Option.some n => Option.some (Pair.pair s.pos (s.pos + n)),
                Option.none => scan_literals lits mask more (I64.add s.pos 1),
            },
    }

/// The length of the first literal `xs` starts with.
#[terminating]
def first_at (lits : List (List I64)) (xs : List U8) : Option I64 :=
    match lits {
        List.empty => Option.none,
        List.cons l rest => if starts_with l xs then Option.some (List.length l) else first_at rest xs,
    }

#[terminating]
def starts_with (lit : List I64) (xs : List U8) : Bool :=
    match lit {
        List.empty => true,
        List.cons b more =>
            match xs {
                List.cons x rest => I64.beq b (U8.to_i64 x) && starts_with more rest,
                List.empty => false,
            },
    }
