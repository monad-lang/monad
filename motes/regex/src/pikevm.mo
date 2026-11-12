/// The Pike VM: the reference engine, and the one that resolves captures.
///
/// Threads are `(pc, slots)` in priority order. Each step consumes one
/// haystack byte; the epsilon closure runs with an explicit stack (never
/// O(m)-deep recursion) and a per-step bitset of visited states, so a step
/// touches each state at most once. That bounds a search at O(m·n): there
/// is no input that makes it backtrack.
///
/// Leftmost-first: a new thread starts at each position (at the lowest
/// priority) until some thread matches; a match cuts every thread of lower
/// priority, and the search ends when no higher-priority thread is left.
///
/// The haystack is a `List U8` cursor, never `String.get` (a `strlen` per
/// non-zero index compiled).
use lib::hir {RxLook}
use lib::nfa {RxProg, RxState, RxTrans}
use lib::table {RxTable, table_get, table_len}
use std::array {Array}
use std::list {}

/// Where a search stands: the bytes from `pos` on, the byte before `pos`
/// (-1 at the start), and whether the scalar before `pos` is a word
/// character (tracked only when the program has a Unicode `\b`).
pub struct RxCursor {
    rest : List U8,
    pos : I64,
    prev : I64,
    prev_word : Bool,
}

/// Word ranges as a table, for `\b`'s per-position lookup.
pub struct RxWords {
    ranges : RxTable (Pair I64 I64),
}

struct RxThread {
    pc : I64,
    slots : Array I64,
}

/// What a search returns: the winning thread's slots, and how many
/// thread operations it took (the G1 tests' deterministic clock).
pub struct RxResult {
    slots : Option (Array I64),
    steps : I64,
}

// ─── Cursor ───

pub def cursor_start (bytes : List U8) : RxCursor :=
    let c : RxCursor := { rest := bytes, pos := 0, prev := 0 - 1, prev_word := false } in c

def head_byte (xs : List U8) : I64 :=
    match xs {
        List.cons b _ => U8.to_i64 b,
        List.empty => 0 - 1,
    }

#[terminating]
def byte_at (xs : List U8) (n : I64) : I64 :=
    match xs {
        List.empty => 0 - 1,
        List.cons b rest => if I64.beq n 0 then U8.to_i64 b else byte_at rest (n - 1),
    }

def is_cont (b : I64) : Bool := I64.lt 127 b && I64.lt b 192

/// The scalar starting at the head of `xs`, or -1 if it is not valid UTF-8.
pub def decode_head (xs : List U8) : I64 :=
    let b0 : I64 := head_byte xs in
    if I64.lt b0 0 then 0 - 1
    else if I64.lt b0 128 then b0
    else if I64.lt b0 194 then 0 - 1
    else if I64.lt b0 224 then dec2 (I64.and b0 31) (byte_at xs 1)
    else if I64.lt b0 240 then dec3 (I64.and b0 15) (byte_at xs 1) (byte_at xs 2)
    else if I64.lt b0 245 then dec4 (I64.and b0 7) (byte_at xs 1) (byte_at xs 2) (byte_at xs 3)
    else 0 - 1

def dec2 (h : I64) (c1 : I64) : I64 :=
    if is_cont c1 then I64.or (I64.shl h 6) (I64.and c1 63) else 0 - 1

def dec3 (h : I64) (c1 : I64) (c2 : I64) : I64 :=
    if is_cont c1 && is_cont c2 then
        I64.or (I64.shl h 12) (I64.or (I64.shl (I64.and c1 63) 6) (I64.and c2 63))
    else 0 - 1

def dec4 (h : I64) (c1 : I64) (c2 : I64) (c3 : I64) : I64 :=
    if is_cont c1 && is_cont c2 && is_cont c3 then
        I64.or (I64.shl h 18) (I64.or (I64.shl (I64.and c1 63) 12) (I64.or (I64.shl (I64.and c2 63) 6) (I64.and c3 63)))
    else 0 - 1

/// Binary search over the word ranges.
pub def is_word_scalar (w : RxWords) (c : I64) : Bool :=
    if I64.lt c 0 then false else word_search w.ranges c 0 (table_len w.ranges - 1)

#[terminating]
def word_search (t : RxTable (Pair I64 I64)) (c : I64) (lo : I64) (hi : I64) : Bool :=
    if I64.lt hi lo then false
    else
        let mid : I64 := I64.div (lo + hi) 2 in
        let r : Pair I64 I64 := table_get t mid (Pair.pair 0 (0 - 1)) in
        if I64.lt c r.first then word_search t c lo (mid - 1)
        else if I64.lt r.second c then word_search t c (mid + 1) hi
        else true

/// One byte on. The scalar before the new position is the one whose
/// lead byte was passed most recently.
pub def cursor_advance (needs_word : Bool) (w : RxWords) (c : RxCursor) : RxCursor :=
    match c.rest {
        List.empty => c,
        List.cons b more =>
            let byte : I64 := U8.to_i64 b in
            let word : Bool :=
                if needs_word && Bool.not (is_cont byte) then is_word_scalar w (decode_head c.rest)
                else c.prev_word in
            let n : RxCursor := { rest := more, pos := c.pos + 1, prev := byte, prev_word := word } in n,
    }

#[terminating]
pub def cursor_skip (needs_word : Bool) (w : RxWords) (c : RxCursor) (n : I64) : RxCursor :=
    if I64.lt 0 n && Bool.not (List.is_empty c.rest) then cursor_skip needs_word w (cursor_advance needs_word w c) (n - 1)
    else c

// ─── Assertions ───

def ascii_word_byte (b : I64) : Bool :=
    (I64.lt 47 b && I64.lt b 58) || (I64.lt 64 b && I64.lt b 91) || I64.beq b 95 || (I64.lt 96 b && I64.lt b 123)

def bool_ne (a : Bool) (b : Bool) : Bool := if a then Bool.not b else b

def look_holds (kind : RxLook) (w : RxWords) (c : RxCursor) : Bool :=
    match kind {
        RxLook.start_text => I64.beq c.pos 0,
        RxLook.end_text => List.is_empty c.rest,
        RxLook.start_line => I64.beq c.pos 0 || I64.beq c.prev 10,
        RxLook.end_line => List.is_empty c.rest || I64.beq (head_byte c.rest) 10,
        RxLook.word_ascii => bool_ne (ascii_word_byte c.prev) (ascii_word_byte (head_byte c.rest)),
        RxLook.not_word_ascii => Bool.not (bool_ne (ascii_word_byte c.prev) (ascii_word_byte (head_byte c.rest))),
        RxLook.word_unicode => bool_ne c.prev_word (is_word_scalar w (decode_head c.rest)),
        RxLook.not_word_unicode => Bool.not (bool_ne c.prev_word (is_word_scalar w (decode_head c.rest))),
    }

// ─── Visited set ───

def bit_test (words : Array I64) (pc : I64) : Bool :=
    Bool.not (I64.beq (I64.and (Array.get_or words (I64.shr pc 6) 0) (I64.shl 1 (I64.and pc 63))) 0)

def bit_set (words : Array I64) (pc : I64) : Array I64 :=
    let wi : I64 := I64.shr pc 6 in
    Array.set words wi (I64.or (Array.get_or words wi 0) (I64.shl 1 (I64.and pc 63)))

def fresh_set (prog : RxProg) : Array I64 := Array.new (I64.div (prog.len + 63) 64) 0

// ─── Closure ───

/// The closure's output: the visited set, the threads found (newest
/// first), and the work done.
struct RxClosure {
    seen : Array I64,
    out : List RxThread,
    steps : I64,
}

/// Explore from the stack's top, depth first: a `union` pushes its
/// alternatives so the first is explored first, which keeps the output in
/// priority order. Only byte-consuming states and `accept` are output.
#[terminating]
def closure (prog : RxProg) (w : RxWords) (c : RxCursor) (nslots : I64) (stack : List RxThread) (acc : RxClosure) : RxClosure :=
    match stack {
        List.empty => acc,
        List.cons t rest =>
            if bit_test acc.seen t.pc then closure prog w c nslots rest acc
            else
                let acc2 : RxClosure := { acc with seen := bit_set acc.seen t.pc, steps := acc.steps + 1 } in
                closure_state prog w c nslots t (table_get prog.states t.pc RxState.dead) rest acc2
    }

#[terminating]
def closure_state (prog : RxProg) (w : RxWords) (c : RxCursor) (nslots : I64) (t : RxThread) (st : RxState) (rest : List RxThread) (acc : RxClosure) : RxClosure :=
    match st {
        RxState.goto next => closure prog w c nslots (List.cons (thread next t.slots) rest) acc,
        RxState.union alts => closure prog w c nslots (List.append (List.map (fn (pc : I64) => thread pc t.slots) alts) rest) acc,
        RxState.capture slot next =>
            let slots : Array I64 := if I64.lt slot nslots then Array.set t.slots slot c.pos else t.slots in
            closure prog w c nslots (List.cons (thread next slots) rest) acc,
        RxState.look kind next =>
            if look_holds kind w c then closure prog w c nslots (List.cons (thread next t.slots) rest) acc
            else closure prog w c nslots rest acc,
        RxState.dead => closure prog w c nslots rest acc,
        _ => closure prog w c nslots rest { acc with out := List.cons t acc.out },
    }

def thread (pc : I64) (slots : Array I64) : RxThread :=
    let t : RxThread := { pc := pc, slots := slots } in t

// ─── Search ───

/// Search from `c` for the leftmost-first match. `nslots` is how many
/// capture slots to record (2 for a plain span). `earliest` stops at the
/// first accept, which settles WHETHER there is a match but not its span.
pub def search (prog : RxProg) (w : RxWords) (c : RxCursor) (nslots : I64) (earliest : Bool) : RxResult :=
    let acc0 : RxClosure := { seen := fresh_set prog, out := List.empty, steps := 0 } in
    run prog w nslots earliest c acc0 Option.none

/// One position: seed a thread (while nothing has matched), then step
/// every thread over the byte at `c`. `acc` holds the threads already
/// waiting at `c` (newest first) and their visited set.
#[terminating]
def run (prog : RxProg) (w : RxWords) (nslots : I64) (earliest : Bool) (c : RxCursor) (acc : RxClosure) (matched : Option (Array I64)) : RxResult :=
    let seeded : RxClosure :=
        match matched {
            Option.none => closure prog w c nslots [thread prog.start (Array.new nslots (0 - 1))] acc,
            Option.some _ => acc,
        } in
    let clist : List RxThread := List.reverse seeded.out in
    let next_c : RxCursor := cursor_advance prog.needs_word w c in
    let fresh : RxClosure := { seen := fresh_set prog, out := List.empty, steps := seeded.steps } in
    let stepped : RxStepped := step prog w nslots (head_byte c.rest) next_c clist fresh matched in
    if List.is_empty c.rest || (is_some stepped.matched && (earliest || List.is_empty stepped.next.out)) then
        let r : RxResult := { slots := stepped.matched, steps := stepped.next.steps } in r
    else run prog w nslots earliest next_c stepped.next stepped.matched

def is_some (o : Option (Array I64)) : Bool :=
    match o {
        Option.some _ => true,
        Option.none => false,
    }

struct RxStepped {
    next : RxClosure,
    matched : Option (Array I64),
}

/// Threads in priority order over byte `b` (-1 at the end). An `accept`
/// records the match and drops every lower-priority thread.
#[terminating]
def step (prog : RxProg) (w : RxWords) (nslots : I64) (b : I64) (next_c : RxCursor) (clist : List RxThread) (acc : RxClosure) (matched : Option (Array I64)) : RxStepped :=
    match clist {
        List.empty =>
            let s : RxStepped := { next := acc, matched := matched } in s,
        List.cons t rest =>
            let acc1 : RxClosure := { acc with steps := acc.steps + 1 } in
            match table_get prog.states t.pc RxState.dead {
                RxState.accept =>
                    let s : RxStepped := { next := acc1, matched := Option.some t.slots } in s,
                RxState.byte_range lo hi next =>
                    if I64.lt b lo || I64.lt hi b then step prog w nslots b next_c rest acc1 matched
                    else step prog w nslots b next_c rest (closure prog w next_c nslots [thread next t.slots] acc1) matched,
                RxState.sparse ts =>
                    match find_trans ts b {
                        Option.some next =>
                            step prog w nslots b next_c rest (closure prog w next_c nslots [thread next t.slots] acc1) matched,
                        Option.none => step prog w nslots b next_c rest acc1 matched,
                    },
                _ => step prog w nslots b next_c rest acc1 matched,
            },
    }

#[terminating]
def find_trans (ts : List RxTrans) (b : I64) : Option I64 :=
    match ts {
        List.empty => Option.none,
        List.cons t rest =>
            if I64.lt b t.lo then Option.none
            else if I64.lt t.hi b then find_trans rest b
            else Option.some t.next,
    }
