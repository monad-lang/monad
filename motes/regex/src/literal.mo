/// What the meta strategy learns from the HIR before searching: whether
/// the pattern is a plain literal (or a small set of them), which bytes a
/// match can start with, how long a match can be, and whether the lazy
/// DFA can run it at all.
use lib::hir {RxHir, RxLook}
use lib::utf8 {encode_scalar}
use std::array {Array}
use std::list {}

/// The most alternatives a literal set may have; past it the DFA wins.
def max_literals : I64 := 16

// ─── Literals ───

/// The pattern's alternatives as UTF-8 bytes, in priority order, when it
/// is nothing but literals: no captures, assertions, classes or
/// repetition, and no empty alternative.
pub def hir_literals (h : RxHir) : Option (List (List I64)) :=
    match h {
        RxHir.alternation items =>
            if I64.lt max_literals (List.length items) then Option.none else all_literals items List.empty,
        _ =>
            match one_literal h {
                Option.some bs => Option.some [bs],
                Option.none => Option.none,
            },
    }

#[terminating]
def all_literals (items : List RxHir) (acc : List (List I64)) : Option (List (List I64)) :=
    match items {
        List.empty => Option.some (List.reverse acc),
        List.cons h rest =>
            match one_literal h {
                Option.some bs => all_literals rest (List.cons bs acc),
                Option.none => Option.none,
            },
    }

def one_literal (h : RxHir) : Option (List I64) :=
    match literal_bytes h List.empty {
        Option.some rev => if List.is_empty rev then Option.none else Option.some (List.reverse rev),
        Option.none => Option.none,
    }

/// `h`'s bytes prepended to `acc` (newest first).
#[terminating]
def literal_bytes (h : RxHir) (acc : List I64) : Option (List I64) :=
    match h {
        RxHir.empty => Option.some acc,
        RxHir.cset ranges bytes =>
            match ranges {
                List.cons r rest =>
                    if List.is_empty rest && I64.beq r.first r.second then
                        Option.some (if bytes then List.cons r.first acc else List.append (List.reverse (encode_scalar r.first)) acc)
                    else Option.none,
                List.empty => Option.none,
            },
        RxHir.concat items => concat_bytes items acc,
        _ => Option.none,
    }

#[terminating]
def concat_bytes (items : List RxHir) (acc : List I64) : Option (List I64) :=
    match items {
        List.empty => Option.some acc,
        List.cons h rest =>
            match literal_bytes h acc {
                Option.some acc2 => concat_bytes rest acc2,
                Option.none => Option.none,
            },
    }

// ─── Byte masks ───

/// A 256-bit byte set in four words.
pub def mask_empty : Array I64 := Array.new 4 0

pub def mask_has (m : Array I64) (b : I64) : Bool :=
    Bool.not (I64.beq (I64.and (Array.get_or m (I64.shr b 6) 0) (I64.shl 1 (I64.and b 63))) 0)

def mask_add (m : Array I64) (b : I64) : Array I64 :=
    let wi : I64 := I64.shr b 6 in
    Array.set m wi (I64.or (Array.get_or m wi 0) (I64.shl 1 (I64.and b 63)))

/// Bytes `lo..=hi`, one bit at a time: compile time only.
#[terminating]
pub def mask_add_range (m : Array I64) (lo : I64) (hi : I64) : Array I64 :=
    if I64.lt hi lo then m else mask_add_range (mask_add m lo) (lo + 1) hi

/// Whether every byte is in the set, which makes it useless as a filter.
pub def mask_full (m : Array I64) : Bool :=
    I64.beq (Array.get_or m 0 0) (0 - 1) && I64.beq (Array.get_or m 1 0) (0 - 1)
        && I64.beq (Array.get_or m 2 0) (0 - 1) && I64.beq (Array.get_or m 3 0) (0 - 1)

/// The first bytes of a literal set.
pub def literals_mask (lits : List (List I64)) : Array I64 := lits_mask lits mask_empty

#[terminating]
def lits_mask (lits : List (List I64)) (m : Array I64) : Array I64 :=
    match lits {
        List.empty => m,
        List.cons l rest =>
            match l {
                List.cons b _ => lits_mask rest (mask_add m b),
                List.empty => lits_mask rest m,
            },
    }

// ─── First bytes ───

/// Every byte a match can start with, or none when the pattern can match
/// the empty string (then any position may match, and nothing filters).
pub def hir_first_bytes (h : RxHir) : Option (Array I64) :=
    let f : RxFirst := first_of h in
    if f.nullable then Option.none else Option.some f.mask

/// Whether `h` can match without consuming, and the bytes it can start
/// with. Assertions are zero-width, so they count as nullable: the mask
/// is a superset, which is all a filter needs.
struct RxFirst {
    nullable : Bool,
    mask : Array I64,
}

def first_info (nullable : Bool) (mask : Array I64) : RxFirst :=
    let f : RxFirst := { nullable := nullable, mask := mask } in f

/// The UTF-8 lead byte of a scalar. Lead bytes grow with the scalar, so a
/// range's leads lie between its ends' leads.
def lead_byte (c : I64) : I64 :=
    if I64.lt c 128 then c
    else if I64.lt c 2048 then I64.or 192 (I64.shr c 6)
    else if I64.lt c 65536 then I64.or 224 (I64.shr c 12)
    else I64.or 240 (I64.shr c 18)

#[terminating]
def ranges_mask (ranges : List (Pair I64 I64)) (bytes : Bool) (m : Array I64) : Array I64 :=
    match ranges {
        List.empty => m,
        List.cons r rest =>
            if bytes then ranges_mask rest bytes (mask_add_range m r.first r.second)
            else ranges_mask rest bytes (mask_add_range m (lead_byte r.first) (lead_byte r.second)),
    }

#[terminating]
def first_of (h : RxHir) : RxFirst :=
    match h {
        RxHir.empty => first_info true mask_empty,
        RxHir.cset ranges bytes => first_info false (ranges_mask ranges bytes mask_empty),
        RxHir.look _ => first_info true mask_empty,
        RxHir.repetition min _ _ sub =>
            let f : RxFirst := first_of sub in
            first_info (I64.beq min 0 || f.nullable) f.mask,
        RxHir.capture _ sub => first_of sub,
        RxHir.concat items => first_concat items mask_empty,
        RxHir.alternation items => first_alt items false mask_empty,
    }

/// Items contribute until one cannot be skipped.
#[terminating]
def first_concat (items : List RxHir) (m : Array I64) : RxFirst :=
    match items {
        List.empty => first_info true m,
        List.cons h rest =>
            let f : RxFirst := first_of h in
            let m2 : Array I64 := mask_union m f.mask in
            if f.nullable then first_concat rest m2 else first_info false m2,
    }

#[terminating]
def first_alt (items : List RxHir) (nullable : Bool) (m : Array I64) : RxFirst :=
    match items {
        List.empty => first_info nullable m,
        List.cons h rest =>
            let f : RxFirst := first_of h in
            first_alt rest (nullable || f.nullable) (mask_union m f.mask),
    }

def mask_union (a : Array I64) (b : Array I64) : Array I64 :=
    let w : List I64 := [
        I64.or (Array.get_or a 0 0) (Array.get_or b 0 0),
        I64.or (Array.get_or a 1 0) (Array.get_or b 1 0),
        I64.or (Array.get_or a 2 0) (Array.get_or b 2 0),
        I64.or (Array.get_or a 3 0) (Array.get_or b 3 0),
    ] in
    Array.from_list w

// ─── Match length ───

/// Lengths past this are treated as unbounded.
def len_cap : I64 := 1000000000

/// The longest match in bytes, or none when it is unbounded.
#[terminating]
pub def hir_max_len (h : RxHir) : Option I64 :=
    match h {
        RxHir.empty => Option.some 0,
        RxHir.cset ranges bytes => Option.some (if bytes then 1 else scalar_len (last_hi ranges 0)),
        RxHir.look _ => Option.some 0,
        RxHir.repetition _ max _ sub =>
            match hir_max_len sub {
                Option.some n =>
                    if I64.beq n 0 then Option.some 0
                    else
                        match max {
                            Option.some k => capped (if I64.lt (I64.div len_cap n) k then len_cap + 1 else n * k),
                            Option.none => Option.none,
                        },
                Option.none => Option.none,
            },
        RxHir.capture _ sub => hir_max_len sub,
        RxHir.concat items => max_concat items 0,
        RxHir.alternation items => max_alt items 0,
    }

def capped (n : I64) : Option I64 := if I64.lt len_cap n then Option.none else Option.some n

#[terminating]
def last_hi (ranges : List (Pair I64 I64)) (acc : I64) : I64 :=
    match ranges {
        List.empty => acc,
        List.cons r rest => last_hi rest (if I64.lt acc r.second then r.second else acc),
    }

def scalar_len (c : I64) : I64 :=
    if I64.lt c 128 then 1 else if I64.lt c 2048 then 2 else if I64.lt c 65536 then 3 else 4

#[terminating]
def max_concat (items : List RxHir) (acc : I64) : Option I64 :=
    match items {
        List.empty => capped acc,
        List.cons h rest =>
            match hir_max_len h {
                Option.some n => if I64.lt len_cap (acc + n) then Option.none else max_concat rest (acc + n),
                Option.none => Option.none,
            },
    }

#[terminating]
def max_alt (items : List RxHir) (acc : I64) : Option I64 :=
    match items {
        List.empty => Option.some acc,
        List.cons h rest =>
            match hir_max_len h {
                Option.some n => max_alt rest (if I64.lt acc n then n else acc),
                Option.none => Option.none,
            },
    }

// ─── DFA eligibility ───

/// Whether the lazy DFA can run `h`: its only assertions are `\A`/`^` and
/// `\z`/`$` outside multi-line mode, which the DFA resolves from where a
/// search starts and ends. Line and word assertions need the byte before
/// a position, which the DFA does not track until Phase 6.
#[terminating]
pub def hir_dfa_ok (h : RxHir) : Bool :=
    match h {
        RxHir.look kind =>
            match kind {
                RxLook.start_text => true,
                RxLook.end_text => true,
                _ => false,
            },
        RxHir.repetition _ _ _ sub => hir_dfa_ok sub,
        RxHir.capture _ sub => hir_dfa_ok sub,
        RxHir.concat items => all_dfa_ok items,
        RxHir.alternation items => all_dfa_ok items,
        _ => true,
    }

#[terminating]
def all_dfa_ok (items : List RxHir) : Bool :=
    match items {
        List.empty => true,
        List.cons h rest => hir_dfa_ok h && all_dfa_ok rest,
    }
