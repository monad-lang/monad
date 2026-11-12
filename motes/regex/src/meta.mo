/// Strategy selection: which engine answers a search.
///
/// 1. A pattern that is only literals (no capture groups) is a literal
///    scan; no automaton is consulted.
/// 2. A pattern the lazy DFA can run: the forward DFA finds where the
///    leftmost-first match ends (skipping with the first-byte prefilter
///    while it sits in its start state), then the reverse DFA finds where
///    it starts. Captures run the Pike VM anchored at that start.
/// 3. Everything else, and any search whose DFA cache gave up, runs the
///    Pike VM.
///
/// Every path is linear in the haystack: a give-up restarts the search on
/// the Pike VM at most once, so the bound at worst doubles (G1, G3).
use lib::hir {RxHir, hir_reverse}
use lib::nfa {RxProg, compile_prog, estimate}
use lib::literal {hir_literals, literals_mask, hir_first_bytes, mask_full, hir_max_len, hir_dfa_ok}
use lib::prefilter {scan_literals}
use lib::dfa::lazy {RxDfa, RxDfaCache, RxDfaRun, dfa_cache_new, dfa_forward, dfa_reverse, dfa_cache_gave_up, dfa_cache_clears}
use lib::pikevm {RxCursor, RxWords, RxResult, search, search_anchored, cursor_skip}
use std::array {Array}
use std::list {}

pub type RxStrategy {
    strat_literal (lits : List (List I64)) (mask : Array I64),
    strat_dfa (fwd : RxDfa) (rev : RxDfa) (mask : Option (Array I64)) (max_len : Option I64),
    strat_pike,
}

/// Which engine a search uses. `eng_auto` follows the strategy; the
/// others pin one, for the differential tests.
pub type RxEngine {
    eng_auto,
    eng_pike,
    /// The DFA with no prefilter (the Pike VM if the strategy has no DFA).
    eng_dfa_bare,
}

/// A warm search cache: the lazy DFAs' states, reusable across searches
/// of the same regex (`Regex.find_with`).
pub struct Cache {
    fwd : RxDfaCache,
    rev : RxDfaCache,
}

pub def cache_new : Cache :=
    let c : Cache := { fwd := dfa_cache_new 0, rev := dfa_cache_new 0 } in c

/// Whether a DFA in `c` gave up, and how often the caches were cleared.
pub def cache_gave_up (c : Cache) : Bool := dfa_cache_gave_up c.fwd || dfa_cache_gave_up c.rev

pub def cache_clears (c : Cache) : I64 := dfa_cache_clears c.fwd + dfa_cache_clears c.rev

/// `limit` is the program size limit in states; `cache_limit` the DFA
/// cache budget in bytes.
pub def choose_strategy (h : RxHir) (prog : RxProg) (captures : I64) (limit : I64) (cache_limit : I64) : RxStrategy :=
    match literal_strategy h captures {
        Option.some s => s,
        Option.none => if hir_dfa_ok h then dfa_strategy h prog limit cache_limit else RxStrategy.strat_pike,
    }

def literal_strategy (h : RxHir) (captures : I64) : Option RxStrategy :=
    if I64.lt 0 captures then Option.none
    else
        match hir_literals h {
            Option.some lits => Option.some (RxStrategy.strat_literal lits (literals_mask lits)),
            Option.none => Option.none,
        }

/// The reverse program is refused like the forward one: past the size
/// limit the Pike VM runs instead.
def dfa_strategy (h : RxHir) (prog : RxProg) (limit : I64) (cache_limit : I64) : RxStrategy :=
    let rh : RxHir := hir_reverse h in
    if I64.lt limit (estimate rh limit) then RxStrategy.strat_pike
    else
        let fwd : RxDfa := { prog := prog, cut := true, limit := cache_limit } in
        let rev : RxDfa := { prog := compile_prog rh 0, cut := false, limit := cache_limit } in
        let mask : Option (Array I64) :=
            match hir_first_bytes h {
                Option.some m => if mask_full m then Option.none else Option.some m,
                Option.none => Option.none,
            } in
        RxStrategy.strat_dfa fwd rev mask (hir_max_len h)

// ─── Searching ───

/// A span search's answer and the cache to reuse.
pub struct RxFound {
    span : Option (Pair I64 I64),
    cache : Cache,
}

def found (span : Option (Pair I64 I64)) (cache : Cache) : RxFound :=
    let f : RxFound := { span := span, cache := cache } in f

def pike_span (prog : RxProg) (w : RxWords) (c : RxCursor) (cache : Cache) : RxFound :=
    let r : RxResult := search prog w c 2 false in
    match r.slots {
        Option.some slots => found (Option.some (Pair.pair (Array.get_or slots 0 0) (Array.get_or slots 1 0))) cache,
        Option.none => found Option.none cache,
    }

/// The leftmost-first match's span from `c` on.
pub def meta_find (s : RxStrategy) (eng : RxEngine) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) : RxFound :=
    match eng {
        RxEngine.eng_pike => pike_span prog w c cache,
        RxEngine.eng_dfa_bare =>
            match s {
                RxStrategy.strat_dfa fwd rev _ max_len => dfa_find fwd rev Option.none max_len prog w cache c,
                _ => pike_span prog w c cache,
            },
        RxEngine.eng_auto =>
            match s {
                RxStrategy.strat_literal lits mask => found (scan_literals lits mask c.rest c.pos) cache,
                RxStrategy.strat_dfa fwd rev mask max_len => dfa_find fwd rev mask max_len prog w cache c,
                RxStrategy.strat_pike => pike_span prog w c cache,
            },
    }

def dfa_find (fwd : RxDfa) (rev : RxDfa) (mask : Option (Array I64)) (max_len : Option I64) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) : RxFound :=
    let f : RxDfaRun := dfa_forward fwd cache.fwd c.rest c.pos mask false in
    let cache2 : Cache := { cache with fwd := f.cache } in
    if f.quit then pike_span prog w c cache2
    else if I64.lt f.found 0 then found Option.none cache2
    else dfa_start rev max_len prog w cache2 c f.found f.at_eoi

/// Scan back from `end_pos`. Only the last `max_len` bytes can hold the
/// match, so only those are reversed when the length is bounded.
def dfa_start (rev : RxDfa) (max_len : Option I64) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) (end_pos : I64) (at_eoi : Bool) : RxFound :=
    let len : I64 := end_pos - c.pos in
    let take : I64 :=
        match max_len {
            Option.some k => if I64.lt k len then k else len,
            Option.none => len,
        } in
    let bytes : List U8 := rev_take (drop_bytes c.rest (len - take)) take List.empty in
    let r : RxDfaRun := dfa_reverse rev cache.rev bytes end_pos at_eoi (I64.beq (end_pos - take) 0) in
    let cache2 : Cache := { cache with rev := r.cache } in
    if r.quit || I64.lt r.found 0 then pike_span prog w c cache2
    else found (Option.some (Pair.pair r.found end_pos)) cache2

#[terminating]
def drop_bytes (xs : List U8) (n : I64) : List U8 :=
    if I64.lt 0 n then
        match xs {
            List.cons _ rest => drop_bytes rest (n - 1),
            List.empty => xs,
        }
    else xs

/// The first `n` bytes, newest first.
#[terminating]
def rev_take (xs : List U8) (n : I64) (acc : List U8) : List U8 :=
    if I64.lt 0 n then
        match xs {
            List.cons b rest => rev_take rest (n - 1) (List.cons b acc),
            List.empty => acc,
        }
    else acc

/// Whether there is a match from `c` on; stops at the first match state.
pub def meta_is_match (s : RxStrategy) (eng : RxEngine) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) : Pair Bool Cache :=
    match eng {
        RxEngine.eng_pike => Pair.pair (pike_is_match prog w c) cache,
        RxEngine.eng_dfa_bare =>
            match s {
                RxStrategy.strat_dfa fwd _ _ _ => dfa_is_match fwd Option.none prog w cache c,
                _ => Pair.pair (pike_is_match prog w c) cache,
            },
        RxEngine.eng_auto =>
            match s {
                RxStrategy.strat_literal lits mask =>
                    match scan_literals lits mask c.rest c.pos {
                        Option.some _ => Pair.pair true cache,
                        Option.none => Pair.pair false cache,
                    },
                RxStrategy.strat_dfa fwd _ mask _ => dfa_is_match fwd mask prog w cache c,
                RxStrategy.strat_pike => Pair.pair (pike_is_match prog w c) cache,
            },
    }

def pike_is_match (prog : RxProg) (w : RxWords) (c : RxCursor) : Bool :=
    let r : RxResult := search prog w c 2 true in
    match r.slots {
        Option.some _ => true,
        Option.none => false,
    }

def dfa_is_match (fwd : RxDfa) (mask : Option (Array I64)) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) : Pair Bool Cache :=
    let f : RxDfaRun := dfa_forward fwd cache.fwd c.rest c.pos mask true in
    let cache2 : Cache := { cache with fwd := f.cache } in
    if f.quit then Pair.pair (pike_is_match prog w c) cache2
    else Pair.pair (I64.lt (0 - 1) f.found) cache2

/// A search's capture slots and the cache to reuse.
pub struct RxFoundSlots {
    slots : Option (Array I64),
    cache : Cache,
}

def found_slots (slots : Option (Array I64)) (cache : Cache) : RxFoundSlots :=
    let f : RxFoundSlots := { slots := slots, cache := cache } in f

/// `nslots` capture slots of the leftmost-first match from `c` on. With
/// groups to resolve, the Pike VM runs anchored at the span's start.
pub def meta_slots (s : RxStrategy) (eng : RxEngine) (prog : RxProg) (w : RxWords) (cache : Cache) (c : RxCursor) (nslots : I64) : RxFoundSlots :=
    if is_pike s eng then
        let r : RxResult := search prog w c nslots false in
        found_slots r.slots cache
    else
        let f : RxFound := meta_find s eng prog w cache c in
        match f.span {
            Option.none => found_slots Option.none f.cache,
            Option.some sp =>
                if I64.lt 2 nslots then
                    let r : RxResult := search_anchored prog w (cursor_skip prog.needs_word w c (sp.first - c.pos)) nslots in
                    found_slots r.slots f.cache
                else found_slots (Option.some (span_slots sp.first sp.second)) f.cache,
        }

def is_pike (s : RxStrategy) (eng : RxEngine) : Bool :=
    match eng {
        RxEngine.eng_pike => true,
        _ =>
            match s {
                RxStrategy.strat_pike => true,
                _ => false,
            },
    }

def span_slots (st : I64) (en : I64) : Array I64 := Array.set (Array.new 2 st) 1 en
