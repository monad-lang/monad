/// The lazy DFA: deterministic states built on demand from sets of NFA
/// states, so each haystack byte costs one table read once the states it
/// needs exist. This is the RE2 / `regex-automata` hybrid design.
///
/// A DFA state is the ORDERED list of NFA states that the Pike VM's thread
/// list would hold at a position, without capture slots. It holds
/// consuming states, `accept`, any pending `\z` assertions, and the restart
/// marker. Two modes:
///
/// - **Leftmost-first** (forward): the list is cut after `accept`, which
///   drops every lower-priority thread, the Pike VM's rule. An unanchored
///   search keeps a restart marker at the lowest priority: stepping it
///   starts a new attempt, and a match cuts it, so no attempt starts after
///   the first match.
/// - **All matches** (reverse): nothing is cut. Scanning backwards from a
///   match end, the last match state seen gives the leftmost start.
///
/// Assertions: `\A` is resolved when the start state is built (it holds
/// only where the text starts); `\z` stays pending in the state and is
/// resolved by an end-of-input closure. Line and word assertions never
/// reach the DFA (`hir_dfa_ok`).
///
/// The cache is an ordinary value threaded through the search. Once it
/// outgrows its byte limit it is cleared; after `max_clears` clears the
/// search gives up (`quit`) and the caller falls back to the Pike VM (G3).
use lib::hir {RxLook}
use lib::nfa {RxProg, RxState}
use lib::pikevm {bit_test, bit_set, fresh_set, find_trans}
use lib::table {RxTable, table_get, table_set, table_push, table_len, table_of_list}
use lib::literal {mask_has}
use lib::prefilter {RxSkip, skip_to_mask}
use std::array {Array}
use std::list {}

/// Where it sits in a state, a new attempt starts at the lowest priority.
def restart_pc : I64 := 0 - 2

def max_clears : I64 := 3

def nbuckets : I64 := 256

/// A program and how to run it.
pub struct RxDfa {
    prog : RxProg,
    /// Leftmost-first (true) or all matches (false).
    cut : Bool,
    /// The cache's byte budget.
    limit : I64,
    /// `table_get`'s fallback, built once rather than per search.
    dead : RxDState,
}

pub def dfa_new (prog : RxProg) (cut : Bool) (limit : I64) : RxDfa :=
    let d : RxDfa := { prog := prog, cut := cut, limit := limit, dead := dead_state } in d

pub struct RxDState {
    pcs : List I64,
    is_match : Bool,
    /// Indexed by byte class; -1 is not computed yet.
    trans : Array I64,
}

struct RxDKey {
    pcs : List I64,
    id : I64,
}

/// State 0 is the dead state.
pub struct RxDfaCache {
    states : RxTable RxDState,
    buckets : RxTable (List RxDKey),
    /// Start state ids, -1 until built: index 2 * anchored + at_start.
    starts : Array I64,
    bytes : I64,
    clears : I64,
    gave_up : Bool,
}

def dead_state : RxDState :=
    let s : RxDState := { pcs := List.empty, is_match := false, trans := Array.empty } in s

#[terminating]
def empty_buckets (n : I64) (acc : List (List RxDKey)) : List (List RxDKey) :=
    if I64.lt 0 n then empty_buckets (n - 1) (List.cons List.empty acc) else acc

/// An empty cache. Building one costs a 256-bucket table, so a compiled
/// regex keeps a fresh one to hand out.
pub def dfa_cache_new (clears : I64) : RxDfaCache :=
    let c : RxDfaCache := {
        states := table_of_list [dead_state],
        buckets := table_of_list (empty_buckets nbuckets List.empty),
        starts := Array.new 4 (-1),
        bytes := 0,
        clears := clears,
        gave_up := false,
    } in
    c

/// How many times the cache was cleared, and whether it gave up.
pub def dfa_cache_clears (c : RxDfaCache) : I64 := c.clears

pub def dfa_cache_gave_up (c : RxDfaCache) : Bool := c.gave_up

// ─── Closure ───

struct RxDc {
    seen : Array I64,
    /// Newest first.
    out : List I64,
    matched : Bool,
    /// Set when a leftmost-first closure reached `accept`.
    stop : Bool,
}

def fresh_dc (d : RxDfa) : RxDc :=
    let c : RxDc := { seen := fresh_set d.prog, out := List.empty, matched := false, stop := false } in c

def emit (acc : RxDc) (pc : I64) : RxDc := { acc with out := List.cons pc acc.out }

/// Depth first from the stack's top, as the Pike VM's closure. The output
/// is in priority order (reversed); in leftmost-first mode reaching
/// `accept` stops, discarding the lower-priority rest of the stack.
#[terminating]
def dclosure (d : RxDfa) (at_start : Bool) (at_end : Bool) (stack : List I64) (acc : RxDc) : RxDc :=
    match stack {
        List.empty => acc,
        List.cons pc rest =>
            if I64.beq pc restart_pc then dclosure d at_start at_end rest (emit acc pc)
            else if bit_test acc.seen pc then dclosure d at_start at_end rest acc
            else
                let acc2 : RxDc := { acc with seen := bit_set acc.seen pc } in
                dclosure_state d at_start at_end pc (table_get d.prog.states pc RxState.dead) rest acc2,
    }

#[terminating]
def dclosure_state (d : RxDfa) (at_start : Bool) (at_end : Bool) (pc : I64) (st : RxState) (rest : List I64) (acc : RxDc) : RxDc :=
    match st {
        RxState.goto next => dclosure d at_start at_end (List.cons next rest) acc,
        RxState.union alts => dclosure d at_start at_end (List.append alts rest) acc,
        RxState.capture _ next => dclosure d at_start at_end (List.cons next rest) acc,
        RxState.look kind next =>
            match kind {
                RxLook.start_text =>
                    if at_start then dclosure d at_start at_end (List.cons next rest) acc
                    else dclosure d at_start at_end rest acc,
                RxLook.end_text =>
                    if at_end then dclosure d at_start at_end (List.cons next rest) acc
                    else dclosure d at_start at_end rest (emit acc pc),
                _ => dclosure d at_start at_end rest acc,
            },
        RxState.dead => dclosure d at_start at_end rest acc,
        RxState.accept =>
            let acc2 : RxDc := emit acc pc in
            let acc3 : RxDc := { acc2 with matched := true } in
            if d.cut then { acc3 with stop := true } else dclosure d at_start at_end rest acc3,
        _ => dclosure d at_start at_end rest (emit acc pc),
    }

/// Every state's step over byte `b`, in priority order, into one closure.
#[terminating]
def dstep (d : RxDfa) (pcs : List I64) (b : I64) (acc : RxDc) : RxDc :=
    if acc.stop then acc
    else
        match pcs {
            List.empty => acc,
            List.cons pc rest =>
                if I64.beq pc restart_pc then dstep d rest b (dclosure d false false [d.prog.start, restart_pc] acc)
                else
                    match table_get d.prog.states pc RxState.dead {
                        RxState.byte_range lo hi next =>
                            if I64.lt b lo || I64.lt hi b then dstep d rest b acc
                            else dstep d rest b (dclosure d false false [next] acc),
                        RxState.sparse ts =>
                            match find_trans ts b {
                                Option.some next => dstep d rest b (dclosure d false false [next] acc),
                                Option.none => dstep d rest b acc,
                            },
                        _ => dstep d rest b acc,
                    },
        }

// ─── Interning ───

#[terminating]
def key_hash (pcs : List I64) (h : I64) : I64 :=
    match pcs {
        List.empty => h,
        List.cons pc rest => key_hash rest (I64.and (h * 31 + pc + 3) 1073741823),
    }

#[terminating]
def pcs_eq (a : List I64) (b : List I64) : Bool :=
    match a {
        List.empty => List.is_empty b,
        List.cons x xs =>
            match b {
                List.cons y ys => I64.beq x y && pcs_eq xs ys,
                List.empty => false,
            },
    }

#[terminating]
def bucket_find (bucket : List RxDKey) (pcs : List I64) : I64 :=
    match bucket {
        List.empty => -1,
        List.cons k rest => if pcs_eq k.pcs pcs then k.id else bucket_find rest pcs,
    }

/// An interned state id, and whether the cache was cleared to make room
/// (every id from before is then gone).
type RxIntern {
    interned (id : I64) (cache : RxDfaCache) (cleared : Bool),
    intern_quit (cache : RxDfaCache),
}

def intern (d : RxDfa) (cache : RxDfaCache) (dc : RxDc) : RxIntern :=
    let pcs : List I64 := List.reverse dc.out in
    if List.is_empty pcs then RxIntern.interned 0 cache false
    else
        let bi : I64 := I64.and (key_hash pcs 17) (nbuckets - 1) in
        let found : I64 := bucket_find (table_get cache.buckets bi List.empty) pcs in
        if I64.lt found 0 then
            let cost : I64 := 8 * d.prog.nclasses + 8 * List.length pcs + 64 in
            if I64.lt d.limit (cache.bytes + cost) && I64.lt 1 (table_len cache.states) then
                if I64.lt max_clears (cache.clears + 1) then RxIntern.intern_quit { cache with gave_up := true }
                else
                    match insert d (dfa_cache_new (cache.clears + 1)) pcs dc.matched bi cost {
                        Pair.pair id c2 => RxIntern.interned id c2 true,
                    }
            else
                match insert d cache pcs dc.matched bi cost {
                    Pair.pair id c2 => RxIntern.interned id c2 false,
                }
        else RxIntern.interned found cache false

def insert (d : RxDfa) (cache : RxDfaCache) (pcs : List I64) (is_match : Bool) (bi : I64) (cost : I64) : Pair I64 RxDfaCache :=
    let id : I64 := table_len cache.states in
    let st : RxDState := { pcs := pcs, is_match := is_match, trans := Array.new d.prog.nclasses (-1) } in
    let key : RxDKey := { pcs := pcs, id := id } in
    let c2 : RxDfaCache := {
        cache with
        states := table_push cache.states st,
        buckets := table_set cache.buckets bi (List.cons key (table_get cache.buckets bi List.empty)),
        bytes := cache.bytes + cost,
    } in
    Pair.pair id c2

/// The start state: anchored, or with the restart marker; `at_start`
/// says whether `\A` holds where the search begins.
def start_state (d : RxDfa) (cache : RxDfaCache) (anchored : Bool) (at_start : Bool) : RxIntern :=
    let slot : I64 := (if anchored then 2 else 0) + (if at_start then 1 else 0) in
    let known : I64 := Array.get_or cache.starts slot (-1) in
    if I64.lt known 0 then
        let stack : List I64 := if anchored then [d.prog.start] else [d.prog.start, restart_pc] in
        match intern d cache (dclosure d at_start false stack (fresh_dc d)) {
            RxIntern.interned id c2 cleared => RxIntern.interned id { c2 with starts := Array.set c2.starts slot id } cleared,
            RxIntern.intern_quit c2 => RxIntern.intern_quit c2,
        }
    else RxIntern.interned known cache false

/// Compute the transition of state `sid` over `b` (class `cls`) and
/// install it, unless making room cleared `sid` away.
def fill (d : RxDfa) (cache : RxDfaCache) (sid : I64) (st : RxDState) (b : I64) (cls : I64) : RxIntern :=
    match intern d cache (dstep d st.pcs b (fresh_dc d)) {
        RxIntern.interned id c2 cleared =>
            if cleared then RxIntern.interned id c2 true
            else
                let st2 : RxDState := { st with trans := Array.set st.trans cls id } in
                RxIntern.interned id { c2 with states := table_set c2.states sid st2 } false,
        RxIntern.intern_quit c2 => RxIntern.intern_quit c2,
    }

// ─── Scanning ───

/// What a scan returns: the last match position (-1 for none), whether
/// it gave up, and whether the match was recorded at the end of the input.
pub struct RxDfaRun {
    found : I64,
    quit : Bool,
    at_eoi : Bool,
    cache : RxDfaCache,
}

struct RxScan {
    dfa : RxDfa,
    /// +1 forward, -1 reverse.
    dir : I64,
    earliest : Bool,
    /// While in the unanchored start state, bytes outside this are skipped.
    mask : Option (Array I64),
    /// Whether the end of the bytes is an end of the text (`\z` holds).
    eoi_ok : Bool,
    /// Whether `\A` held where the scan began, and that position.
    start_ok : Bool,
    start_pos : I64,
}

def finish (found : I64) (at_eoi : Bool) (cache : RxDfaCache) : RxDfaRun :=
    let r : RxDfaRun := { found := found, quit := false, at_eoi := at_eoi, cache := cache } in r

def quit_run (cache : RxDfaCache) : RxDfaRun :=
    let r : RxDfaRun := { found := -1, quit := true, at_eoi := false, cache := cache } in r

def skippable (x : RxScan) (b : I64) : Bool :=
    match x.mask {
        Option.some m => Bool.not (mask_has m b),
        Option.none => false,
    }

/// At the end of the bytes: whether a pending `\z` leads to `accept`.
def eoi_match (x : RxScan) (st : RxDState) (pos : I64) : Bool :=
    if x.eoi_ok then
        let dc : RxDc := dclosure x.dfa (x.start_ok && I64.beq pos x.start_pos) true st.pcs (fresh_dc x.dfa) in
        dc.matched
    else false

/// One byte per step; the measure is the bytes left in `rest`. `start_id`
/// is the unanchored start state where the prefilter may skip (-1: none).
#[terminating]
def scan_go (x : RxScan) (cache : RxDfaCache) (sid : I64) (start_id : I64) (rest : List U8) (pos : I64) (last : I64) : RxDfaRun :=
    if I64.beq sid 0 then finish last false cache
    else
        let st : RxDState := table_get cache.states sid x.dfa.dead in
        let last2 : I64 := if st.is_match then pos else last in
        if st.is_match && x.earliest then finish pos false cache
        else
            match rest {
                List.empty =>
                    let final : I64 := if eoi_match x st pos then pos else last2 in
                    finish final (I64.beq final pos) cache,
                List.cons b more =>
                    let byte : I64 := U8.to_i64 b in
                    if I64.beq sid start_id && skippable x byte then
                        match x.mask {
                            Option.some m =>
                                let s : RxSkip := skip_to_mask m more (I64.add pos 1) in
                                scan_go x cache sid start_id s.rest s.pos last2,
                            Option.none => scan_go x cache sid start_id more (I64.add pos 1) last2,
                        }
                    else
                        let cls : I64 := Array.get_or x.dfa.prog.classes byte 0 in
                        let t : I64 := Array.get_or st.trans cls (-1) in
                        if I64.lt t 0 then
                            match fill x.dfa cache sid st byte cls {
                                RxIntern.interned id c2 cleared =>
                                    scan_go x c2 id (if cleared then -1 else start_id) more (I64.add pos x.dir) last2,
                                RxIntern.intern_quit c2 => quit_run c2,
                            }
                        else scan_go x cache t start_id more (I64.add pos x.dir) last2,
            }

/// The end of the leftmost-first match from `pos` on, unanchored.
/// `earliest` stops at the first match state (enough for `is_match`).
pub def dfa_forward (d : RxDfa) (cache : RxDfaCache) (rest : List U8) (pos : I64) (mask : Option (Array I64)) (earliest : Bool) : RxDfaRun :=
    if cache.gave_up then quit_run cache
    else
        let at_start : Bool := I64.beq pos 0 in
        let x : RxScan := {
            dfa := d, dir := 1, earliest := earliest, mask := mask, eoi_ok := true,
            start_ok := at_start, start_pos := pos,
        } in
        match start_state d cache false at_start {
            RxIntern.interned sid c1 _ =>
                match mask {
                    Option.some _ => forward_with_filter x c1 sid rest pos,
                    Option.none => scan_go x c1 sid (-1) rest pos (-1),
                },
            RxIntern.intern_quit c1 => quit_run c1,
        }

/// The prefilter skips only in the start state of a position past the
/// text's start (where `\A` no longer holds).
def forward_with_filter (x : RxScan) (cache : RxDfaCache) (sid : I64) (rest : List U8) (pos : I64) : RxDfaRun :=
    match start_state x.dfa cache false false {
        RxIntern.interned start_id c2 cleared =>
            if cleared then
                match start_state x.dfa c2 false x.start_ok {
                    RxIntern.interned sid2 c3 _ => scan_go x c3 sid2 (-1) rest pos (-1),
                    RxIntern.intern_quit c3 => quit_run c3,
                }
            else scan_go x c2 sid start_id rest pos (-1),
        RxIntern.intern_quit c2 => quit_run c2,
    }

/// The leftmost start of a match ending at `end_pos`: an anchored scan
/// over the bytes before it, newest first (`rev`), keeping the last match.
/// `start_ok`: whether `end_pos` is the end of the text (`\z`, reversed).
/// `eoi_ok`: whether `rev` runs out at the start of the text.
pub def dfa_reverse (d : RxDfa) (cache : RxDfaCache) (rev : List U8) (end_pos : I64) (start_ok : Bool) (eoi_ok : Bool) : RxDfaRun :=
    if cache.gave_up then quit_run cache
    else
        let x : RxScan := {
            dfa := d, dir := -1, earliest := false, mask := Option.none, eoi_ok := eoi_ok,
            start_ok := start_ok, start_pos := end_pos,
        } in
        match start_state d cache true start_ok {
            RxIntern.interned sid c1 _ => scan_go x c1 sid (-1) rev end_pos (-1),
            RxIntern.intern_quit c1 => quit_run c1,
        }
