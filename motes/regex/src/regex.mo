/// The public regex API.
///
/// Every search is linear in the haystack (O(m·n) for a program of m
/// states): automata only, never a backtracking search. Iterating
/// (`find_all`, `captures_all`, `replace_all`, `split`) runs one search per
/// match, so its worst case is O(m·n²), the bound Rust's `regex` documents
/// for its iterators too.
///
/// Offsets are byte offsets, as `String.slice` takes them. A haystack is a
/// C string compiled, so it cannot contain a NUL byte; `\x00` in a pattern
/// parses but never matches there.
use lib::error {RegexError}
use lib::syntax::parser {parse, RxParsed}
use lib::hir {RxHir, RxFlags, translate}
use lib::nfa {RxProg, compile_prog, estimate}
use lib::pikevm {
    RxCursor, RxWords, RxResult, cursor_start, cursor_advance, cursor_skip, decode_head, search,
}
use lib::table {table_of_list}
use unicode::lookup {Unicode.word_ranges}
use std::array {Array}
use std::list {}

/// How to compile a pattern. `{ pattern := p }` gives the defaults.
pub struct RegexBuilder {
    pattern : String,
    case_insensitive : Bool := false,
    multi_line : Bool := false,
    dot_matches_new_line : Bool := false,
    swap_greed : Bool := false,
    ignore_whitespace : Bool := false,
    unicode : Bool := true,
    /// An approximate bound on the compiled program, in bytes (16 per
    /// state).
    size_limit : I64 := 10485760,
    /// Reserved for the lazy DFA (Phase 5).
    dfa_cache_limit : I64 := 2097152,
    nest_limit : I64 := 250,
}

/// A compiled regex. Its fields are internal.
pub struct Regex {
    pattern : String,
    prog : RxProg,
    words : RxWords,
    captures : I64,
    names : List (Pair String I64),
}

/// One match: `haystack[start, end)`.
pub struct Match {
    haystack : String,
    start : I64,
    end : I64,
}

/// The capture groups of one match. Group 0 is the whole match.
pub struct Captures {
    haystack : String,
    slots : Array I64,
    names : List (Pair String I64),
}

pub def Match.as_str (m : Match) : String := String.slice m.haystack m.start (m.end - m.start)

pub def Match.len (m : Match) : I64 := m.end - m.start

// ─── Building ───

pub def Regex.new (pattern : String) : Result RegexError Regex :=
    let b : RegexBuilder := { pattern := pattern } in RegexBuilder.build b

pub def RegexBuilder.new (pattern : String) : RegexBuilder :=
    let b : RegexBuilder := { pattern := pattern } in b

pub def RegexBuilder.build (b : RegexBuilder) : Result RegexError Regex :=
    match parse b.pattern b.ignore_whitespace b.nest_limit {
        Result.err e => Result.err e,
        Result.ok parsed => build_parsed b parsed,
    }

def build_parsed (b : RegexBuilder) (parsed : RxParsed) : Result RegexError Regex :=
    let flags : RxFlags := {
        case_insensitive := b.case_insensitive,
        multi_line := b.multi_line,
        dot_matches_new_line := b.dot_matches_new_line,
        swap_greed := b.swap_greed,
        unicode := b.unicode,
    } in
    match translate parsed.ast flags {
        Result.err e => Result.err e,
        Result.ok hir => build_hir b parsed hir,
    }

def build_hir (b : RegexBuilder) (parsed : RxParsed) (hir : RxHir) : Result RegexError Regex :=
    let limit : I64 := I64.div b.size_limit 16 in
    if I64.lt limit (estimate hir limit) then Result.err (RegexError.too_big b.size_limit)
    else
        let prog : RxProg := compile_prog hir parsed.captures in
        let words : RxWords := { ranges := table_of_list (if prog.needs_word then Unicode.word_ranges else List.empty) } in
        let r : Regex := {
            pattern := b.pattern,
            prog := prog,
            words := words,
            captures := parsed.captures,
            names := parsed.names,
        } in
        Result.ok r

pub def Regex.as_str (r : Regex) : String := r.pattern

/// The number of capture groups, counting group 0.
pub def Regex.captures_len (r : Regex) : I64 := r.captures + 1

// ─── Searching ───

def cursor_at (r : Regex) (s : String) (start : I64) : RxCursor :=
    cursor_skip r.prog.needs_word r.words (cursor_start (String.to_list s)) start

def run_at (r : Regex) (c : RxCursor) (nslots : I64) : Option (Array I64) :=
    let res : RxResult := search r.prog r.words c nslots false in res.slots

def slot (slots : Array I64) (i : I64) : I64 := Array.get_or slots i (0 - 1)

def match_of (s : String) (slots : Array I64) : Match :=
    let m : Match := { haystack := s, start := slot slots 0, end := slot slots 1 } in m

/// Stops at the first accepting thread: whether there is a match does
/// not need the leftmost-first span settled.
pub def Regex.is_match (r : Regex) (s : String) : Bool :=
    let res : RxResult := search r.prog r.words (cursor_at r s 0) 2 true in
    match res.slots {
        Option.some _ => true,
        Option.none => false,
    }

pub def Regex.find (r : Regex) (s : String) : Option Match := Regex.find_at r s 0

/// The leftmost-first match starting at or after byte `start`. The text
/// before `start` still counts for `^`, `\b` and friends.
pub def Regex.find_at (r : Regex) (s : String) (start : I64) : Option Match :=
    match run_at r (cursor_at r s start) 2 {
        Option.some slots => Option.some (match_of s slots),
        Option.none => Option.none,
    }

pub def Regex.captures (r : Regex) (s : String) : Option Captures :=
    match run_at r (cursor_at r s 0) (2 * (r.captures + 1)) {
        Option.some slots => Option.some (captures_of r s slots),
        Option.none => Option.none,
    }

def captures_of (r : Regex) (s : String) (slots : Array I64) : Captures :=
    let c : Captures := { haystack := s, slots := slots, names := r.names } in c

/// How many thread operations one search from the start took: the G1
/// tests' deterministic clock.
pub def Regex.search_steps (r : Regex) (s : String) : I64 :=
    let res : RxResult := search r.prog r.words (cursor_at r s 0) 2 false in res.steps

// ─── Captures ───

pub def Captures.len (c : Captures) : I64 := I64.div (Array.length c.slots) 2

pub def Captures.get (c : Captures) (i : I64) : Option Match :=
    let a : I64 := slot c.slots (2 * i) in
    let b : I64 := slot c.slots (2 * i + 1) in
    if I64.lt a 0 || I64.lt b 0 then Option.none
    else
        let m : Match := { haystack := c.haystack, start := a, end := b } in
        Option.some m

pub def Captures.name (c : Captures) (n : String) : Option Match :=
    match group_index c.names n {
        Option.some i => Captures.get c i,
        Option.none => Option.none,
    }

#[terminating]
def group_index (names : List (Pair String I64)) (n : String) : Option I64 :=
    match names {
        List.empty => Option.none,
        List.cons e rest => if String.beq e.first n then Option.some e.second else group_index rest n,
    }

/// Group `i`'s text, or "" when it did not participate.
def group_text (c : Captures) (i : I64) : String :=
    match Captures.get c i {
        Option.some m => Match.as_str m,
        Option.none => "",
    }

// ─── Iteration ───

/// Every successive non-overlapping match's slots. After an empty match,
/// a match ending at the same place is skipped by searching again one
/// scalar further on, so iteration never yields two empty matches at one
/// position and never splits a scalar.
def all_slots (r : Regex) (s : String) (nslots : I64) : List (Array I64) :=
    List.reverse (iter_go r nslots (cursor_start (String.to_list s)) (0 - 1) List.empty)

#[terminating]
def iter_go (r : Regex) (nslots : I64) (c : RxCursor) (last_end : I64) (acc : List (Array I64)) : List (Array I64) :=
    match run_at r c nslots {
        Option.none => acc,
        Option.some slots =>
            let st : I64 := slot slots 0 in
            let en : I64 := slot slots 1 in
            if I64.beq st en && I64.beq en last_end then iter_retry r nslots c last_end acc
            else iter_go r nslots (cursor_skip r.prog.needs_word r.words c (en - c.pos)) en (List.cons slots acc),
    }

/// Searching from `c` found an empty match where the last match ended:
/// step one scalar (or stop at the end) and search again.
#[terminating]
def iter_retry (r : Regex) (nslots : I64) (c : RxCursor) (last_end : I64) (acc : List (Array I64)) : List (Array I64) :=
    if List.is_empty c.rest then acc
    else
        let next : RxCursor := cursor_skip r.prog.needs_word r.words c (scalar_width c.rest) in
        iter_go r nslots next last_end acc

def scalar_width (xs : List U8) : I64 :=
    match xs {
        List.empty => 1,
        List.cons b _ =>
            let c : I64 := U8.to_i64 b in
            if I64.lt c 192 then 1 else if I64.lt c 224 then 2 else if I64.lt c 240 then 3 else 4,
    }

pub def Regex.find_all (r : Regex) (s : String) : List Match :=
    List.map (fn (slots : Array I64) => match_of s slots) (all_slots r s 2)

pub def Regex.captures_all (r : Regex) (s : String) : List Captures :=
    List.map (fn (slots : Array I64) => captures_of r s slots) (all_slots r s (2 * (r.captures + 1)))

// ─── Replacement ───

/// `rep` with `$1`, `${1}`, `$name` and `${name}` expanded from `c`, and
/// `$$` a literal `$`. `$name` takes the longest run of `[_0-9A-Za-z]`; a
/// group that does not exist or did not participate expands to "". A `$`
/// starting nothing valid is literal.
pub def Captures.expand (c : Captures) (rep : String) : String :=
    String.concat_list (List.reverse (expand_go c (String.to_list rep) List.empty List.empty))

def is_name_byte (b : I64) : Bool :=
    (I64.lt 47 b && I64.lt b 58) || (I64.lt 64 b && I64.lt b 91) || I64.beq b 95 || (I64.lt 96 b && I64.lt b 123)

/// `lit` gathers literal bytes (newest first) between expansions.
#[terminating]
def expand_go (c : Captures) (xs : List U8) (lit : List U8) (acc : List String) : List String :=
    match xs {
        List.empty => flush_lit lit acc,
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) 36 then expand_dollar c rest (List.cons b lit) acc
            else expand_go c rest (List.cons b lit) acc,
    }

/// After a `$` (already pushed onto `lit` in case it is literal).
#[terminating]
def expand_dollar (c : Captures) (xs : List U8) (lit : List U8) (acc : List String) : List String :=
    let b : I64 := match xs { List.cons x _ => U8.to_i64 x, List.empty => 0 - 1 } in
    if I64.beq b 36 then expand_go c (drop1 xs) lit acc
    else if I64.beq b 123 then
        match take_braced (drop1 xs) List.empty {
            Option.some nm => expand_go c nm.second List.empty (List.cons (group_ref c nm.first) (flush_lit (drop1 lit) acc)),
            Option.none => expand_go c xs lit acc,
        }
    else if is_name_byte b then
        match take_name xs List.empty {
            Pair.pair name rest => expand_go c rest List.empty (List.cons (group_ref c name) (flush_lit (drop1 lit) acc)),
        }
    else expand_go c xs lit acc

def drop1 (xs : List U8) : List U8 :=
    match xs {
        List.cons _ rest => rest,
        List.empty => List.empty,
    }

def flush_lit (lit : List U8) (acc : List String) : List String :=
    if List.is_empty lit then acc else List.cons (String.from_list (List.reverse lit)) acc

#[terminating]
def take_name (xs : List U8) (acc : List U8) : Pair String (List U8) :=
    match xs {
        List.cons b rest =>
            if is_name_byte (U8.to_i64 b) then take_name rest (List.cons b acc)
            else Pair.pair (String.from_list (List.reverse acc)) xs,
        List.empty => Pair.pair (String.from_list (List.reverse acc)) List.empty,
    }

#[terminating]
def take_braced (xs : List U8) (acc : List U8) : Option (Pair String (List U8)) :=
    match xs {
        List.empty => Option.none,
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) 125 then
                if List.is_empty acc then Option.none
                else Option.some (Pair.pair (String.from_list (List.reverse acc)) rest)
            else take_braced rest (List.cons b acc),
    }

/// An all-digit name is an index; anything else a group name.
def group_ref (c : Captures) (name : String) : String :=
    match parse_index (String.to_list name) 0 {
        Option.some i => group_text c i,
        Option.none =>
            match Captures.name c name {
                Option.some m => Match.as_str m,
                Option.none => "",
            },
    }

#[terminating]
def parse_index (xs : List U8) (acc : I64) : Option I64 :=
    match xs {
        List.empty => Option.some acc,
        List.cons b rest =>
            let d : I64 := U8.to_i64 b - 48 in
            if I64.lt d 0 || I64.lt 9 d || I64.lt 100000 acc then Option.none
            else parse_index rest (acc * 10 + d),
    }

/// Replace the first match.
pub def Regex.replace (r : Regex) (s : String) (rep : String) : String :=
    match Regex.captures r s {
        Option.some c => splice s [c] (fn (x : Captures) => Captures.expand x rep),
        Option.none => s,
    }

pub def Regex.replace_all (r : Regex) (s : String) (rep : String) : String :=
    splice s (Regex.captures_all r s) (fn (x : Captures) => Captures.expand x rep)

/// Replace every match with `f` of its captures; no `$` expansion.
pub def Regex.replace_all_with (r : Regex) (s : String) (f : Captures -> String) : String :=
    splice s (Regex.captures_all r s) f

/// `s` with each capture's whole match replaced by `f` of it. The matches
/// are ascending and disjoint.
def splice (s : String) (cs : List Captures) (f : Captures -> String) : String :=
    String.concat_list (List.reverse (splice_go s cs f 0 List.empty))

#[terminating]
def splice_go (s : String) (cs : List Captures) (f : Captures -> String) (last : I64) (acc : List String) : List String :=
    match cs {
        List.empty => List.cons (String.slice s last (String.length s - last)) acc,
        List.cons c rest =>
            let st : I64 := slot c.slots 0 in
            let en : I64 := slot c.slots 1 in
            splice_go s rest f en (List.cons (f c) (List.cons (String.slice s last (st - last)) acc)),
    }

// ─── Splitting ───

/// The text between matches, including empty pieces and a trailing one.
pub def Regex.split (r : Regex) (s : String) : List String :=
    pieces s (Regex.find_all r s) (0 - 1)

/// At most `limit` pieces; the last is the rest of the text.
pub def Regex.splitn (r : Regex) (s : String) (limit : I64) : List String :=
    if I64.lt limit 1 then List.empty else pieces s (Regex.find_all r s) (limit - 1)

/// `budget` matches may split (-1: all of them).
def pieces (s : String) (ms : List Match) (budget : I64) : List String :=
    List.reverse (pieces_go s ms budget 0 List.empty)

#[terminating]
def pieces_go (s : String) (ms : List Match) (budget : I64) (last : I64) (acc : List String) : List String :=
    match ms {
        List.empty => List.cons (String.slice s last (String.length s - last)) acc,
        List.cons m rest =>
            if I64.beq budget 0 then List.cons (String.slice s last (String.length s - last)) acc
            else pieces_go s rest (budget - 1) m.end (List.cons (String.slice s last (m.start - last)) acc),
    }

// ─── Escaping ───

/// `s` with every metacharacter backslash-escaped, so it matches literally.
pub def Regex.escape (s : String) : String :=
    String.from_list (List.reverse (escape_go (String.to_list s) List.empty))

def is_meta (b : I64) : Bool :=
    I64.beq b 92 || I64.beq b 46 || I64.beq b 43 || I64.beq b 42 || I64.beq b 63 || I64.beq b 40
        || I64.beq b 41 || I64.beq b 124 || I64.beq b 91 || I64.beq b 93 || I64.beq b 123
        || I64.beq b 125 || I64.beq b 94 || I64.beq b 36 || I64.beq b 35 || I64.beq b 38
        || I64.beq b 45 || I64.beq b 126

#[terminating]
def escape_go (xs : List U8) (acc : List U8) : List U8 :=
    match xs {
        List.empty => acc,
        List.cons b rest =>
            if is_meta (U8.to_i64 b) then escape_go rest (List.cons b (List.cons 92u8 acc))
            else escape_go rest (List.cons b acc),
    }
