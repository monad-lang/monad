// Fuzzy search over the graph's motes, modules and declarations.
//
// A candidate is scored against the query in tiers, case-insensitively:
//   1000  its own name equals the query
//    900  its own name starts with the query
//    800  its full path starts with the query
//    600  the query occurs in the full path
//    400  the query's characters occur in order (a subsequence)
// Within a tier, shorter candidates and tighter matches score higher; a
// subsequence pays for each gap and is rewarded for starting at a word
// boundary (`_`, `.`, `:`). The tiers follow ply's picker
// (`motes/ply/src/picker.mo`), so a name you know exactly always beats a
// scattered match.
//
// `Fuzzy.search` keeps only the best `limit` hits while scanning (a bounded
// insertion), so a keystroke costs one pass over the candidates.

use std::list {List.filter, List.any}
use lib::model {Trellis.Graph, Trellis.ModuleNode, Trellis.DeclNode}
use lib::seq {Seq.fold}

/// One search result. `key` is what the projection focuses on: the mote
/// name, the module path or the decl id; `level` says which.
pub struct Fuzzy.Hit {
    key : String,
    label : String,
    detail : String,
    level : String,
    kind : String,
    score : I64,
}

def byte_at (s : String) (i : I64) : I64 :=
    match String.get s i { Option.some b => U8.to_i64 b, Option.none => 0 - 1 }

def is_boundary (c : I64) : Bool := c == 95 || c == 46 || c == 58 || c == 32 || c == 47

/// Gaps of an in-order match of `q` in `c`, from index `qi`/`ci`, or -1 when
/// `q` is not a subsequence. Greedy: each query byte takes its earliest
/// occurrence.
#[terminating]
def subseq_gaps (q : String) (qn : I64) (qi : I64) (c : String) (cn : I64) (ci : I64) (last : I64) (gaps : I64) : I64 :=
    if qi >= qn then gaps
    else if ci >= cn then 0 - 1
    else if byte_at q qi == byte_at c ci
    then subseq_gaps q qn (qi + 1) c cn (ci + 1) ci (if last >= 0 && ci > last + 1 then gaps + 1 else gaps)
    else subseq_gaps q qn qi c cn (ci + 1) last gaps

#[terminating]
def first_match (q0 : I64) (c : String) (cn : I64) (ci : I64) : I64 :=
    if ci >= cn then 0 - 1 else if byte_at c ci == q0 then ci else first_match q0 c cn (ci + 1)

def subseq_score (q : String) (c : String) : Option I64 :=
    let qn : I64 := String.length q in
    let cn : I64 := String.length c in
    let start : I64 := first_match (byte_at q 0) c cn 0 in
    if start < 0 then Option.none
    else
        let gaps : I64 := subseq_gaps q qn 0 c cn start (0 - 1) 0 in
        if gaps < 0 then Option.none
        else
            let bonus : I64 := if start == 0 || is_boundary (byte_at c (start - 1)) then 30 else 0 in
            Option.some (400 + bonus - gaps * 15 - cn / 8)

/// Score `name` (a candidate's own last segment) and `path` (its full,
/// qualified spelling) against `query`. Both are compared lowercased;
/// `query` must already be lowercase. `none` when it does not match at all.
pub def Fuzzy.score (query : String) (name : String) (path : String) : Option I64 :=
    if String.is_empty query then Option.none
    else
        let n : String := String.to_lowercase name in
        let p : String := String.to_lowercase path in
        let extra : I64 := String.length n - String.length query in
        if String.beq n query then Option.some 1000
        else if String.starts_with query n then Option.some (900 - extra)
        else if String.starts_with query p then Option.some (800 - (String.length p - String.length query))
        else if String.contains n query then Option.some (700 - extra)
        else if String.contains p query then Option.some (600 - String.length p / 4)
        else subseq_score query p

// ─── Bounded top-N ───

#[terminating]
def insert_hit (h : Fuzzy.Hit) (hits : List Fuzzy.Hit) : List Fuzzy.Hit :=
    match hits {
        List.empty => [h],
        List.cons x rest => if h.score > x.score then List.cons h hits else List.cons x (insert_hit h rest),
    }

#[terminating]
def take (n : I64) (xs : List Fuzzy.Hit) : List Fuzzy.Hit :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => if n <= 0 then List.empty else List.cons x (take (n - 1) rest),
    }

def keep (limit : I64) (h : Fuzzy.Hit) (hits : List Fuzzy.Hit) : List Fuzzy.Hit := take limit (insert_hit h hits)

// ─── Candidates ───

def tail_of (path : String) : String :=
    match List.reverse (String.split path "::") { List.empty => path, List.cons last _ => last }

def consider (q : String) (limit : I64) (key : String) (name : String) (path : String) (detail : String)
    (level : String) (kind : String) (hits : List Fuzzy.Hit) : List Fuzzy.Hit :=
    match Fuzzy.score q name path {
        Option.none => hits,
        Option.some s =>
            let h : Fuzzy.Hit := { key := key, label := name, detail := detail, level := level, kind := kind,
                score := s } in
            keep limit h hits,
    }

#[terminating]
def scan_motes (q : String) (limit : I64) (motes : List String) (hits : List Fuzzy.Hit) : List Fuzzy.Hit :=
    match motes {
        List.empty => hits,
        List.cons m rest => scan_motes q limit rest (consider q limit m m m "mote" "mote" "mote" hits),
    }

#[terminating]
def scan_modules (q : String) (limit : I64) (ms : List Trellis.ModuleNode) (hits : List Fuzzy.Hit) : List Fuzzy.Hit :=
    match ms {
        List.empty => hits,
        List.cons m rest =>
            scan_modules q limit rest (consider q limit m.path (tail_of m.path) m.path m.path "module" "module" hits),
    }

def scan_decls (q : String) (limit : I64) (external : Bool) (ds : List Trellis.DeclNode)
    (hits : List Fuzzy.Hit) : List Fuzzy.Hit :=
    Seq.fold (fn (acc : List Fuzzy.Hit) (d : Trellis.DeclNode) =>
        if d.external && Bool.not external then acc
        else consider q limit d.id d.name d.id d.module "decl" d.kind acc) hits ds

#[terminating]
def distinct_motes (ms : List Trellis.ModuleNode) (seen : List String) : List String :=
    match ms {
        List.empty => List.reverse seen,
        List.cons m rest =>
            if List.any (fn (s : String) => String.beq s m.mote) seen
            then distinct_motes rest seen
            else distinct_motes rest (List.cons m.mote seen),
    }

pub def Fuzzy.motes (g : Trellis.Graph) : List String := distinct_motes g.modules List.empty

/// The best `limit` motes, modules and declarations for `query`, best
/// first. External declarations (init, std, ...) are searched only when
/// `external` is set; their modules and motes always are.
pub def Fuzzy.search (g : Trellis.Graph) (query : String) (limit : I64) (external : Bool) : List Fuzzy.Hit :=
    let q : String := String.to_lowercase (String.trim query) in
    if String.is_empty q then List.empty
    else scan_decls q limit external g.decls (scan_modules q limit g.modules (scan_motes q limit
        (Fuzzy.motes g) List.empty))
