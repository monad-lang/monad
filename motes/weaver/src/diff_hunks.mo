/// Myers line-diff hunks -- weaver.md Phase 16. `diff.mo` keeps the plain
/// trim render (dumb mode, the too-large fallback); this module is the
/// structured view the transcript and the approval dialog render: hunks
/// with `@@` headers, old/new line numbers, and a `+N -M` statistic.
///
/// The Myers working vector `V` is a `BTreeMap I64 I64` keyed by the
/// diagonal `k`: `Array.set` is the O(n) copying set on both backends
/// (`runtime_core.c`), so it cannot back the inner loop. The edit distance
/// is bounded; past the bound the caller falls back to `Diff.render`.
use weaver::diff {Diff.lines}
use std::map {Map, BTreeMap}
use std::list {List.intercalate}

pub type HunkKind {
    hunk_context,
    hunk_add,
    hunk_remove,
}

pub struct HunkLine {
    kind : HunkKind,
    /// 1-based; 0 on the side this line does not exist.
    old_no : I64,
    new_no : I64,
    text : String,
}

pub struct Hunk {
    old_start : I64,
    old_count : I64,
    new_start : I64,
    new_count : I64,
    lines : List HunkLine,
}

pub def DiffHunks.max_edit_distance : I64 := 2000

def pair_fst (p : Pair A B) : A :=
    match p { Pair.pair a _ => a }

def pair_snd (p : Pair A B) : B :=
    match p { Pair.pair _ b => b }

/// A list indexed by position. `std/array`'s `Array` type is not exported
/// from the mote, so the line arrays are maps (O(log n) reads; the bound
/// keeps the edit distance small).
#[partial]
def index_of {A : Type} (xs : List A) (i : I64) (acc : BTreeMap I64 A) : BTreeMap I64 A :=
    match xs {
        List.empty => acc,
        List.cons x rest => index_of rest (i + 1) (Map.insert i x acc),
    }

def get_of {A : Type} (m : BTreeMap I64 A) (i : I64) (fallback : A) : A :=
    match Map.lookup i m { Option.some v => v, Option.none => fallback }

def at (a : BTreeMap I64 String) (i : I64) : String :=
    get_of a i ""

def vget (v : BTreeMap I64 I64) (k : I64) : I64 :=
    match Map.lookup k v { Option.some x => x, Option.none => 0 }

def vset (v : BTreeMap I64 I64) (k : I64) (x : I64) : BTreeMap I64 I64 :=
    Map.insert k x v

def kind_eq (a b : HunkKind) : Bool :=
    match a {
        HunkKind.hunk_context => match b { HunkKind.hunk_context => true, _ => false },
        HunkKind.hunk_add => match b { HunkKind.hunk_add => true, _ => false },
        HunkKind.hunk_remove => match b { HunkKind.hunk_remove => true, _ => false },
    }

def blank_line : HunkLine :=
    { kind := HunkKind.hunk_context, old_no := 0, new_no := 0, text := "" }

/// Advance the snake: equal lines cost no edit.
#[partial]
def snake (a b : BTreeMap I64 String) (n m x y : I64) : Pair I64 I64 :=
    if x < n && y < m && String.beq (at a x) (at b y)
    then snake a b n m (x + 1) (y + 1)
    else Pair.pair x y

/// One `d`'s diagonals, `k` from `-d` to `d` by 2.
#[partial]
def step_ks (a b : BTreeMap I64 String) (n m d k : I64) (v : BTreeMap I64 I64) : BTreeMap I64 I64 :=
    if k > d
    then v
    else
        let x0 : I64 :=
            if k == 0 - d || (k != d && vget v (k - 1) < vget v (k + 1))
            then vget v (k + 1)
            else vget v (k - 1) + 1 in
        let xy : Pair I64 I64 := snake a b n m x0 (x0 - k) in
        step_ks a b n m d (k + 2) (vset v k (pair_fst xy))

/// Is the endpoint diagonal `n - m` reached? A diagonal is in `V` only
/// after the `d` that computes it, so a missing entry is not success. (The
/// old test read a missing `V[k]` as 0 > -1, so an empty old side -- a new
/// file -- produced no hunks.)
def endpoint_reached (n m : I64) (v : BTreeMap I64 I64) : Bool :=
    match Map.lookup (n - m) v {
        Option.none => false,
        Option.some x => x > n - 1,
    }

/// Forward pass. `trace` holds the V *before* each d, newest first.
#[partial]
def forward (a b : BTreeMap I64 String) (n m d : I64) (v : BTreeMap I64 I64) (trace : List (BTreeMap I64 I64)) (max_d : I64) : Option (Pair (BTreeMap I64 I64) (List (BTreeMap I64 I64))) :=
    if d > max_d
    then Option.none
    else
        let trace2 : List (BTreeMap I64 I64) := List.cons v trace in
        let v2 : BTreeMap I64 I64 := step_ks a b n m d (0 - d) v in
        if endpoint_reached n m v2
        then Option.some (Pair.pair v2 trace2)
        else forward a b n m (d + 1) v2 trace2 max_d

def context_line (a : BTreeMap I64 String) (i j : I64) : HunkLine :=
    let l : HunkLine := { kind := HunkKind.hunk_context, old_no := i + 1, new_no := j + 1, text := at a i } in
    l

def add_line (b : BTreeMap I64 String) (j : I64) : HunkLine :=
    let l : HunkLine := { kind := HunkKind.hunk_add, old_no := 0, new_no := j + 1, text := at b j } in
    l

def remove_line (a : BTreeMap I64 String) (i : I64) : HunkLine :=
    let l : HunkLine := { kind := HunkKind.hunk_remove, old_no := i + 1, new_no := 0, text := at a i } in
    l

/// Walk one snake backwards, prepending its context lines.
#[partial]
def back_snake (a : BTreeMap I64 String) (x y px py : I64) (acc : List HunkLine) : Pair (List HunkLine) (Pair I64 I64) :=
    if x > px && y > py
    then back_snake a (x - 1) (y - 1) px py (List.cons (context_line a (x - 1) (y - 1)) acc)
    else Pair.pair acc (Pair.pair x y)

/// The common prefix before the first edit, as context.
#[partial]
def back_prefix (a : BTreeMap I64 String) (x y : I64) (acc : List HunkLine) : List HunkLine :=
    if x < 1
    then acc
    else back_prefix a (x - 1) (y - 1) (List.cons (context_line a (x - 1) (y - 1)) acc)

#[partial]
def backtrack (a b : BTreeMap I64 String) (trace : List (BTreeMap I64 I64)) (d x y : I64) (acc : List HunkLine) : List HunkLine :=
    if d < 1
    then back_prefix a x y acc
    else match trace {
        List.empty => acc,
        List.cons v rest =>
            let k : I64 := x - y in
            let prev_k : I64 :=
                if k == 0 - d || (k != d && vget v (k - 1) < vget v (k + 1))
                then k + 1
                else k - 1 in
            let prev_x : I64 := vget v prev_k in
            let prev_y : I64 := prev_x - prev_k in
            let pr : Pair (List HunkLine) (Pair I64 I64) := back_snake a x y prev_x prev_y acc in
            let acc2 : List HunkLine := pair_fst pr in
            let x2 : I64 := pair_fst (pair_snd pr) in
            let y2 : I64 := pair_snd (pair_snd pr) in
            if x2 == prev_x
            then backtrack a b rest (d - 1) prev_x prev_y (List.cons (add_line b (y2 - 1)) acc2)
            else backtrack a b rest (d - 1) prev_x prev_y (List.cons (remove_line a (x2 - 1)) acc2),
    }

/// The full edit script in forward order, or none past the bound.
pub def DiffHunks.script (old : String) (new : String) : Option (List HunkLine) :=
    let xs : List String := Diff.lines old in
    let ys : List String := Diff.lines new in
    let a : BTreeMap I64 String := index_of xs 0 BTreeMap.empty in
    let b : BTreeMap I64 String := index_of ys 0 BTreeMap.empty in
    let n : I64 := List.length xs in
    let m : I64 := List.length ys in
    match forward a b n m 0 BTreeMap.empty List.empty DiffHunks.max_edit_distance {
        Option.none => Option.none,
        Option.some pr =>
            let trace : List (BTreeMap I64 I64) := pair_snd pr in
            let d : I64 := List.length trace - 1 in
            // Backtracking walks the path backwards and PREPENDS each line,
            // so its accumulator is already in forward order.
            Option.some (backtrack a b trace d n m List.empty),
    }

def is_change (l : HunkLine) : Bool :=
    match l.kind {
        HunkKind.hunk_context => false,
        _ => true,
    }

/// The next change index at or after `i`.
#[partial]
def next_change (arr : BTreeMap I64 HunkLine) (i n : I64) : Option I64 :=
    if i > n - 1
    then Option.none
    else match Map.lookup i arr {
        Option.none => Option.none,
        Option.some l => if is_change l then Option.some i else next_change arr (i + 1) n,
    }

/// Extend a change group over gaps of at most 6 context lines.
#[partial]
def grow (arr : BTreeMap I64 HunkLine) (last n : I64) : I64 :=
    match next_change arr (last + 1) n {
        Option.none => last,
        Option.some c => if c - last <= 7 then grow arr c n else last,
    }

#[partial]
def slice (arr : BTreeMap I64 HunkLine) (i stop : I64) (acc : List HunkLine) : List HunkLine :=
    if i >= stop
    then List.reverse acc
    else slice arr (i + 1) stop (List.cons (get_of arr i blank_line) acc)

#[partial]
def count_old (ls : List HunkLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons l rest => (if l.old_no == 0 then 0 else 1) + count_old rest,
    }

#[partial]
def count_new (ls : List HunkLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons l rest => (if l.new_no == 0 then 0 else 1) + count_new rest,
    }

#[partial]
def first_old (ls : List HunkLine) (fallback : I64) : I64 :=
    match ls {
        List.empty => fallback,
        List.cons l rest => if l.old_no == 0 then first_old rest fallback else l.old_no,
    }

#[partial]
def first_new (ls : List HunkLine) (fallback : I64) : I64 :=
    match ls {
        List.empty => fallback,
        List.cons l rest => if l.new_no == 0 then first_new rest fallback else l.new_no,
    }

#[partial]
def old_before (arr : BTreeMap I64 HunkLine) (i : I64) (acc : I64) : I64 :=
    if i < 1
    then acc
    else match Map.lookup (i - 1) arr {
        Option.none => acc,
        Option.some l => old_before arr (i - 1) (if l.old_no == 0 then acc else acc + 1),
    }

#[partial]
def new_before (arr : BTreeMap I64 HunkLine) (i : I64) (acc : I64) : I64 :=
    if i < 1
    then acc
    else match Map.lookup (i - 1) arr {
        Option.none => acc,
        Option.some l => new_before arr (i - 1) (if l.new_no == 0 then acc else acc + 1),
    }

def hunk_of (arr : BTreeMap I64 HunkLine) (start stop : I64) : Hunk :=
    let ls : List HunkLine := slice arr start stop List.empty in
    let h : Hunk := {
        old_start := first_old ls (old_before arr start 0),
        old_count := count_old ls,
        new_start := first_new ls (new_before arr start 0),
        new_count := count_new ls,
        lines := ls,
    } in
    h

#[partial]
def group (arr : BTreeMap I64 HunkLine) (i n : I64) (acc : List Hunk) : List Hunk :=
    match next_change arr i n {
        Option.none => List.reverse acc,
        Option.some c =>
            let start : I64 := if c < 3 then 0 else c - 3 in
            let last : I64 := grow arr c n in
            let stop : I64 := if last + 4 > n then n else last + 4 in
            group arr (last + 1) n (List.cons (hunk_of arr start stop) acc),
    }

/// The hunks, or none when nothing changed or the edit-distance bound was
/// hit (the caller then falls back to `Diff.render`).
pub def DiffHunks.hunks (old : String) (new : String) : Option (List Hunk) :=
    match DiffHunks.script old new {
        Option.none => Option.none,
        Option.some ls =>
            let arr : BTreeMap I64 HunkLine := index_of ls 0 BTreeMap.empty in
            Option.some (group arr 0 (List.length ls) List.empty),
    }

def pad (n : I64) : String :=
    let s : String := I64.to_string n in
    let l : I64 := String.length s in
    if l < 2 then String.concat "   " s
    else if l < 3 then String.concat "  " s
    else if l < 4 then String.concat " " s
    else s

def line_text (l : HunkLine) : String :=
    match l.kind {
        HunkKind.hunk_add => String.concat_list ["+  ", pad l.new_no, " | ", l.text],
        HunkKind.hunk_remove => String.concat_list ["-  ", pad l.old_no, " | ", l.text],
        HunkKind.hunk_context => String.concat_list ["   ", pad l.old_no, " | ", l.text],
    }

def header_text (h : Hunk) : String :=
    String.concat_list ["@@ -", I64.to_string h.old_start, ",", I64.to_string h.old_count,
        " +", I64.to_string h.new_start, ",", I64.to_string h.new_count, " @@"]

#[partial]
def render_lines (ls : List HunkLine) (acc : List String) : List String :=
    match ls {
        List.empty => List.reverse acc,
        List.cons l rest => render_lines rest (List.cons (line_text l) acc),
    }

def hunk_text (h : Hunk) : List String :=
    List.cons (header_text h) (render_lines h.lines List.empty)

/// The text form: a `@@` header and gutter-numbered rows per hunk.
pub def DiffHunks.render_text (hs : List Hunk) : String :=
    List.intercalate "\n" (List.flatten (List.map hunk_text hs))

#[partial]
def count_kind (k : HunkKind) (ls : List HunkLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons l rest => (if kind_eq l.kind k then 1 else 0) + count_kind k rest,
    }

#[partial]
def stat_hunks (hs : List Hunk) (adds removes : I64) : Pair I64 I64 :=
    match hs {
        List.empty => Pair.pair adds removes,
        List.cons h rest =>
            let a : I64 := adds + count_kind HunkKind.hunk_add h.lines in
            let r : I64 := removes + count_kind HunkKind.hunk_remove h.lines in
            stat_hunks rest a r,
    }

pub def DiffHunks.stat (hs : List Hunk) : Pair I64 I64 :=
    stat_hunks hs 0 0

/// The largest input the display paths run Myers on; past it the trim
/// render is used (a full-file rewrite must not spend seconds in a dialog).
pub def DiffHunks.max_display_input : I64 := 65536

/// `s` truncated to at most `n` bytes ON a UTF-8 character boundary.
/// `String.slice` answers "" for a cut on either side of a multi-byte
/// character, so a raw byte cut can silently drop the whole string. The
/// boundary is found over the byte list: a one-byte slice probe cannot
/// distinguish "inside a character" from "this character starts here".
def is_continuation (b : U8) : Bool :=
    Bool.and (I64.lt 127 (U8.to_i64 b)) (I64.lt (U8.to_i64 b) 192)

#[partial]
def byte_at (bs : List U8) (i : I64) : Option U8 :=
    match bs {
        List.empty => Option.none,
        List.cons b rest => if i < 1 then Option.some b else byte_at rest (i - 1),
    }

#[partial]
def boundary_go (bs : List U8) (i : I64) : I64 :=
    match byte_at bs i {
        Option.none => i,
        Option.some b => if is_continuation b then boundary_go bs (i - 1) else i,
    }

pub def DiffHunks.cut_utf8 (s : String) (n : I64) : String :=
    let len : I64 := String.length s in
    if I64.lt len (n + 1)
    then s
    else String.slice s 0 (boundary_go (String.to_list s) n)
