// Ply's rope: a persistent balanced binary tree over String leaves.
//
// THE WORKING UNIT IS A BYTE OFFSET (the plan's Decision 2), matching
// `String.length`/`String.slice` and `toolkit::text`'s TextSpan. Line/column
// for display and UTF-16 for the LSP wire are derived at the edge, never
// stored here.
//
// Every NODE caches its byte count, newline count and depth, so a tree of
// any shape answers `bytes`/`newlines` in O(1) and an offset<->line descent
// is O(depth). The cache is a value the constructors compute, so a Rope
// built through `Rope.concat`/`Rope.of_string`/`Rope.replace` is always
// consistent -- there is no invalid state to defend against.
//
// `<=`/`>=` ARE NOT BOUND (init/src/prelude.mo's TODO), so every range test
// is written with `<`, `>` and negation, exactly as the plan's Design §2
// already does.

use lib::types {Rope}

use init::copy {Copy}

/// A rope is an immutable persistent tree, so duplicating the VALUE
/// duplicates handles to immutable bytes -- the same reading `Copy
/// String` records (`init/src/copy.mo`'s "a bitwise duplicate is the
/// correct duplicate"), and the same reason `Rect`/`TextStyle` carry
/// field-wise instances in `motes/tui/src/core.mo`. Nothing in the rope
/// mutates in place, so two owners cannot observe each other; the
/// "deliberately absent" list in `init/src/copy.mo` covers MUTABLE and
/// borrow-shaped values, and a persistent rope is neither.
///
/// The instance lives here rather than in `types.mo` because an instance
/// is a function body, and a derive-bearing file must hold none
/// (`motes/tui/src/types.mo`'s rule).
pub instance Copy Rope {
    def copy (r : Rope) : Pair Rope Rope :=
        match r {
            Rope.leaf t => Pair.pair (Rope.leaf t) (Rope.leaf t),
            Rope.node l rt b n d => Pair.pair (Rope.node l rt b n d) (Rope.node l rt b n d)
        }
}

/// Bytes in the rope. O(1): a node caches its total.
pub def Rope.bytes (r : Rope) : I64 :=
    match r {
        Rope.leaf t => String.length t,
        Rope.node _ _ b _ _ => b
    }

/// Newlines in the rope. O(1) at a node; a leaf asks the native.
pub def Rope.newlines (r : Rope) : I64 :=
    match r {
        Rope.leaf t => String.count_newlines t (String.length t),
        Rope.node _ _ _ n _ => n
    }

pub def Rope.depth (r : Rope) : I64 :=
    match r {
        Rope.leaf _ => 0,
        Rope.node _ _ _ _ d => d
    }

def max_i64 (a : I64) (b : I64) : I64 := if a > b then a else b

/// Join two ropes, caching the totals. Rebalancing is `Rope.balance`'s job.
pub def Rope.concat (l : Rope) (r : Rope) : Rope :=
    Rope.node l r (Rope.bytes l + Rope.bytes r) (Rope.newlines l + Rope.newlines r) (max_i64 (Rope.depth l) (Rope.depth r) + 1)

/// Bytes `[start, start + len)` as one string.
pub def Rope.slice (r : Rope) (start : I64) (len : I64) : String :=
    match r {
        Rope.leaf t => String.slice t start len,
        Rope.node l rt _ _ _ =>
            let lb := Rope.bytes l in
            if (start + len) > lb
            then (if start < lb
                  then Rope.slice l start (lb - start) ++ Rope.slice rt 0 (len - (lb - start))
                  else Rope.slice rt (start - lb) len)
            else Rope.slice l start len
    }

/// The whole rope as one string -- the round-trip oracle and the debug
/// printer. O(n) over the leaves, and only ever called by tests and by
/// Phase 4's file writer, never by the editing loop.
pub def Rope.to_string (r : Rope) : String :=
    Rope.slice r 0 (Rope.bytes r)

// ── Building ────────────────────────────────────────────────────────────
//
// A leaf never splits a UTF-8 sequence, so the chunker below cuts only at
// bytes that are NOT continuation bytes (`toolkit::bytes`'s predicate is
// the stated rule; the three-way character test here is its byte shape:
// `0b10xxxxxx` is `0x80..=0xbf`).

/// The chunking target, in bytes. Small enough that a viewport of lines
/// touches a handful of leaves; large enough that a 1 MiB file is ~1 KiB
/// leaves rather than thousands of tiny ones.
pub def Rope.chunk_bytes : I64 := 1024

/// A chunk boundary is a character boundary: the byte is ASCII or a lead
/// byte. `String.get` is an O(1) byte read (`init/src/string.mo`'s note
/// against `String.get_char`'s Vec<char> rebuild), so this test is cheap.
def rope_char_boundary (s : String) (i : I64) : Bool :=
    match String.get s i {
        Option.none => false,
        Option.some b => rope_is_boundary_byte b
    }

/// "Not a continuation byte": ASCII (`b < 0x80`) or a lead byte
/// (`b > 0xbf`). The byte a character STARTS at satisfies this.
def rope_is_boundary_byte (b : U8) : Bool :=
    Bool.not (U8.gt b 127u8 && Bool.not (U8.gt b 191u8))

/// Chunk `s` into leaf texts of about `Rope.chunk_bytes` bytes, cutting only
/// on character boundaries and preferring the byte after a `\n` when one is
/// near the target.
///
/// The scan keeps two cut points as it walks: the first character boundary
/// at or after the target size, and the best `\n`+1 boundary seen before
/// it. Either can be absent (an empty tail, a run of fewer bytes than the
/// target), and the one chosen is: a newline boundary past half the
/// target, else the plain character boundary.
#[terminating]
def rope_chunks_go (s : String) (from : I64) (n : I64) : List String :=
    if I64.beq n 0
    then List.empty
    else
        let target := from + Rope.chunk_bytes in
        let plain := rope_boundary_from s from target n in
        let nl := rope_newline_from s from target n in
        match rope_pick_cut from n plain nl {
            Option.none => rope_chunks_tail s from n,
            Option.some cut => rope_chunk_emit s from n cut
        }

/// Emit the chunk `[from, cut)` and recurse into the rest -- split out so
/// the picked `cut` is bound exactly once per use.
#[terminating]
def rope_chunk_emit (s : String) (from : I64) (n : I64) (cut : I64) : List String :=
    List.cons (String.slice s from (cut - from)) (rope_chunks_go s cut (n - (cut - from)))

/// The first character boundary at or after `target`, if any byte exists
/// there. `target - from` bytes of lookahead is bounded by the tail length.
#[terminating]
def rope_boundary_from (s : String) (from : I64) (target : I64) (n : I64) : Option I64 :=
    rope_boundary_go s (max_i64 from target) (from + n)

#[terminating]
def rope_boundary_go (s : String) (i : I64) (stop : I64) : Option I64 :=
    if Bool.not (i < stop)
    then Option.none
    else if rope_char_boundary s i then Option.some i else rope_boundary_go s (i + 1) stop

/// The LAST `\n` byte in `[from, from+n)` whose successor is a character
/// boundary, as a cut point at the newline's successor -- so a leaf ends
/// WITH its line terminator and the next starts a fresh line.
///
/// Takes the last one rather than the first so a chunk spans as much of the
/// target as possible; both ends are character boundaries either way.
#[terminating]
def rope_newline_from (s : String) (from : I64) (target : I64) (n : I64) : Option I64 :=
    rope_newline_go s (min_i64 (from + n) (target + Rope.chunk_bytes)) from Option.none

#[terminating]
def rope_newline_go (s : String) (stop : I64) (i : I64) (best : Option I64) : Option I64 :=
    if Bool.not (i < stop)
    then best
    else
        match String.get s i {
            Option.none => best,
            Option.some b => rope_newline_step s stop i best b
        }

def min_i64 (a : I64) (b : I64) : I64 := if a < b then a else b

/// One byte of the newline scan: a `\n` whose successor is a character
/// boundary updates the best cut; anything else leaves the best cut alone.
/// Split out so the byte is bound once and the cut arithmetic once.
#[terminating]
def rope_newline_step (s : String) (stop : I64) (i : I64) (best : Option I64) (b : U8) : Option I64 :=
    if U8.beq b 10u8 && rope_char_boundary s (i + 1)
    then rope_newline_go s stop (i + 1) (Option.some (i + 1))
    else rope_newline_go s stop (i + 1) best

/// Choose between the two cut candidates. A newline boundary only wins if
/// it is at least half the target size away, so a lone early newline cannot
/// make a leaf tiny; and it must exist, as must the plain boundary.
def rope_pick_cut (from : I64) (n : I64) (plain : Option I64) (nl : Option I64) : Option I64 :=
    match nl {
        Option.some cut => rope_pick_newline from n cut plain,
        Option.none => rope_pick_plain plain
    }

/// The newline cut wins when it is at least half a chunk away (a lone early
/// newline cannot make a leaf tiny) and not the whole tail (a chunk needs a
/// successor to exist). Otherwise the plain character boundary.
def rope_pick_newline (from : I64) (n : I64) (cut : I64) (plain : Option I64) : Option I64 :=
    if (cut - from) > (Rope.chunk_bytes / 2) && (cut - from) < n
    then Option.some cut
    else rope_pick_plain plain

def rope_pick_plain (plain : Option I64) : Option I64 :=
    match plain {
        Option.some cut => Option.some cut,
        Option.none => Option.none
    }

/// The final tail: whatever remains when no cut point was found. A
/// non-empty tail is one more leaf (its bytes are all one chunk; the scan
/// guarantees `from` is a boundary because every prior cut was).
def rope_chunks_tail (s : String) (from : I64) (n : I64) : List String :=
    if I64.beq n 0 then List.empty else List.cons (String.slice s from n) List.empty

/// A rope over `s`: the empty rope for the empty string, one leaf for
/// anything under the chunk target, and a balanced tree of chunked leaves
/// otherwise.
pub def Rope.of_string (s : String) : Rope :=
    let n := String.length s in
    if I64.beq n 0
    then Rope.leaf ""
    else if Bool.not (Rope.chunk_bytes < n)
    then Rope.leaf s
    else Rope.from_leaf_texts (rope_chunks_go s 0 n)

/// Build a balanced tree over a list of leaf texts (non-empty list; the
/// empty rope is `Rope.leaf ""` above).
///
/// Bottom-up pairwise merge: every text becomes a leaf, then adjacent ropes
/// are joined by `Rope.concat` one level at a time -- leaves, pairs, pairs
/// of pairs -- until one rope remains. Each level halves the list, so a
/// chunked file lands at depth ceil(log2 leaves) and `Rope.slice`/
/// `line_start` pay the minimum descent. Left-to-right merge order keeps
/// the text order, unlike a fold that conses onto a running list.
#[terminating]
pub def Rope.from_leaf_texts (ts : List String) : Rope :=
    rope_merge_levels (rope_leaf_ropes ts)

/// Every text as a leaf rope, in order.
#[terminating]
def rope_leaf_ropes (ts : List String) : List Rope :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (Rope.leaf t) (rope_leaf_ropes rest)
    }

#[terminating]
def rope_merge_levels (level : List Rope) : Rope :=
    match level {
        List.cons one rest => rope_merge_level_one one rest,
        List.empty => Rope.leaf ""
    }

/// The level has at least one rope: a lone rope IS the result; otherwise
/// one pairwise pass and recurse. (`List.cons one List.empty => one`
/// would be the direct shape, but a bare nullary constructor as a pattern's
/// final positional argument is a parse error -- `motes/tui`'s own matches
/// all bind the tail instead, and this file follows that.)
#[terminating]
def rope_merge_level_one (one : Rope) (rest : List Rope) : Rope :=
    match rest {
        List.empty => one,
        List.cons two more => rope_merge_levels (rope_merge_pairs_from one two more)
    }

/// The pairwise pass seeded with this level's first three ropes, so the
/// level list itself is never rebuilt or used twice.
#[terminating]
def rope_merge_pairs_from (one : Rope) (two : Rope) (more : List Rope) : List Rope :=
    List.cons (Rope.concat one two) (rope_merge_pairs more)

/// One pass: join each adjacent pair. A single trailing rope carries to
/// the next level unchanged; `Rope.concat` computes the node's caches.
#[terminating]
def rope_merge_pairs (level : List Rope) : List Rope :=
    match level {
        List.cons a rest => rope_merge_pair_one a rest,
        List.empty => List.empty
    }

/// Join the first pair and carry the rest; a lone trailing rope passes
/// through unchanged. Same tail-binding shape as `rope_merge_level_one`,
/// for the same parse reason.
#[terminating]
def rope_merge_pair_one (a : Rope) (rest : List Rope) : List Rope :=
    match rest {
        List.empty => List.cons a List.empty,
        List.cons b more => List.cons (Rope.concat a b) (rope_merge_pairs more)
    }

// ── UTF-8 boundaries ──────────────────────────────────────────────────────

/// The offsets land on UTF-8 character boundaries -- the byte is ASCII, a
/// lead byte, or one past the last byte (which IS a boundary: an edit at the
/// very end of the text appends).
pub def Rope.char_start (r : Rope) (off : I64) : Bool :=
    let b := Rope.bytes r in
    if I64.beq off b
    then true
    else Rope.byte_is_boundary r off

/// Is the byte AT `off` a character START (ASCII or a lead byte)?
def Rope.byte_is_boundary (r : Rope) (off : I64) : Bool :=
    match String.get (Rope.slice r off 4) 0 {
        Option.none => false,
        Option.some b => rope_is_boundary_byte b
    }

/// The byte AT `off`, or `none` when `off` is outside the rope. One
/// descent and one byte read -- the primitive every text motion in
/// `commands.mo` walks with, because a `String.get` needs a flat string
/// and the rope must not flatten for the sake of one byte.
pub def Rope.byte_at (r : Rope) (off : I64) : Option U8 :=
    match String.get (Rope.slice r off 1) 0 {
        Option.some b => Option.some b,
        Option.none => Option.none
    }

/// The rope's byte count, the bound every motion clamps to.
pub def Rope.end_offset (r : Rope) : I64 := Rope.bytes r

// ── Splitting, replacing, rebalancing ────────────────────────────────────


/// Split the rope at byte offset `off` into `(before, after)`.
///
/// `off` must be a character boundary -- `Rope.split_at` never splits a
/// UTF-8 sequence, so a caller handing it an arbitrary offset must first
/// check the boundary the way `transaction.mo` does. An `off` outside
/// `[0, bytes]` clamps to the nearer end rather than failing: splitting at
/// 0 is `(empty, whole)` and at `bytes` is `(whole, empty)`, which is what
/// a `replace` at either end of a document needs.
pub def Rope.split_at (r : Rope) (off : I64) : Pair Rope Rope :=
    let b := Rope.bytes r in
    if Bool.not (0 < off)
    then Pair.pair (Rope.leaf "") r
    else if Bool.not (off < b)
    then Pair.pair r (Rope.leaf "")
    else Rope.split_within r off

/// The interior split: `0 < off < bytes`, so the tree descends to the leaf
/// holding the boundary and slices it. Both halves keep the shared leaves
/// outside the boundary, which is the persistence win -- a split at the
/// viewport edge allocates only the path it walks.
def Rope.split_within (r : Rope) (off : I64) : Pair Rope Rope :=
    match r {
        Rope.leaf t =>
            Pair.pair (Rope.leaf (String.slice t 0 off)) (Rope.leaf (String.drop off t)),
        Rope.node l rt _ _ _ =>
            let lb := Rope.bytes l in
            if off < lb
            then match Rope.split_within l off {
                Pair.pair cl cr => Pair.pair cl (Rope.concat cr rt)
            }
            else match Rope.split_within rt (off - lb) {
                Pair.pair cl cr => Pair.pair (Rope.concat l cl) cr
            }
    }

/// Replace bytes `[start, stop)` of the OLD text with `text`: the rope over
/// `before ++ text ++ after`. A pure rebuild -- the unchanged prefix and
/// suffix keep their leaves, the edit itself allocates one leaf.
///
/// The boundary rule is the caller's (a `Change` that lands inside a
/// multi-byte sequence is rejected by `transaction.mo`, per the plan's
/// UTF-8-offsets risk), so `String.drop` answering `""` on a bad boundary is
/// never reached with a bad boundary.
pub def Rope.replace (r : Rope) (start : I64) (stop : I64) (text : String) : Rope :=
    let b := Rope.bytes r in
    let lo := max_i64 (min_i64 start b) 0 in
    let hi := max_i64 (min_i64 stop b) lo in
    match Rope.split_at r hi {
        Pair.pair _ after => match Rope.split_at r lo {
            Pair.pair before _ => Rope.concat (Rope.concat before (Rope.leaf text)) after
        }
    }

/// Count the leaves, the measure `Rope.balance` compares depth against.
pub def Rope.leaf_count (r : Rope) : I64 :=
    match r {
        Rope.leaf _ => 1,
        Rope.node l rt _ _ _ => Rope.leaf_count l + Rope.leaf_count rt
    }

/// The depth above which a rope is worth rebuilding: about twice the log of
/// its leaf count. A skewed rope (repeated one-sided `replace`s) grows a
/// level per edit; this bound catches it while the rebuild is still cheap.
pub def Rope.depth_limit (leaves : I64) : I64 :=
    2 * (rope_log2 (max_i64 leaves 2)) + 1

/// floor(log2 n) for n > 0, by halving.
#[terminating]
def rope_log2 (n : I64) : I64 :=
    if n < 2 then 0 else 1 + rope_log2 (n / 2)

/// Whether the rope is deeper than `Rope.depth_limit` of its own leaf count
/// -- the test `Rope.balance` makes. `pub` because the test suite pins it.
pub def Rope.needs_balance (r : Rope) : Bool :=
    Rope.depth r > Rope.depth_limit (Rope.leaf_count r)

/// Rebuild a skewed rope into the balanced bottom-up shape, or leave it
/// alone when it is within `Rope.depth_limit`. Flattening is O(bytes) --
/// one `Rope.slice` per leaf -- so it runs only when the depth test says
/// to, never per edit.
pub def Rope.balance (r : Rope) : Rope :=
    if Rope.needs_balance r
    then Rope.from_leaf_texts (Rope.leaf_texts r)
    else r

/// Every leaf's text, left to right.
#[terminating]
pub def Rope.leaf_texts (r : Rope) : List String :=
    match r {
        Rope.leaf t => List.cons t List.empty,
        Rope.node l rt _ _ _ => List.append (Rope.leaf_texts l) (Rope.leaf_texts rt)
    }

// ── Lines ───────────────────────────────────────────────────────────────

/// The byte offset of line `line`'s first byte (line 0 is offset 0; every
/// `\n` starts a new line). The descent subtracts cached `newlines`, so the
/// walk is O(depth + leaf), never a full scan -- the whole point of the
/// newline cache. A `line` past the end clamps to the last line's start,
/// the same total-input rule `toolkit::text`'s cursor scan states.
pub def Rope.line_start (r : Rope) (line : I64) : I64 :=
    if Bool.not (0 < line)
    then 0
    else Rope.line_start_go r (min_i64 line (Rope.newlines r)) 0

def Rope.line_start_go (r : Rope) (line : I64) (before : I64) : I64 :=
    match r {
        Rope.leaf t => Rope.line_scan t 0 (String.length t) line,
        Rope.node l rt _ _ _ =>
            let ln := Rope.newlines l in
            if line < ln
            then Rope.line_start_go l line before
            else Rope.line_start_go rt (line - ln) (before + Rope.bytes l)
    }

/// Scan a leaf for the `line`th `\n` and return the byte after it. The leaf
/// is at most a few KiB, so a byte loop here is the cheap case; the tree
/// above it already did the logarithmic work.
#[terminating]
def Rope.line_scan (t : String) (i : I64) (stop : I64) (line : I64) : I64 :=
    if Bool.not (i < stop)
    then stop
    else
        match String.get t i {
            Option.none => stop,
            Option.some b => Rope.line_step t i stop line b
        }

/// One byte of the line scan: a `\n` with no line left to cross is the
/// answer; a `\n` that still has lines to cross steps past it; anything
/// else just moves on.
#[terminating]
def Rope.line_step (t : String) (i : I64) (stop : I64) (line : I64) (b : U8) : I64 :=
    if Bool.not (U8.beq b 10u8)
    then Rope.line_scan t (i + 1) stop line
    else if I64.beq line 1
    then i + 1
    else Rope.line_scan t (i + 1) stop (line - 1)
