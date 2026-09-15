/// Position tracking utilities for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lib::types {LocatedSpan, Location, mk}
use lib::parser::combinators {utf8_char_width}

/// Create a new LocatedSpan starting at offset 0, line 1, column 1
#[partial]
def new_span (s : String) : LocatedSpan :=
	LocatedSpan.mk s (Location.mk 0 1 1)

/// Extract the location from a LocatedSpan
#[partial]
def span_location (span : LocatedSpan) : Location :=
	match span {
		mk frag loc => loc
	}

/// Extract the fragment string from a LocatedSpan
#[partial]
def span_fragment (span : LocatedSpan) : String :=
	match span {
		mk frag loc => frag
	}

// --- Line/column scanning ---
//
// The Rust reference interpreter (core_eval.rs) has no tail-call
// optimization: a single recursive call chain longer than roughly
// 1000-1500 frames overflows the stack, even inside the test runner's
// dedicated 64MB thread (confirmed by direct measurement — a bare
// self-recursive countdown from 1500 crashes, from 1000 doesn't; this
// is a pre-existing, systemic limitation of the interpreter itself, not
// specific to any one function — `lang.parser.combinators.take_while`,
// used throughout the whole grammar, crashes the exact same way if
// asked to scan an entire large file in one call, though nothing in
// normal parsing ever does that since every real token/construct is far
// shorter than 1000 characters).
//
// `lang/json.mo` alone is ~37,000 characters, so recovering one
// line:column from it (as `location_of_remaining` does when rendering a
// parse error) means accounting for every character of the consumed
// prefix. This used to be a one-character-at-a-time walk, arranged as a
// divide-and-conquer split purely to keep the recursion DEPTH off the
// interpreter's ~1000-1500 frame ceiling -- the total work was always
// O(n); depth was the thing that crashed.
//
// It is now two native scans and no recursion at all. Splitting,
// combining, and the threshold that chose between them are gone with it,
// since `String.count_newlines`/`String.trailing_chars`
// (`init/string.mo`) do the whole accounting in one pass each without
// building a frame per character. `line_col_scan_direct` below survives
// as the REFERENCE implementation the tests check the natives against.
struct LineColScan {
	newlines : I64,
	/// Characters since the last newline -- or, if there is no newline at
	/// all, the character count of the whole string.
	trailing : I64,
}

/// The character-at-a-time reference implementation, kept ONLY so the
/// tests have something independent to check `line_col_scan` against.
///
/// It decides "what is a character" a different way than the natives do:
/// it steps by `utf8_char_width`, reading each LEAD byte's own encoding
/// rule, where the natives count bytes that are not continuation bytes.
/// Those two definitions agreeing is exactly the property worth testing,
/// so this must never be reimplemented in terms of them --
/// `test_line_col_scan_matches_reference` is the check.
///
/// Not for production use: one frame per character, which past a few
/// hundred characters is past the interpreter's recursion ceiling. That
/// ceiling is why the old `dc_threshold` existed.
#[partial]
def line_col_scan_direct (s : String) (nl : I64) (trailing : I64) : LineColScan :=
	if String.is_empty s
	then { newlines := nl, trailing := trailing }
	else
		let width : I64 := utf8_char_width s in
		let ch : String := String.slice s 0 width in
		let rest : String := String.drop width s in
		if String.beq "\n" ch
		then line_col_scan_direct rest (I64.add nl 1) 0
		else line_col_scan_direct rest nl (I64.add trailing 1)

/// Scan `s` for the newline/trailing-column bookkeeping `advance_location`
/// needs. Two native passes over the bytes: no recursion, no allocation,
/// and no length limit.
#[partial]
def line_col_scan (s : String) : LineColScan :=
	let len : I64 := String.length s in
	{ newlines := String.count_newlines s len,
	  trailing := String.trailing_chars s len }

/// A byte in the 0x80-0xBF (128-191) range is a UTF-8 *continuation*
/// byte — never a character on its own, since it is the middle of a
/// multi-byte sequence (see `utf8_char_width`'s own doc comment,
/// lang/parser/combinators.mo, for the encoding rule this checks
/// against).
///
/// This is the executable statement of the rule `String.trailing_chars`
/// counts by on BOTH runtimes -- `core/src/core_native.rs` and
/// `runtime/src/runtime.c` each test `(b & 0xC0) != 0x80`, which is
/// this same range. `test_trailing_chars_matches_continuation_byte_rule`
/// holds the native to it directly, rather than leaving the agreement to
/// a comment.
#[partial]
def is_utf8_continuation_byte (byte : U8) : Bool :=
	U8.gt byte 127u8 && U8.lt byte 192u8

/// Advance a location past the given consumed string. Safe for a
/// consumed prefix of any size — `line_col_scan` is two native passes,
/// with no per-character recursion to overflow. `consumed`'s own byte
/// length determines the new `offset` (matching `String.slice`/
/// `String.drop`'s byte semantics).
#[partial]
def advance_location (loc : Location) (consumed : String) : Location :=
	match loc {
		mk off line col =>
			let byte_len : I64 := String.length consumed in
			let new_off : I64 := I64.add off byte_len in
			match line_col_scan consumed {
				mk newlines trailing =>
					if I64.beq newlines 0
					then Location.mk new_off line (I64.add col trailing)
					else Location.mk new_off (I64.add line newlines) (I64.add 1 trailing)
			}
	}

/// Consume n bytes from a LocatedSpan, advancing the location
#[partial]
def consume_span (span : LocatedSpan) (n : I64) : LocatedSpan :=
	match span {
		mk frag loc =>
			let consumed : String := String.slice frag 0 n in
			let rest : String := String.drop n frag in
			let new_loc : Location := advance_location loc consumed in
			LocatedSpan.mk rest new_loc
	}

/// Compute the `Location` where `remaining` begins within `original` —
/// how this parser surfaces error positions: rather than threading a
/// `LocatedSpan` through every one of ~450 grammar functions (the Rust
/// reference's nom-locate approach, core/src/parser/locate.rs), every
/// `ParseError` already carries the input remaining right at the point
/// of failure (see `ParseError`'s own doc comment, lang/parser/core.mo);
/// this converts that back into a `Location` by diffing against the
/// original full source text, computed once on demand when rendering a
/// diagnostic, not threaded through every parse step. `remaining` is
/// always a suffix of `original` at a valid UTF-8 boundary (every
/// scanner in this parser now steps by `utf8_char_width`, never a raw
/// byte), so the byte-length diff below always lands on one too.
#[partial]
def location_of_remaining (original : String) (remaining : String) : Location :=
	location_of_remaining_len original (String.length remaining)

/// The same arithmetic from a recorded remaining-input LENGTH rather
/// than the remainder string itself, which is what a `ParseSpan` stores
/// (see `ParseSpan`'s own doc comment, lang/types.mo, for why the
/// parser records lengths and not absolute offsets). `decls_parser`'s
/// located twin goes through here: the parser already recorded where
/// each declaration began, so the position is a projection over that
/// span rather than a second parse that re-derives it.
#[partial]
def location_of_remaining_len (original : String) (remaining_len : I64) : Location :=
	let consumed_len : I64 := String.length original - remaining_len in
	let consumed : String := String.slice original 0 consumed_len in
	advance_location (Location.mk 0 1 1) consumed


// --- Bulk offset resolution ------------------------------------------
//
// `location_of_remaining_len` above answers ONE position by scanning the
// whole consumed prefix. Per top-level declaration that is fine -- a few
// hundred calls per file. Per TERM it is quadratic: tens of thousands of
// calls, each scanning up to the whole file.
//
// So resolve every position in a single pass instead. The parser records
// spans as remaining-input lengths, and a pre-order left-to-right walk of
// the parse tree visits nodes in non-decreasing absolute offset -- so the
// offsets arrive already sorted and nothing needs a sort (`std/list.mo`
// has none) or an index (there is no `Array`, and no `Hashable I64` for a
// map keyed by offset).
//
// This walks the OFFSETS, not the characters. An earlier version walked
// every character of the file, threading a running `Location`, with a
// divide-and-conquer split to keep the recursion depth off the
// interpreter's ~1000-1500 frame ceiling. It was correct and it was 88%
// of what locating every term costs: measured by
// `bench/parser_locate_cost.mo` on `lang/types.mo` (73000 bytes, 1469
// spans), 652ms of a 739ms overhead, about 8.9us per character. The cost
// was not the loop's shape -- per character it called `utf8_char_width`,
// which is `match String.get s 0`, and `string_get` returns a
// `Value::Con`, so the walk allocated an `Option` PER CHARACTER.
//
// Only 1469 of those 73000 characters are positions anyone asked for.
// The walk existed solely to count newlines and columns in between, so
// counting is what got pushed into a native: one step per SPAN, each
// step asking `String.count_newlines`/`String.trailing_chars`
// (`init/string.mo`) about the segment since the previous span. Total
// bytes scanned is still O(n) -- every byte falls in exactly one
// segment -- but the interpreted step count drops by ~50x.
//
// Two things here are load-bearing rather than stylistic, and both are
// about the COMPILED runtime, where this file also runs:
//   * the natives take a LENGTH, and nothing is sliced. Compiled
//     `monad_string_slice` does a `strlen` plus a malloc plus a memcpy
//     per call (`runtime/src/runtime.c`), so a slice per span would be
//     quadratic -- and note the old per-character `String.slice s 0
//     width` was exactly that, quadratic, on every compiled build.
//   * `String.length source` is taken ONCE, outside the walk, for the
//     same reason: compiled, it is `strlen`.
// The recursion is one frame per offset with an accumulator, the same
// shape (and the same scale) `merge_asc` below already relies on.

/// Advance `loc` across the first `len` bytes of `rest`, with two native
/// scans rather than a per-character walk.
///
/// The two cases are the whole of the line:column rule. If the range
/// holds a newline, the column restarts and `trailing_chars` is already
/// measured from the last one; if it holds none, the range is all
/// "trailing" and the column simply grows by it. That is the same split
/// `advance_location` makes over `LineColScan`, which is why the field
/// there is also called `trailing`.
///
/// CHARACTERS, not bytes, for the column -- `String.trailing_chars` skips
/// UTF-8 continuation bytes, which is what
/// `test_resolve_offsets_column_counts_characters` pins down. The byte
/// `offset` still advances by `len`, since offsets are byte-measured.
#[partial]
def resolve_advance (rest : String) (len : I64) (loc : Location) : Location :=
    let nl : I64 := String.count_newlines rest len in
    let trail : I64 := String.trailing_chars rest len in
    if I64.gt nl 0
    then Location.mk (I64.add loc.offset len) (I64.add loc.line nl) (I64.add trail 1)
    else Location.mk (I64.add loc.offset len) loc.line (I64.add loc.column trail)

/// Resolve each offset in turn, carrying the remaining source and the
/// position it starts at.
///
/// `limit` is the file's byte length, passed in because computing it is
/// `strlen` on the compiled runtime and it does not change. Clamping each
/// offset to it is what gives offsets at or past end-of-file the file's
/// final position rather than dropping them -- end-of-input is a real
/// position, and a dropped entry would leave a term with no location for
/// no visible reason. The pair keeps the offset the CALLER asked for as
/// its key, not the clamped one, so a lookup by the original offset still
/// finds it.
///
/// A negative step cannot happen for ascending input, but is clamped to
/// zero rather than trusted: a descending pair would otherwise hand the
/// natives a negative length, and `resolve_offsets_in_file` sorts
/// precisely because callers have been wrong about ascendingness before.
///
/// **The reported position and the carried cursor are not the same byte,
/// and that is the point.** `at_off` answers at exactly the byte asked
/// for. The cursor advances to the next character BOUNDARY at or after it
/// (`boundary_at_or_after`), because `String.drop` at a non-boundary
/// returns the EMPTY string on the Rust host -- `SharedStr::subslice`
/// falls back to empty rather than splitting a character. Dropping by the
/// raw step would therefore hand the rest of the walk an empty remainder,
/// and every offset behind the offending one would resolve against it:
/// `count_newlines`/`trailing_chars` both answer 0, so `line` and `column`
/// FREEZE while `offset` keeps climbing. One bad offset, every later
/// position silently wrong.
///
/// It also kept the two runtimes from agreeing, which is the shape
/// `runtime.c`'s own comment warns reads like a codegen bug and is not
/// one: compiled, `monad_string_drop` is `return s + n` with no boundary
/// check, so a self-compiled binary kept walking the real remainder while
/// the host sat on `""`. Advancing on boundaries only makes both runtimes
/// take the same step.
///
/// A real span never holds a non-boundary offset -- every scanner in the
/// parser steps by `utf8_char_width` or by byte predicates no UTF-8 byte
/// satisfies -- so this is a latent case, not a live one. It is still the
/// case the file claims to handle, and
/// `test_resolve_offsets_mid_character_batch` is what holds it to the
/// claim for a BATCH rather than for one offset in isolation.
///
/// On the normal path `safe` equals `step` and `loc1` is `at_off`, so the
/// boundary handling costs one `String.get` per OFFSET (not per character,
/// which is the cost this rewrite removed) and nothing else.
#[partial]
def resolve_walk (rest : String) (loc : Location) (limit : I64) (offsets : List I64)
                 (out : List (Pair I64 Location)) : List (Pair I64 Location) :=
    match offsets {
        List.empty => out,
        List.cons off more =>
            let target : I64 := if I64.gt off limit then limit else off in
            let raw : I64 := I64.sub target loc.offset in
            let step : I64 := if I64.lt raw 0 then 0 else raw in
            // What this offset resolves to: the byte the caller asked for.
            let at_off : Location := resolve_advance rest step loc in
            // Where the walk stands afterwards: the next boundary at or
            // after it, so the `String.drop` below never splits a character.
            let safe : I64 := boundary_at_or_after rest step in
            let loc1 : Location :=
                if I64.beq safe step then at_off else resolve_advance rest safe loc in
            resolve_walk (String.drop safe rest) loc1 limit more
                (List.cons (Pair.pair off at_off) out),
    }

/// The first UTF-8 character boundary at or after byte `i` in `s`.
///
/// Nudges at most 3 times -- the longest a UTF-8 sequence runs past its
/// lead byte -- since only a continuation byte (0x80-0xBF) is a
/// non-boundary. `String.get` past the end answers `Option.none`, which is
/// already a boundary (end-of-input), so `i` stands.
///
/// This is the `safe_split_offset` the divide-and-conquer scanner used to
/// need to keep a split off the middle of a character. The split is gone;
/// the requirement is not, because `resolve_walk` still has to hand
/// `String.drop` a boundary.
#[partial]
def boundary_at_or_after (s : String) (i : I64) : I64 :=
    match String.get s i {
        Option.some byte =>
            if is_utf8_continuation_byte byte
            then boundary_at_or_after s (I64.add i 1)
            else i,
        Option.none => i,
    }

/// Resolve `offsets` (ascending, absolute byte offsets) against `source`.
///
/// Offsets at or past end-of-file resolve to the file's final position
/// rather than being dropped: end-of-input is a real position, and a
/// dropped entry would leave a term with no location for no visible
/// reason.
/// The single-pass walk consumes `pending` from the head and never goes
/// back, so it REQUIRES ascending input. This used to check `is_ascending`
/// and fall back to a per-offset rescan of the whole file when it failed --
/// "the correct-but-quadratic path. Slow beats wrong." Correct, and a trap:
/// the fallback is silent, and callers do not in fact deliver ascending
/// offsets.
///
/// `build_loc_table` (`lang/parser.mo`) collects spans in pre-order and
/// argued that pre-order IS ascending. It is not, and the counterexample is
/// every infix expression in the language: `a + b` parses to
/// `app (app (+) a) b`, so a pre-order walk visits the operator node --
/// whose span starts at the `+` -- BEFORE the operand `a` that precedes it
/// in the source. Measured with `bench/parser_located.mo`:
///
///   init/id.mo      675 bytes,   30 spans  ascending YES   27ms ->    36ms
///   lang/types.mo 73000 bytes, 1469 spans  ascending NO   1753ms -> 287766ms
///
/// 164x, with the first inversion at span index 244. That fallback is what
/// made a `--verbose` self-compile WITHOUT `--release` take 28035824ms
/// (7h48m) against 275424ms with it, ~99.4% of it in `with_located_decls`.
/// Debug info is on by default, so that was the default `monad compile`.
///
/// So sort, and make the invariant hold rather than detecting that it does
/// not. `is_ascending` is kept as the cheap skip for input that already is
/// (the small-file case above) and as the executable statement of what the
/// walk needs. The quadratic fallback is gone: an unreachable-by-hope slow
/// path that nothing exercises is how this hid for as long as it did.
///
/// Sorting changes the ORDER of the returned pairs, not their content. The
/// only consumer (`build_loc_table` -> `rekey_by_rem`) folds them into a
/// `HashMap` keyed by offset, and this file's own tests look results up by
/// offset via `lookup_resolved`, so no caller observes the order.
///
/// Offsets at or past end-of-file resolve to the file's final position
/// rather than being dropped: end-of-input is a real position, and a
/// dropped entry would leave a term with no location for no visible
/// reason.
#[partial]
def resolve_offsets_in_file (source : String) (offsets : List I64) : List (Pair I64 Location) :=
    if is_ascending offsets
    then resolve_ascending source offsets
    else resolve_ascending source (sort_offsets_asc offsets)

/// Merge sort over absolute byte offsets. Local to this file and
/// distinctively named on purpose: the self-hosted global name table is not
/// module-scoped (AGENTS.md item 18), and there is no `List.sort` in `std/`
/// to reuse.
///
/// Accumulator-passing in `merge_asc`, not `List.cons x (merge rest)`: the
/// merge is the one part whose recursion depth is O(n) rather than O(log n),
/// and `lang/codegen/decls.mo`'s own note explains why depth is expensive
/// here beyond the stack (Boehm marks conservatively from the whole stack on
/// every collection, so depth is paid again per collection).
#[partial]
def sort_offsets_asc (xs : List I64) : List I64 :=
    match xs {
        List.empty => xs,
        List.cons _ rest =>
            match rest {
                // One element is already sorted; this is also the base case
                // that stops the split recursion.
                List.empty => xs,
                List.cons _ _ =>
                    match split_alternating xs List.empty List.empty true {
                        Pair.pair l r =>
                            merge_asc (sort_offsets_asc l) (sort_offsets_asc r),
                    },
            },
    }

/// Deal alternately into two halves. Both come out reversed, which a sort
/// does not care about, and dealing avoids walking the list twice to find a
/// midpoint.
#[partial]
def split_alternating (xs : List I64) (l : List I64) (r : List I64) (to_left : Bool) : Pair (List I64) (List I64) :=
    match xs {
        List.empty => Pair.pair l r,
        List.cons x rest =>
            if to_left
            then split_alternating rest (List.cons x l) r false
            else split_alternating rest l (List.cons x r) true,
    }

#[partial]
def merge_asc (a : List I64) (b : List I64) : List I64 :=
    reverse_offsets (merge_asc_go a b List.empty) List.empty

/// Takes from `a` on a tie, so equal offsets keep their relative order --
/// duplicates are real (two spans can start at the same byte) and both must
/// survive to be keyed.
#[partial]
def merge_asc_go (a : List I64) (b : List I64) (acc : List I64) : List I64 :=
    match a {
        List.empty => reverse_offsets b acc,
        List.cons x xs =>
            match b {
                List.empty => reverse_offsets a acc,
                List.cons y ys =>
                    if I64.lt y x
                    then merge_asc_go a ys (List.cons y acc)
                    else merge_asc_go xs b (List.cons x acc),
            },
    }

/// `reverse_offsets xs acc` is `List.reverse xs ++ acc` -- both the final
/// flip and the "one side ran out, tip the rest on" step want exactly this.
#[partial]
def reverse_offsets (xs : List I64) (acc : List I64) : List I64 :=
    match xs {
        List.empty => acc,
        List.cons x rest => reverse_offsets rest (List.cons x acc),
    }

#[partial]
def is_ascending (offsets : List I64) : Bool := match offsets {
    List.empty => true,
    List.cons a rest => is_ascending_from a rest,
}

#[partial]
def is_ascending_from (prev : I64) (offsets : List I64) : Bool := match offsets {
    List.empty => true,
    List.cons b rest => if I64.lt b prev then false else is_ascending_from b rest,
}

/// `String.length` is taken ONCE here rather than inside `resolve_walk`:
/// it is `strlen` on the compiled runtime, so per-offset it would put the
/// quadratic term back that this whole rewrite removed.
///
/// `resolve_walk` accumulates in reverse, hence the reverse at the end --
/// the same accumulator-passing shape, and for the same
/// recursion-depth reason, as `merge_asc` above.
#[partial]
def resolve_ascending (source : String) (offsets : List I64) : List (Pair I64 Location) :=
    list_reverse_pairs
        (resolve_walk source (Location.mk 0 1 1) (String.length source) offsets List.empty)
        List.empty

#[partial]
def list_reverse_pairs (xs : List (Pair I64 Location)) (acc : List (Pair I64 Location)) : List (Pair I64 Location) :=
    match xs {
        List.empty => acc,
        List.cons x rest => list_reverse_pairs rest (List.cons x acc),
    }


// --- Tests -----------------------------------------------------------
//
// The oracle for bulk resolution is the single-offset path it replaces:
// for any offset, `resolve_offsets_in_file` must return exactly what
// `location_of_remaining_len` would have. That is a real equivalence
// check, not a restatement of the implementation.

/// Look one offset up in a resolved table.
#[partial]
def lookup_resolved (pairs : List (Pair I64 Location)) (off : I64) : Option Location :=
    match pairs {
        List.empty => Option.none,
        List.cons p rest => lookup_resolved_step p rest off,
    }

#[partial]
def lookup_resolved_step (p : Pair I64 Location) (rest : List (Pair I64 Location)) (off : I64) : Option Location :=
    match p {
        Pair.pair k v => if I64.beq k off then Option.some v else lookup_resolved rest off,
    }

/// `location_of_remaining_len` takes a REMAINING length; the bulk path
/// takes an absolute offset. This converts, so both sides of the
/// comparison below describe the same point.
#[partial]
def single_location_at (source : String) (off : I64) : Location :=
    location_of_remaining_len source (I64.sub (String.length source) off)

#[partial]
def agrees_at (source : String) (pairs : List (Pair I64 Location)) (off : I64) : Bool :=
    match lookup_resolved pairs off {
        Option.some got => location_beq got (single_location_at source off),
        Option.none => false,
    }

#[partial]
def location_beq (a : Location) (b : Location) : Bool :=
    I64.beq a.offset b.offset && I64.beq a.line b.line && I64.beq a.column b.column

#[partial]
def agrees_at_all (source : String) (pairs : List (Pair I64 Location)) (offs : List I64) : Bool :=
    match offs {
        List.empty => true,
        List.cons o rest =>
            if agrees_at source pairs o then agrees_at_all source pairs rest else false,
    }

/// `line_col_scan` (two natives) must agree with `line_col_scan_direct`
/// (one frame per character, stepping by `utf8_char_width`) on every
/// shape that distinguishes them.
///
/// This is the oracle the native conversion rests on, so the cases are
/// chosen rather than arbitrary: empty; no newline at all (trailing is
/// then the whole count); a trailing newline (trailing resets to 0); a
/// leading newline; consecutive newlines (an empty line contributes a
/// line but no column); multi-byte characters both before and after the
/// last newline, which is where a byte count and a character count come
/// apart. Kept under a few hundred characters because the reference
/// implementation cannot survive more -- which is the whole reason it is
/// not the production one.
#[test]
def test_line_col_scan_matches_reference : Bool :=
    scan_agrees ""
        && scan_agrees "abc"
        && scan_agrees "abc\n"
        && scan_agrees "\nabc"
        && scan_agrees "a\n\nb"
        && scan_agrees "\n"
        && scan_agrees "// — x"
        && scan_agrees "// — x\ndef y — z"
        && scan_agrees "—\n—\n—"
        && scan_agrees "def a : I64 := 1\ndef b : I64 := 2\n\ndef c : I64 := 3\n"

#[partial]
def scan_agrees (s : String) : Bool :=
    match line_col_scan s {
        mk nl trail =>
            match line_col_scan_direct s 0 0 {
                mk rnl rtrail => I64.beq nl rnl && I64.beq trail rtrail,
            },
    }

/// `String.trailing_chars` must count exactly the bytes that
/// `is_utf8_continuation_byte` rejects, since that is the rule its two
/// implementations (Rust host and C runtime) are each written to.
///
/// Checked against a count derived from the predicate itself rather than
/// against another scanner, so this pins the native to the STATED rule
/// and not merely to a second implementation that could share a mistake.
#[test]
def test_trailing_chars_matches_continuation_byte_rule : Bool :=
    // Literal characters, NOT a `\u{00e9}` escape: the self-hosted string
    // parser deliberately does not support unicode escapes (see
    // lang/parser/string.mo's own doc comment), so one here truncates the
    // self-hosted parse of this whole file while `monad-rs check` still
    // reports it clean -- AGENTS.md item 40's failure shape exactly.
    let s : String := "a—béc" in
    // 8 bytes, 5 characters. Asserted, not just intended: without this
    // the test would still pass on an ASCII fixture, where counting
    // bytes and counting characters are the same thing and a
    // byte-counting native would go unnoticed.
    I64.beq (String.length s) 8
        && I64.beq (count_non_continuation s 0 0) 5
        && I64.beq (String.trailing_chars s (String.length s))
                   (count_non_continuation s 0 0)

/// Characters in `s` from byte `i` on, counting a byte iff it is not a
/// UTF-8 continuation byte. Deliberately byte-indexed and deliberately
/// NOT newline-aware: `s` above has no newline, so this is the whole
/// count, which is what `trailing_chars` returns in that case.
#[partial]
def count_non_continuation (s : String) (i : I64) (acc : I64) : I64 :=
    match String.get s i {
        Option.none => acc,
        Option.some byte =>
            count_non_continuation s (I64.add i 1)
                (if is_utf8_continuation_byte byte then acc else I64.add acc 1),
    }

/// Every offset in a multi-line source must resolve exactly as the
/// single-offset scanner would.
#[test]
def test_resolve_offsets_agrees_with_single : Bool :=
    let src : String := "def a : I64 := 1\ndef b : I64 := 2\n\ndef c : I64 := 3\n" in
    let offs : List I64 := [0, 4, 16, 17, 21, 34, 35, 39] in
    agrees_at_all src (resolve_offsets_in_file src offs) offs

/// The multi-byte case, which is where a byte-offset/character-column mix-up
/// shows up: the em dash occupies bytes 3-5 but advances the column by one.
///
/// Every offset here is a real character BOUNDARY, which is the only kind a
/// span ever holds -- every scanner in the parser steps by
/// `utf8_char_width` or by byte predicates that no UTF-8 lead or
/// continuation byte satisfies. For the non-boundary case, which the two
/// paths used to disagree about, see
/// `test_resolve_offsets_mid_character_offset` below.
#[test]
def test_resolve_offsets_agrees_over_utf8 : Bool :=
    let src : String := "// — x\ndef y : I64 := 1\n" in
    let offs : List I64 := [0, 3, 6, 7, 9, 12] in
    agrees_at_all src (resolve_offsets_in_file src offs) offs

/// The em dash advances the column by one, not three -- pinned directly
/// rather than only via agreement, since agreement would also hold if both
/// paths were wrong the same way.
#[test]
def test_resolve_offsets_column_counts_characters : Bool :=
    let src : String := "// — x\ndef y : I64 := 1\n" in
    match lookup_resolved (resolve_offsets_in_file src [7]) 7 {
        // `/`, `/`, ` `, `—`, ` ` are 5 characters (7 bytes), so `x` is at
        // column 6 -- not the byte-derived 8.
        Option.some loc => I64.beq loc.line 1 && I64.beq loc.column 6 && I64.beq loc.offset 7,
        Option.none => false,
    }

/// An offset landing INSIDE a multi-byte character. A real span never
/// holds one -- every scanner steps by `utf8_char_width` -- but a
/// synthesized or corrupted offset can, so this pins what happens rather
/// than leaving it to chance.
///
/// Byte 4 is the middle of the 3-byte em dash at bytes 3-5. The walk stops
/// exactly at the byte asked for, and the partial character counts as one
/// (its lead byte is not a continuation byte), giving column 5 and
/// `offset` 4 -- the offset requested, not the boundary after it.
///
/// This is deliberately NOT an `agrees_at` check, and that is the
/// interesting part. `single_location_at` cannot answer here at all: it
/// works by `String.slice source 0 off`, and a slice that would split a
/// character yields the EMPTY string (`string_slice`'s
/// `get(start..end).unwrap_or("")` semantics, kept by
/// `SharedStr::subslice`), so it collapses to the zero location 0/1/1 for
/// any non-boundary offset. Verified, not assumed. The two paths differed
/// here before this rewrite too -- the old character walk consumed such an
/// offset at the NEXT boundary -- so the change is which meaningless
/// answer the bulk path gives, and it now gives the predictable one.
///
/// One offset in isolation is NOT enough, though: see
/// `test_resolve_offsets_mid_character_batch` just below, which is the
/// half of this case that was actually broken.
#[test]
def test_resolve_offsets_mid_character_offset : Bool :=
    match lookup_resolved (resolve_offsets_in_file "// — x\ndef y : I64 := 1\n" [4]) 4 {
        Option.some loc => I64.beq loc.line 1 && I64.beq loc.column 5 && I64.beq loc.offset 4,
        Option.none => false,
    }

/// A non-boundary offset must not disturb the offsets BEHIND it, which is
/// the part a single-offset test cannot see.
///
/// Offset 10 is the `e` of `def` on line 2, column 2. Asking for it alone
/// and asking for it after the mid-character offset 4 must give the same
/// answer -- and asserted absolutely, not just for agreement, so that two
/// equally wrong answers cannot pass.
///
/// This failed before `resolve_walk` advanced its cursor on boundaries:
/// `String.drop 4` at the middle of the em dash returned `""` on the Rust
/// host, so offset 10 resolved against an empty remainder and read
/// `line 1 col 5` -- the position frozen at offset 4, with only the byte
/// `offset` still climbing. Every offset after the first bad one was
/// affected, not just the bad one.
#[test]
def test_resolve_offsets_mid_character_batch : Bool :=
    let src : String := "// — x\ndef y : I64 := 1\n" in
    match lookup_resolved (resolve_offsets_in_file src [4, 10]) 10 {
        Option.some loc =>
            I64.beq loc.line 2 && I64.beq loc.column 2 && I64.beq loc.offset 10
                && loc_eq_opt (lookup_resolved (resolve_offsets_in_file src [10]) 10) loc,
        Option.none => false,
    }

/// `Option.some loc` equal to `expect` on all three fields; `Option.none`
/// is never equal, so a missing entry fails rather than passing vacuously.
#[partial]
def loc_eq_opt (got : Option Location) (expect : Location) : Bool :=
    match got {
        Option.some l =>
            I64.beq l.line expect.line
                && I64.beq l.column expect.column
                && I64.beq l.offset expect.offset,
        Option.none => false,
    }

/// Long enough (648 bytes, 12 identical lines) that a resolver getting
/// its line accounting wrong only some of the time would show up. The
/// offsets deliberately straddle line boundaries and land mid-line.
#[test]
def test_resolve_offsets_across_split : Bool :=
    let line : String := "def padding_definition_for_length : I64 := 1234567890\n" in
    let src : String := repeat_str line 12 in
    let offs : List I64 := [0, 54, 108, 300, 540, 594] in
    agrees_at_all src (resolve_offsets_in_file src offs) offs

#[partial]
def repeat_str (s : String) (n : I64) : String :=
    if I64.lt n 1 then "" else String.concat s (repeat_str s (n - 1))

/// A non-ascending list still resolves correctly -- via the slow path.
/// Without the guard this returned silently wrong positions for everything
/// after the first inversion.
#[test]
def test_resolve_offsets_unsorted_still_correct : Bool :=
    let src : String := "def a : I64 := 1\ndef b : I64 := 2\n\ndef c : I64 := 3\n" in
    let offs : List I64 := [34, 0, 17] in
    agrees_at_all src (resolve_offsets_in_file src offs) offs

/// An offset at or past end-of-file resolves to the final position rather
/// than vanishing from the table.
#[test]
def test_resolve_offsets_past_eof : Bool :=
    let src : String := "abc\n" in
    match lookup_resolved (resolve_offsets_in_file src [4, 99]) 99 {
        Option.some loc => I64.beq loc.line 2,
        Option.none => false,
    }
