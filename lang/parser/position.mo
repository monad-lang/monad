/// Position tracking utilities for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types {LocatedSpan, Location, mk}
use lang.parser.combinators {utf8_char_width}

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

// --- Divide-and-conquer line/column scanning ---
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
// `lang/json.mo` alone is ~37,000 characters, so a naive
// one-character-at-a-time linear scan over its full consumed prefix (as
// `location_of_remaining` needs to do to recover a line:column) crashes
// well before reaching the end. `LineColScan` fixes this by scanning
// via divide-and-conquer: split a chunk in half, scan each half
// independently (recursing further only on chunks still over a safe
// small threshold), then *combine* the two results — an associative,
// monoid-shaped operation, so the combining itself doesn't care how the
// splits were arranged. This keeps the recursion *depth* at O(log n)
// (~16 for a file this size) while the *total* work stays O(n) — depth
// is what the interpreter's stack can't afford, not total work.
struct LineColScan {
	newlines : I64,
	chars : I64,
	/// Characters since the last newline *within this chunk alone* — if
	/// this chunk has no newline of its own, the whole chunk is
	/// "trailing" (equal to `chars`).
	trailing : I64,
}

/// Combine two adjacent chunks' scans, left-to-right.
#[partial]
def combine_line_col_scan (left : LineColScan) (right : LineColScan) : LineColScan :=
	match left {
		mk l_nl l_chars l_trail =>
			match right {
				mk r_nl r_chars r_trail =>
					let trailing : I64 := if I64.gt r_nl 0 then r_trail else I64.add l_trail r_trail in
					{ newlines := I64.add l_nl r_nl, chars := I64.add l_chars r_chars, trailing := trailing }
			}
	}

/// Base case: scan a small chunk directly, one character at a time.
/// Only ever called on chunks already below `dc_threshold` (see
/// `line_col_scan`), so this stays well within the interpreter's real
/// recursion-depth ceiling.
#[partial]
def line_col_scan_direct (s : String) (nl : I64) (chars : I64) (trailing : I64) : LineColScan :=
	if String.is_empty s
	then { newlines := nl, chars := chars, trailing := trailing }
	else
		let width : I64 := utf8_char_width s in
		let ch : String := String.slice s 0 width in
		let rest : String := String.drop width s in
		if String.beq "\n" ch
		then line_col_scan_direct rest (I64.add nl 1) (I64.add chars 1) 0
		else line_col_scan_direct rest nl (I64.add chars 1) (I64.add trailing 1)

/// Byte length above which `line_col_scan` splits rather than scanning
/// directly — comfortably under the interpreter's ~1000-1500 frame
/// ceiling (a UTF-8 chunk of this many *bytes* has at most this many
/// characters, usually fewer), with margin for whatever's already on
/// the stack from the caller (`decls_parser_strict`'s own parse attempt,
/// `render_parse_error`'s own call chain).
def dc_threshold : I64 := 400

/// Scan `s` for newline/character/trailing-column bookkeeping via
/// divide-and-conquer. See this module's own doc comment above
/// (`LineColScan`) for why this can't just be a single linear scan.
#[partial]
def line_col_scan (s : String) : LineColScan :=
	if I64.lt (String.length s) dc_threshold
	then line_col_scan_direct s 0 0 0
	else
		let raw_mid : I64 := I64.div (String.length s) 2 in
		let mid : I64 := safe_split_offset s raw_mid in
		let left : String := String.slice s 0 mid in
		let right : String := String.drop mid s in
		combine_line_col_scan (line_col_scan left) (line_col_scan right)

/// A byte in the 0x80-0xBF (128-191) range is a UTF-8 *continuation*
/// byte — never a valid place to split a string, since it's the middle
/// of a multi-byte character (see `utf8_char_width`'s own doc comment,
/// lang/parser/combinators.mo, for the encoding rule this checks
/// against).
#[partial]
def is_utf8_continuation_byte (byte : U8) : Bool :=
	U8.gt byte 127u8 && U8.lt byte 192u8

/// Nudge `approx` forward (at most 3 times — the longest a UTF-8
/// sequence can be past its lead byte) until it lands on a real
/// character boundary, so `line_col_scan`'s divide-and-conquer split
/// never cuts a multi-byte character in half.
#[partial]
def safe_split_offset (s : String) (approx : I64) : I64 :=
	match String.get s approx {
		Option.some byte =>
			if is_utf8_continuation_byte byte
			then safe_split_offset s (I64.add approx 1)
			else approx,
		// Past the end of `s` (or `approx` already lands exactly on the
		// end) — `String.slice`/`String.drop` already clamp out-of-range
		// offsets safely, nothing further to adjust.
		Option.none => approx
	}

/// Advance a location past the given consumed string, using
/// `line_col_scan`'s divide-and-conquer scan rather than a linear pass —
/// safe for a consumed prefix of any size (see this module's own doc
/// comment on `LineColScan`). `consumed`'s own byte length determines
/// the new `offset` (matching `String.slice`/`String.drop`'s byte
/// semantics).
#[partial]
def advance_location (loc : Location) (consumed : String) : Location :=
	match loc {
		mk off line col =>
			let byte_len : I64 := String.length consumed in
			let new_off : I64 := I64.add off byte_len in
			match line_col_scan consumed {
				mk newlines _chars trailing =>
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
// The divide-and-conquer split is kept for the same reason
// `line_col_scan` has it: the interpreter overflows its stack somewhere
// around 1000-1500 frames, and a whole-file linear walk is one frame per
// character. But unlike `line_col_scan` this needs no `combine` step --
// threading the running `Location` left-to-right through the halves means
// the right half simply starts where the left one ended.

/// A bulk resolution in progress.
struct ResolveState {
    /// Position at the start of the not-yet-scanned remainder. `offset`
    /// is absolute within the whole file, which is what `pending` is
    /// measured against.
    loc : Location,
    /// Offsets still to resolve, ascending. Consumed from the head as the
    /// walk passes each one.
    pending : List I64,
    /// Resolved pairs, in reverse order of resolution.
    out : List (Pair I64 Location),
}

/// Emit every pending offset the walk has now reached or passed.
///
/// `>=` rather than `==` deliberately: an offset that does not land on a
/// character boundary (which a real span always does, but a corrupted or
/// synthesized one might not) must still be consumed, or it would block
/// every later offset behind it and silently lose the rest of the file.
#[partial]
def resolve_emit_reached (st : ResolveState) : ResolveState := match st.pending {
    List.empty => st,
    List.cons off rest =>
        if I64.lt st.loc.offset off
        then st
        else resolve_emit_reached
                { loc := st.loc,
                  pending := rest,
                  out := List.cons (Pair.pair off st.loc) st.out },
}

/// Advance one character. Mirrors `line_col_scan_direct`'s stepping
/// exactly -- byte offset by the character's WIDTH, column by one
/// character -- which is the distinction that makes a column after a
/// multi-byte character correct.
#[partial]
def resolve_step_loc (loc : Location) (ch : String) (width : I64) : Location :=
    if String.beq "\n" ch
    then Location.mk (I64.add loc.offset width) (I64.add loc.line 1) 1
    else Location.mk (I64.add loc.offset width) loc.line (I64.add loc.column 1)

/// Walk a chunk one character at a time, resolving offsets as it passes
/// them. Only ever called on chunks already under `dc_threshold`, so the
/// recursion stays well inside the interpreter's frame ceiling.
#[partial]
def resolve_direct (s : String) (st : ResolveState) : ResolveState :=
    if String.is_empty s
    then st
    else
        let st1 : ResolveState := resolve_emit_reached st in
        let width : I64 := utf8_char_width s in
        let ch : String := String.slice s 0 width in
        resolve_direct (String.drop width s)
            { loc := resolve_step_loc st1.loc ch width, pending := st1.pending, out := st1.out }

/// Resolve every pending offset falling inside `s`, threading the running
/// position left to right. O(n) total work, O(log n) recursion depth.
#[partial]
def resolve_offsets (s : String) (st : ResolveState) : ResolveState :=
    if I64.lt (String.length s) dc_threshold
    then resolve_direct s st
    else
        let mid : I64 := safe_split_offset s (I64.div (String.length s) 2) in
        // Left first, then right from wherever left ended -- this
        // sequencing is what replaces `combine_line_col_scan`.
        resolve_offsets (String.drop mid s) (resolve_offsets (String.slice s 0 mid) st)

/// Resolve `offsets` (ascending, absolute byte offsets) against `source`.
///
/// Offsets at or past end-of-file resolve to the file's final position
/// rather than being dropped: end-of-input is a real position, and a
/// dropped entry would leave a term with no location for no visible
/// reason.
#[partial]
def resolve_offsets_in_file (source : String) (offsets : List I64) : List (Pair I64 Location) :=
    // The single-pass walk consumes `pending` from the head and never goes
    // back, so a non-ascending list would resolve everything after the
    // first inversion to whatever position the walk had already reached --
    // silently wrong positions, not a crash. Callers are expected to
    // collect in tree order (which IS ascending, since `ParseSpan` stores a
    // remaining length and a pre-order walk visits nodes left to right),
    // but "expected" is not "checked", so check.
    if is_ascending offsets
    then resolve_ascending source offsets
    else resolve_one_by_one source offsets

/// The correct-but-quadratic path, for input the fast path cannot take.
/// Slow beats wrong.
#[partial]
def resolve_one_by_one (source : String) (offsets : List I64) : List (Pair I64 Location) :=
    match offsets {
        List.empty => List.empty,
        List.cons off rest =>
            List.cons (Pair.pair off (location_of_remaining_len source (String.length source - off)))
                      (resolve_one_by_one source rest),
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

#[partial]
def resolve_ascending (source : String) (offsets : List I64) : List (Pair I64 Location) :=
    let done : ResolveState :=
        resolve_offsets source { loc := Location.mk 0 1 1, pending := offsets, out := List.empty } in
    // `resolve_emit_reached` cannot fire for an offset past the end during
    // the walk (the walk stops at EOF), so flush them here.
    let flushed : ResolveState := resolve_flush done in
    list_reverse_pairs flushed.out List.empty

#[partial]
def resolve_flush (st : ResolveState) : ResolveState := match st.pending {
    List.empty => st,
    List.cons off rest =>
        resolve_flush { loc := st.loc, pending := rest, out := List.cons (Pair.pair off st.loc) st.out },
}

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
/// continuation byte satisfies. The two paths deliberately differ on a
/// non-boundary offset: this one advances to the next boundary, while
/// `location_of_remaining_len` slices mid-character. Neither is meaningful
/// there, and consuming the offset is the safer of the two -- blocking on
/// it would stall every later offset behind it.
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

/// Long enough to force the divide-and-conquer split (`dc_threshold` is
/// 400 bytes), so the split path is exercised rather than only the direct
/// walk -- and so a wrong split would show up as a wrong line.
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
