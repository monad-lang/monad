/// Source positions: `lang`'s coordinates on one side, the LSP wire's on the
/// other, and the three different counts in between.
///
/// THE THREE COUNTS ARE NOT THE SAME COUNT, and every bug this module exists to
/// prevent is a mix-up between them:
///
///   * `lang`'s `Location.offset` is a 0-based BYTE offset into the file.
///   * `lang`'s `Location.column` is 1-based and counts CODE POINTS -- pinned by
///     `test_resolve_offsets_column_counts_characters`
///     (`lang/src/parser/position.mo:623`), where an em dash advances the
///     column by one and the byte offset by three.
///   * LSP's `Position.character` is 0-based and counts whatever the negotiated
///     `positionEncoding` says: UTF-8 code units (which are bytes) for
///     `"utf-8"`, UTF-16 code units for `"utf-16"`.
///
/// So none of the three is derivable from another by arithmetic, and the one
/// that looks cheapest -- `column - 1` -- is correct for ASCII-only text and
/// silently wrong past the first astral character. `wire_of_location` therefore
/// takes `line` and `offset` and NOT `column`, and that omission is the point
/// rather than an oversight: there is no encoding for which `column` is the
/// answer, so accepting it would only invite the mistake.
///
/// The failure mode is worth stating because it is quiet. A position that is
/// off by one code unit puts the editor's cursor on the neighbouring character
/// and its squiggle one column to the left; nothing errors, nothing logs, and
/// the only symptom is that the tool looks slightly careless on exactly the
/// lines a human is most likely to be reading closely. `test_position_*` below
/// pin the two inputs where the cheap answer diverges, one BMP and one astral.
///
/// THIS MODULE DELIBERATELY DOES NOT KNOW ABOUT `lang`. It works on plain `I64`
/// coordinates because `lang` depends on `llvm` and `runtime`, so a dependency
/// edge -- even for one struct -- would drag the whole compiler into the
/// closure of every consumer, including a linter or formatter that needs
/// position conversion and nothing else. `motes/lsp` holds the two one-line
/// adapters that read `Location.line` and `Location.offset`; the cost of that
/// split is two lines, and the benefit is that the tests below run against
/// `init` alone.
///
/// Lines are 1-BASED in a `LineIndex` and 0-BASED on the wire, each matching
/// the convention of the side it came from. Only `wire_of_location` and
/// `offset_of_wire` cross that boundary, and each does it once.

use toolkit::bytes { byte_cr, byte_lf, is_ascii_byte, is_continuation_byte, utf16_units_of_byte }

/// Which unit LSP counts `Position.character` in.
///
/// Negotiated at `initialize`; the client's first choice of `["utf-8",
/// "utf-16"]` that this server supports wins. Both are supported because both
/// are cheap here: the encoding decides one predicate, not the architecture.
pub type PositionEncoding {
  utf8,
  utf16,
}

/// The specification's default, and what a client that announces nothing gets.
///
/// This is also what the Rust server being replaced assumed, less explicitly:
/// it advertised no `positionEncoding` at all (`rust/rust-cli/src/lsp.rs:285-304`)
/// and so was held to utf-16 by clients while its ranges were built from
/// byte-derived columns. This module exists so that assumption can be made
/// true instead of avoided.
pub def position_encoding_default : PositionEncoding := PositionEncoding.utf16

/// `"utf-8"` / `"utf-16"` as the wire spells them, or `Option.none` for a name
/// this server does not speak.
///
/// The names are matched EXACTLY, lowercase and hyphenated, because that is
/// what the specification fixes and what clients send. An unrecognized name
/// answers `Option.none` rather than falling back silently, so the caller can
/// report what it was offered -- and the caller MUST then keep
/// `position_encoding_default`, since a client that asked for something else
/// and was silently given utf-16 is the desynchronization this module is built
/// to prevent.
pub def position_encoding_from_string (s : String) : Option PositionEncoding :=
  if String.beq s "utf-8"
  then Option.some PositionEncoding.utf8
  else
    if String.beq s "utf-16"
    then Option.some PositionEncoding.utf16
    else Option.none

/// The name to echo back in the `initialize` result.
pub def position_encoding_name (e : PositionEncoding) : String :=
  match e {
    PositionEncoding.utf8 => "utf-8",
    PositionEncoding.utf16 => "utf-16",
  }

/// A wire position. Both fields 0-based, as LSP defines them.
pub struct WirePosition { line : I64, character : I64 }

/// Build one, for callers that must not write a struct literal in argument
/// position -- a recorded self-hosted codegen hazard in this repo.
pub def wire_position_mk (line : I64) (character : I64) : WirePosition :=
  WirePosition.mk line character

pub def wire_position_line (p : WirePosition) : I64 := p.line

pub def wire_position_character (p : WirePosition) : I64 := p.character

/// A wire range: two positions, `start` inclusive and `end` EXCLUSIVE, as LSP
/// defines them.
///
/// `WireRange` lives here rather than beside the diagnostics that motivated it
/// because a range is a position concept: hover needs one, a definition target
/// needs one, an outline entry needs one, and only one of those four is a
/// diagnostic. The alternative -- each consumer carrying its own pair of
/// positions -- is how a codebase ends up with two spellings of the same
/// conversion, one of which has the exclusive-end rule right.
pub struct WireRange { start : WirePosition, end : WirePosition }

/// For callers that must not write a struct literal in argument position -- the
/// same recorded self-hosted codegen hazard `wire_position_mk` exists for.
pub def wire_range_mk (start : WirePosition) (end : WirePosition) : WireRange :=
  WireRange.mk start end

pub def wire_range_start (r : WireRange) : WirePosition := r.start

pub def wire_range_end (r : WireRange) : WirePosition := r.end

/// One line's byte extent, plus the one bit that makes conversion cheap.
///
/// `stop` EXCLUDES the line's terminator -- both the `\n` and a `\r` before it
/// -- so `[start, stop)` is the line's text exactly as an editor shows it, with
/// no carriage return for a caller to trim. Every caller wants it that way: a
/// range that included the terminator would make a whole-line squiggle extend
/// one character past the text on a CRLF file.
///
/// `ascii` is carried because for ASCII text all three counts coincide, which
/// turns both scans into a subtraction. It is worth a field rather than a
/// re-scan at conversion time: this corpus is mostly comments and code, so a
/// large majority of lines are pure ASCII and a majority of conversions take
/// the O(1) path.
pub struct LineInfo { start : I64, stop : I64, ascii : Bool }

/// Every line's extent in source order, line 1 first.
///
/// A source ending in `\n` gets a final EMPTY line, and that is deliberate
/// rather than an off-by-one. An editor showing a file that ends with a newline
/// shows an empty last line and will put a cursor on it, so a `Location` on that
/// line is legal and must convert; a naive "one line per newline" index would
/// answer `Option.none` for the position a user most often has when they have
/// just typed a newline at the end of a file. A source with no trailing newline
/// gets no such line.
pub struct LineIndex { lines : List LineInfo }

pub def line_info_start (li : LineInfo) : I64 := li.start

pub def line_info_stop (li : LineInfo) : I64 := li.stop

pub def line_info_is_ascii (li : LineInfo) : Bool := li.ascii

/// The number of lines. At least 1, for any input including the empty string --
/// an empty file is one empty line, which is what an editor shows.
pub def line_count (ix : LineIndex) : I64 := line_count_go ix.lines 0

#[partial]
def line_count_go (ls : List LineInfo) (acc : I64) : I64 :=
  match ls {
    List.empty => acc,
    List.cons _l rest => line_count_go rest (I64.add acc 1),
  }

/// The extent of `line`, 1-based. `Option.none` past the last line.
pub def line_at (ix : LineIndex) (line : I64) : Option LineInfo :=
  line_at_go ix.lines line

#[partial]
def line_at_go (ls : List LineInfo) (line : I64) : Option LineInfo :=
  match ls {
    List.empty => Option.none,
    List.cons l rest => if I64.beq line 1 then Option.some l else line_at_go rest (I64.sub line 1),
  }

/// The line containing byte `offset`, 1-based -- the inverse of `line_at`'s
/// question.
///
/// THE LAST LINE THAT STARTS AT OR BEFORE `offset`, and this is a decision about
/// the three offsets that sit between two lines rather than about the ordinary
/// case. `LineInfo.stop` EXCLUDES the terminator, so a line's own half-open range
/// `[start, stop)` leaves its newline, and on a CRLF file the byte between the
/// two, belonging to no line at all -- while `wire_character` clamps such an
/// offset INTO the line it was given. So an offset on a terminator has to resolve
/// to the line it terminates, which is what "the last line starting at or before
/// it" gives, and it is the only rule under which this function and
/// `wire_character`'s clamp agree about where a byte is. An offset past the end
/// of the source resolves to the last line for the same reason.
///
/// `Option.none` only for a HAND-BUILT empty index. `line_index_of_source` always
/// produces at least one line -- `LineIndex` is a struct with a public field, so
/// this is reachable, and the honest answer for an index with no lines is that no
/// line contains anything. Every caller below propagates it rather than inventing
/// line 1.
///
/// A linear scan, not a binary search over the list: `List` has no random access,
/// and every caller here holds a source of a few thousand lines and asks twice.
#[partial]
pub def line_of_offset (ix : LineIndex) (offset : I64) : Option I64 :=
  line_of_offset_go ix.lines offset 1 Option.none

/// Stops at the first line that STARTS after `offset`: the lines are in source
/// order, so every line after that one starts later still. `n` counts 1-based and
/// `best` carries the last start at or before the offset.
#[partial]
def line_of_offset_go (ls : List LineInfo) (offset : I64) (n : I64) (best : Option I64) : Option I64 :=
  match ls {
    List.empty => best,
    List.cons li rest =>
      if I64.gt (line_info_start li) offset
      then best
      else line_of_offset_go rest offset (I64.add n 1) (Option.some n),
  }

/// The wire range spanning a byte span of the source.
///
/// THE CURSOR'S SHAPE, as opposed to `wire_range_of_points`' two `Location`s:
/// what a text scan answers is a span of BYTES -- `toolkit::text`'s
/// `text_identifier_at` returns a `TextSpan` -- and turning one into a range used
/// to require the caller to know which line each end was on, which is a fact
/// about the index rather than about the caller.
///
/// Composed from `wire_range_of_points`, so the widening rule and the two
/// encodings are the same code the diagnostic path uses. Both ends resolve
/// through `line_of_offset` first, so a span whose end is on a later line is
/// converted correctly rather than being clamped to the start's line.
#[partial]
pub def wire_range_of_offsets (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (start_offset : I64) (stop_offset : I64) : Option WireRange :=
  match line_of_offset ix start_offset {
    Option.none => Option.none,
    Option.some start_line =>
      match line_of_offset ix stop_offset {
        Option.none => Option.none,
        Option.some stop_line =>
          wire_range_of_points enc ix source start_line start_offset stop_line stop_offset,
      },
  }

/// Split a source into its lines.
///
/// One pass over the bytes, carrying the current line's start and whether the
/// previous byte was a `\r`. `prev_cr` is carried rather than looked up because
/// the line terminator is two bytes on a CRLF file and a single backward scan
/// per newline would be the same walk performed twice.
///
/// Reverses locally rather than using `List.reverse`, for the same reason
/// `framing.mo` reverses locally: four lines of list reversal is not worth
/// widening a module's stated dependency surface for, and this module is
/// otherwise runnable against `init` alone.
///
/// THE SHAPE OF `line_index_go` IS LOAD-BEARING, and the reason is the compiled
/// server rather than taste. That walk advances one byte per step, so its
/// recursion depth IS the size of the file -- and a per-byte machine call
/// exhausts the compiled binary's stack between 100 KB and 209 KB of source,
/// which is smaller than `lang/src/module.mo` (331 KB) and `lang/src/scope.mo`
/// (435 KB): the two files an editor opens. The compiler's self-tail-call rewrite
/// (`lang/src/codegen/tco.mo`) is what turns such a scan into a loop, and it fires
/// only when a merge point is fed by at most ONE self-call -- so a single `if/else`
/// whose BOTH branches recursed fed one merge two of them, pruning would have
/// emptied its phi, and the pass abandoned the transform for the whole function
/// and left the call in place. Hence: one self-call, as the entire `List.cons` arm
/// body, with every per-byte decision lifted into a helper that returns a value.
/// `toolkit/position_tests`' 320 KB scan is the pin on that shape.
#[partial]
pub def line_index_of_source (source : String) : LineIndex :=
  line_index_go (String.to_list source) 0 0 true false List.empty

#[partial]
def line_index_go (bs : List U8) (i : I64) (start : I64) (ascii : Bool) (prev_cr : Bool)
    (acc : List LineInfo) : LineIndex :=
  match bs {
    // The final line, whether or not the source ended with a newline: if it
    // did, `start` already equals `i` and this is the empty last line the doc
    // above promises.
    List.empty => LineIndex.mk (line_index_rev (List.cons (LineInfo.mk start i ascii) acc) List.empty),
    // ONE self-call, and no branching around it -- see this def's own doc above.
    // Each helper below reads only the PRE-step values, so the order they are
    // evaluated in does not matter.
    List.cons b rest =>
      line_index_go rest (I64.add i 1) (line_index_next_start i start b)
        (line_index_next_ascii ascii b) (U8.beq b byte_cr)
        (line_index_next_acc i start ascii prev_cr b acc),
  }

/// Where the line after `b` starts: one past a newline, and unchanged otherwise.
def line_index_next_start (i : I64) (start : I64) (b : U8) : I64 :=
  if U8.beq b byte_lf then I64.add i 1 else start

/// Whether the line `b` is part of is still pure ASCII. A newline starts a new
/// line, which is ASCII until a byte proves otherwise; any other byte can only
/// take the flag away, never give it back.
def line_index_next_ascii (ascii : Bool) (b : U8) : Bool :=
  if U8.beq b byte_lf then true else ascii && is_ascii_byte b

/// The accumulator after `b`: a newline closes the line it terminates and adds
/// it to the reversed list, any other byte contributes nothing.
///
/// The `LineInfo` is built from the pre-step values of all four carried
/// variables, which is why this takes them as parameters rather than reading a
/// post-step state.
def line_index_next_acc (i : I64) (start : I64) (ascii : Bool) (prev_cr : Bool) (b : U8)
    (acc : List LineInfo) : List LineInfo :=
  if U8.beq b byte_lf
  then List.cons (LineInfo.mk start (line_stop i prev_cr) ascii) acc
  else acc

/// Where a line ends, given the index of its `\n` and whether a `\r` precedes
/// it.
def line_stop (lf_index : I64) (prev_cr : Bool) : I64 :=
  if prev_cr then I64.sub lf_index 1 else lf_index

#[partial]
def line_index_rev (ls : List LineInfo) (acc : List LineInfo) : List LineInfo :=
  match ls {
    List.empty => acc,
    List.cons l rest => line_index_rev rest (List.cons l acc),
  }

/// The byte offset just past the character that starts at `offset`.
///
/// A character's byte length in UTF-8 is "one lead byte plus its continuation
/// bytes", so this is a scan for the next byte that is not a continuation -- one
/// step for ASCII, three for an em dash, four for an astral character. A byte
/// offset is not a cursor position: it can land on the second byte of an em
/// dash, and advancing by one from there would name a byte that is inside a
/// character, which is exactly the position `offset_of_wire` clamps away.
///
/// The scan selects by INDEX rather than slicing at `offset` and dropping, for
/// the reason `utf16_units_between` records above: `String.slice` answers the
/// empty string when its range would split a character, so a slice-based walk
/// started at a mid-character offset would silently report the offset as its own
/// successor and produce a zero-width range where a one-character range was
/// wanted.
///
/// The walk stops at the next character boundary, and a line terminator IS one,
/// so the answer is exactly one character further on -- never the rest of the
/// line. A point ON a `\n` widens over that newline and stops there: the range
/// covers the terminator itself, not the first character of the next line. That
/// is the honest report of the byte the parser stopped at, and it is what keeps a
/// one-character range one character wide whatever that character is.
#[partial]
pub def offset_after_char (source : String) (offset : I64) : I64 :=
  let n : I64 := String.length source in
  let j : I64 := offset_after_char_go (String.to_list source) 0 (I64.add offset 1) in
  if I64.gt j n then n else j

#[partial]
def offset_after_char_go (bs : List U8) (i : I64) (from : I64) : I64 :=
  match bs {
    List.empty => i,
    List.cons b rest =>
      if I64.lt i from
      then offset_after_char_go rest (I64.add i 1) from
      else if is_continuation_byte b then offset_after_char_go rest (I64.add i 1) from
      else i,
  }

/// The wire position of a `lang`-style coordinate.
///
/// `source_line` is 1-BASED and `byte_offset` is a 0-based byte offset, matching
/// `Location.line` and `Location.offset`. `column` is deliberately absent; see
/// the module doc. `Option.none` when `source_line` is past the last line, which
/// the caller must clamp rather than treat as "no position" -- a range at the end
/// of a file is a real range.
///
/// The parameters are named for the side they come from rather than `line` and
/// `offset`, because this function and `offset_of_wire` take their line numbers
/// in OPPOSITE conventions -- 1-based here, 0-based there -- and a caller holding
/// both will at some point pass one where the other belongs. That is not a
/// hypothetical: the first version of these tests had four assertions written
/// with the wrong convention, every one of them in a def asserting about the
/// convention. A name that states the convention is what makes the mistake
/// visible at the call site instead of in a failure.
#[partial]
pub def wire_of_location (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (source_line : I64) (byte_offset : I64) : Option WirePosition :=
  match line_at ix source_line {
    Option.none => Option.none,
    Option.some li =>
      Option.some
        (WirePosition.mk (I64.sub source_line 1) (wire_character enc li source byte_offset)),
  }

/// The wire range of a source-space range, given as two points.
///
/// FOUR COORDINATES RATHER THAN TWO `Location`s, and the reason is the module's
/// stated one: this module does not know `lang`, so it cannot take a
/// `SourceRange`. Two line numbers and two byte offsets is the shape `Location`
/// reduces to anyway -- `column` is deliberately not a parameter, for the reason
/// the module doc gives.
///
/// A ZERO-WIDTH RANGE IS WIDENED ONE CHARACTER, and this is the one place in the
/// module where a caller's input is adjusted rather than translated.
/// `lang`'s `Location` is a POINT, so every diagnostic the checker raises from a
/// parse failure carries `start = end` (`lang`'s own `ranged_parse_failure`
/// builds exactly that, and says so), and a zero-width range is an editor
/// showing nothing: no squiggle, no underline, and often no visible marker at
/// all in a diagnostic list. The specification allows it and every client
/// tolerates it; none of them renders it. Widening forward is what a terminal
/// caret renderer does with the same point -- underline the character that is
/// there -- so the editor and `monad check` end up pointing at the same byte.
///
/// Widening stops at the line's end: a point AT the end of the source, or on the
/// final character when there is no further one, stays zero-width. That case is
/// not worth inventing an extent for -- there is no character to underline, and
/// "here, and nothing further" is the range the parser measured.
///
/// A RESIDUAL ZERO-WIDTH CASE UNDER UTF-16, measured rather than feared and
/// worth knowing before it is mistaken for this function failing. UTF-16 counts
/// a character's continuation bytes as ZERO units and puts all of them on the
/// lead byte, so `wire_of_location` rounds an offset that lands inside a
/// character up to the next boundary. A point at the second byte of an astral
/// character and a point at its end therefore name the SAME wire character, and
/// widening the source offset by a whole character moves the wire end not at
/// all: both ends are the same position and the range is empty. UTF-8 has no
/// such case, since its units are bytes and a byte inside a character is a real
/// position. The UTF-16 outcome is right for the input -- an empty range at a
/// real boundary rather than a range underlining half a surrogate pair -- and it
/// is unreachable from `lang`'s diagnostics, whose offsets come from
/// `location_of_remaining` diffing a suffix of the source and so always name a
/// boundary. It is pinned by a test, in both encodings, rather than left as a
/// comment, so that a change to the widening shows up as a changed assertion
/// instead of as a squiggle nobody can explain.
///
/// The two points are assumed ORDERED. Inverting them would be a caller bug this
/// module cannot repair, and `lang/src/tests/decl_range_tests.mo` pins the
/// ordering for the ranges the declaration table produces, so an inverted range
/// reaching here means a new producer rather than a new edge of this function.
#[partial]
pub def wire_range_of_points (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (start_line : I64) (start_offset : I64) (end_line : I64) (end_offset : I64)
    : Option WireRange :=
  match wire_of_location enc ix source start_line start_offset {
    Option.none => Option.none,
    Option.some a =>
      match wire_of_location enc ix source end_line end_offset {
        Option.none => Option.none,
        Option.some b =>
          let e : WirePosition :=
            if wire_same_position a b
            then widen_end enc ix source end_line end_offset b
            else b
          in
          Option.some (wire_range_mk a e),
      },
  }

def wire_same_position (a : WirePosition) (b : WirePosition) : Bool :=
  I64.beq (wire_position_line a) (wire_position_line b)
    && I64.beq (wire_position_character a) (wire_position_character b)

/// The end position widened by one character, or `fallback` -- the position
/// itself -- when the character at `offset` is a terminator or the source ends
/// there.
///
/// The `Option.none` arm cannot be reached: `line` was just converted
/// successfully by the caller, and this converts the same line again. It is an
/// explicit fallback rather than an unreachable branch because the language has
/// no exhaustiveness checking, and a missing arm would be a runtime panic rather
/// than a compile error.
#[partial]
def widen_end (enc : PositionEncoding) (ix : LineIndex) (source : String) (line : I64)
    (offset : I64) (fallback : WirePosition) : WirePosition :=
  match wire_of_location enc ix source line (offset_after_char source offset) {
    Option.none => fallback,
    Option.some p => p,
  }

/// How far into its line `offset` sits, in `enc`'s unit.
///
/// UTF-8 needs no scan at all, because its code units ARE bytes -- the one
/// encoding where the cheap answer is also the right one. UTF-16 folds to the
/// same subtraction on an ASCII line, where one code unit is one byte, and pays
/// for a scan only on a line that `line_index_of_source` already found
/// non-ASCII. Both of those are properties of the DATA, not of the arithmetic,
/// which is why they live in a branch here rather than in a comment claiming
/// the subtraction is generally correct.
#[partial]
def wire_character (enc : PositionEncoding) (li : LineInfo) (source : String) (offset : I64) : I64 :=
  let rel : I64 := I64.sub offset (line_info_start li) in
  match enc {
    PositionEncoding.utf8 => rel,
    PositionEncoding.utf16 =>
      if line_info_is_ascii li
      then rel
      else utf16_units_between source (line_info_start li) offset,
  }

/// UTF-16 code units in `source` at byte indices `start` up to `stop`.
///
/// The WHOLE source is walked rather than the `[start, stop)` slice, and that is
/// the one implementation choice here that is not about speed. `String.slice`
/// answers the EMPTY string when its range would split a character (`get(start
/// ..end).unwrap_or("")`, the semantics `lang/src/parser/position.mo:645-648`
/// records), so a slice-based count would silently answer 0 for a `stop` that
/// landed mid-character -- turning a corrupt offset into a plausible-looking
/// position instead of a wrong one. Walking with an index and selecting by
/// `start <= i < stop` has no such hole, because it never asks for a substring.
///
/// Only a line already known to be non-ASCII reaches here, which bounds the cost
/// to the minority of lines that carry one. That bound is the whole reason the
/// `ascii` field on `LineInfo` earns its keep; without it this walk would run on
/// every position of every file, which for a symbol table of a few thousand
/// declarations is a whole-file scan per declaration.
#[partial]
pub def utf16_units_between (source : String) (start : I64) (stop : I64) : I64 :=
  utf16_units_go (String.to_list source) 0 start stop 0

#[partial]
def utf16_units_go (bs : List U8) (i : I64) (start : I64) (stop : I64) (acc : I64) : I64 :=
  match bs {
    List.empty => acc,
    List.cons b rest =>
      if I64.lt i stop
      then
        utf16_units_go rest (I64.add i 1) start stop
          (if I64.lt i start then acc else I64.add acc (utf16_units_of_byte b))
      else acc,
  }

/// The byte offset a wire position names, or `Option.none` past the last line.
///
/// `p`'s line is 0-BASED, as the wire defines it, and so is one less than the
/// `source_line` `wire_of_location` takes. See that function's doc for why the two
/// are named apart.
///
/// A `character` past the end of its line, or one that lands INSIDE a
/// multi-byte character or between the two units of a surrogate pair, is
/// CLAMPED DOWN rather than rejected. The specification only says a character
/// greater than the line's length means the line's length, and says nothing
/// about the interior of a character -- but a position is where a cursor sits,
/// and a cursor cannot sit inside a character, so the start of the character the
/// position falls inside is the only answer that names a real byte. Clamping up
/// instead would put the cursor past the character the client placed it in.
///
/// `Option.none` for a line past the end is not the same answer as a clamp, and
/// the caller must not conflate them: a position on a line the document does not
/// have is a client bug worth reporting, while a character past a line's end is
/// routine and silent.
#[partial]
pub def offset_of_wire (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (p : WirePosition) : Option I64 :=
  match line_at ix (I64.add (wire_position_line p) 1) {
    Option.none => Option.none,
    Option.some li =>
      Option.some (wire_offset_in_line enc li source (wire_position_character p)),
  }

#[partial]
def wire_offset_in_line (enc : PositionEncoding) (li : LineInfo) (source : String)
    (character : I64) : I64 :=
  let start : I64 := line_info_start li in
  let stop : I64 := line_info_stop li in
  let plain : I64 := clamp_offset start stop (I64.add start character) in
  if I64.lt character 0
  then start
  else
    match enc {
      PositionEncoding.utf8 => plain,
      PositionEncoding.utf16 =>
        if line_info_is_ascii li
        then plain
        else
          match utf16_offset_in_line source start stop character {
            Option.none => stop,
            Option.some off => off,
          },
    }

/// Clamp `v` into `[start, stop]`.
def clamp_offset (start : I64) (stop : I64) (v : I64) : I64 :=
  if I64.lt v start
  then start
  else if I64.gt v stop then stop else v

/// The first byte index at or after `start` whose UTF-16 offset is `target`, or
/// `Option.none` when `target` is at or past the end of the line.
///
/// The `Option.none` is "the line ran out", not "invalid": the caller turns it
/// into `stop`, which is the clamp the specification asks for. Returning the
/// index where the count EXCEEDS the target is what makes a target inside a
/// character clamp down -- the walk stops at the byte where that character
/// begins rather than stepping into its continuation bytes.
#[partial]
def utf16_offset_in_line (source : String) (start : I64) (stop : I64) (target : I64) : Option I64 :=
  utf16_offset_go (String.to_list source) 0 start stop target 0

#[partial]
def utf16_offset_go (bs : List U8) (i : I64) (start : I64) (stop : I64) (target : I64)
    (acc : I64) : Option I64 :=
  if I64.lt i stop
  then
    match bs {
      List.empty => Option.none,
      List.cons b rest =>
        let u : I64 := if I64.lt i start then 0 else utf16_units_of_byte b in
        if I64.lt target (I64.add acc u)
        then Option.some i
        else utf16_offset_go rest (I64.add i 1) start stop target (I64.add acc u),
    }
  else Option.none
