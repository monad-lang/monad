/// What is under the cursor: the identifier that a hover, a definition jump or a
/// reference search is about.
///
/// THIS IS THE HALF OF THE REFERENCE'S `identifier_at` THAT IS WORTH KEEPING.
/// `rust/rust-cli/src/main.rs:712-736` does two things: it scans the line the cursor
/// is on for the run of identifier characters around a column, and then it
/// resolves the resulting NAME against a symbol table. The scan is right and the
/// resolution is not -- its own doc records that a local shadowing a top-level
/// def resolves to the top-level one, and that an ambiguous cross-mote name
/// resolves to whichever file a scan happens to reach first. This module is the
/// scan and only the scan: it answers WHICH BYTES the cursor is on, and the
/// `motes/lsp` engine resolves the name against the warm scope, where the
/// shadowing answer exists because the scope has a parent chain. Keeping the two
/// apart is what lets the second half be fixed without touching the first.
///
/// THE WORKING UNIT IS A BYTE OFFSET, NOT A LINE AND COLUMN, and that is a
/// deliberate departure. The checker reports byte offsets, the span table is
/// built in byte offsets, and `toolkit::position`'s `offset_of_wire` already
/// converts a wire position into one. A scan taking a line and a character would
/// need its own conversion back into the same units, and two conversions of one
/// position that disagree -- one counting UTF-16 code units, one counting
/// characters -- is exactly the class of bug this mote exists to not have. There
/// is no conversion here. The caller converts once.
///
/// A RUN CANNOT CROSS A LINE, because `\n` and `\r` are not identifier
/// characters. So the scan needs no line index and no line bound -- and that is
/// not an incidental simplification but what makes the step-back-one-byte rule in
/// `text_identifier_at` safe. Its doc has the argument.
///
/// THE CHARACTER SET IS THE REFERENCE'S, verbatim: ASCII alphanumeric, `_`, `.`
/// and `'`. Each of the four is load-bearing:
///
///  - `_` and the digits are how a great many names are spelled.
///  - `.` makes a qualified name -- `Json.parse`, `p.first`, `U8.gt` -- a single
///    run, because a cursor on any part of one is a question about the whole
///    qualified name. Splitting it into a module part and a name part is the
///    resolver's job, since only the resolver knows which modules are in scope.
///  - `'` allows a primed name, and it also means a character literal reads as
///    one run. The reference does the same, and it costs nothing: `'a'` resolves
///    as a name and fails to resolve, so hover shows nothing, which is the honest
///    answer for a cursor on a literal.
///
/// The set is ASCII-only on purpose. A non-ASCII byte -- a lead byte or a
/// continuation byte of any UTF-8 character -- is not an identifier byte, so an
/// identifier ENDS at the first one. Monad identifiers are ASCII, so a
/// non-ASCII byte inside one means the cursor is in a comment or a string, where
/// there is nothing to resolve. The useful consequence runs the other way:
/// every offset this module returns is an ASCII byte offset, hence a character
/// boundary, which is what makes slicing the span back out of the source safe
/// with no further check.

/// A half-open byte range `[start, stop)` into one source string.
///
/// Half-open rather than inclusive so that `stop - start` is the length and an
/// empty span is expressible, which matters upstream: an LSP range's two ends are
/// positions, and a caller that wants a one-character range around a point can
/// say so without a special case.
pub struct TextSpan { start : I64, stop : I64 }

pub def text_span_mk (start : I64) (stop : I64) : TextSpan := TextSpan.mk start stop

pub def text_span_start (sp : TextSpan) : I64 := sp.start

pub def text_span_stop (sp : TextSpan) : I64 := sp.stop

/// The span's text, sliced out of the source it came from.
///
/// No boundary check, and it is not an omission: every span this module produces
/// begins and ends on an ASCII byte, so neither end can fall inside a
/// multi-byte character. A span a caller built by hand could, and
/// `String.slice` answers the empty string in that case rather than panicking --
/// the behaviour `position.mo` relies on for the same reason.
pub def text_span_text (src : String) (sp : TextSpan) : String :=
  String.slice src sp.start (I64.sub sp.stop sp.start)

/// The identifier the cursor is on, or the one it is at the end of.
///
/// LSP positions sit BETWEEN characters while an offset names a byte, so the
/// cursor a user sees as "on the last character of `foo`" arrives as the offset
/// of the byte AFTER it -- the position that follows the word, which is also
/// where a client sends the cursor when the user has just typed it. Testing only
/// the byte at the offset would answer nothing for that single most common
/// gesture there is, so when the byte at the offset is not an identifier byte,
/// the byte BEFORE it is what the scan anchors on.
///
/// THE STEP BACK CANNOT SHADOW A CORRECT ANSWER, which is why it is safe. It is
/// taken only when the byte at the offset is not an identifier byte, and then the
/// offset is not inside any identifier -- there is no run it could belong to --
/// so the preceding identifier is the only one the cursor could plausibly mean.
/// A cursor ON an identifier character, which is where an editor that positions
/// its cursor on a character puts it, is decided by the byte at the offset and
/// never reaches this rule at all.
///
/// IT CANNOT WALK ONTO THE PREVIOUS LINE, which is the case a rule like this
/// gets wrong and so is worth stating rather than assuming. A cursor on an
/// indented line's first space arrives with the byte before it being that line's
/// `\n`, and `\n` is not an identifier byte, so the rule declines: the answer is
/// nothing, not the last identifier of the line above. The general statement is
/// the same one that bounds a run -- the terminator is not an identifier byte, so
/// no test for one can step over it -- and the `text_run_covers` doc makes the
/// same point from the other side.
///
/// An offset past the end of the source is treated as its predecessor, the same
/// rule as above; an offset before the start answers nothing. Callers get an
/// offset from `offset_of_wire`, which clamps, so neither is reachable in
/// practice -- they are total anyway, because a cursor position is client input
/// and a server that crashes on out-of-range input is a server that crashes.
pub def text_identifier_at (src : String) (offset : I64) : Option TextSpan :=
  text_scan (String.to_list src) 0 0 offset

/// The identifier's text, for the caller that wants the name and not the bounds.
pub def text_identifier_text (src : String) (offset : I64) : Option String :=
  match text_identifier_at src offset {
    Option.none => Option.none,
    Option.some sp => Option.some (text_span_text src sp),
  }

/// One pass, carrying the start of the run in progress.
///
/// `run_start` is advanced to `i + 1` on every non-identifier byte, whether or
/// not an answer was given, so at any identifier byte the run in progress starts
/// at exactly the first byte of that run. That replaces carrying the previous
/// byte's classification: a run is non-empty exactly when `run_start < i`, which
/// is a test `text_run_covers` already has to make.
///
/// A run is answered the moment it ends, and the first run that covers the offset
/// is the answer: a later run starts after this one stops, so it cannot cover an
/// offset this one did, and an earlier run that covered it would have returned
/// already. The walk therefore stops at the cursor's own identifier rather than
/// reading the rest of the file.
#[partial]
def text_scan (bs : List U8) (i : I64) (run_start : I64) (offset : I64) : Option TextSpan :=
  match bs {
    List.empty =>
      if text_run_covers run_start i offset
      then Option.some (TextSpan.mk run_start i)
      else Option.none,
    List.cons b rest =>
      if text_byte_is_identifier b
      then text_scan rest (I64.add i 1) run_start offset
      else
        if text_run_covers run_start i offset
        then Option.some (TextSpan.mk run_start i)
        else text_scan rest (I64.add i 1) (I64.add i 1) offset,
  }

/// Whether the run `[run_start, stop)` is the one the cursor is on or at the end
/// of: `run_start <= offset <= stop`, with a non-empty run.
///
/// The `stop > run_start` conjunct is doing two jobs at once, and it is worth
/// knowing both. It rejects the empty run at a byte the scan has just decided is
/// not an identifier's -- without it, a cursor on a space would be "at the end of"
/// a zero-width run starting there. And it is the whole of the line-crossing rule:
/// after a `\n` the run start equals the newline's successor, so the run the
/// previous line ended with has already been considered and rejected on its own
/// bounds (`offset <= stop` fails for a cursor past the terminator), and the empty
/// run at the terminator's successor is rejected here.
///
/// `I64` has no `ge`, so `run_start <= offset` is written as the negation of
/// `offset < run_start` -- the same shape `docstore.mo` records for `U8.lt`, one
/// type over.
def text_run_covers (run_start : I64) (stop : I64) (offset : I64) : Bool :=
  Bool.not (I64.lt offset run_start) && I64.gt stop run_start && Bool.not (I64.gt offset stop)

/// Whether a byte can appear in an identifier.
///
/// Written with `U8.gt` against the byte BELOW each range's floor because `U8.lt`
/// is not `pub` -- so "at least `0`" has to be spelled "greater than `/`", and the
/// floor constants below are named for the byte they are, not for the range they
/// bound. `docstore.mo` records the same dodge for the same reason.
def text_byte_is_identifier (b : U8) : Bool :=
  text_byte_is_alphanumeric b
    || U8.beq b text_byte_underscore
    || U8.beq b text_byte_dot
    || U8.beq b text_byte_quote

#[partial]
def text_byte_is_alphanumeric (b : U8) : Bool :=
  (U8.gt b text_byte_slash && Bool.not (U8.gt b text_byte_nine))
    || (U8.gt b text_byte_at_sign && Bool.not (U8.gt b text_byte_upper_z))
    || (U8.gt b text_byte_backtick && Bool.not (U8.gt b text_byte_lower_z))

// The digits and the two letter runs, each floor named as the byte one below it
// because that is the byte the comparison is against.

def text_byte_slash : U8 := 47u8

def text_byte_nine : U8 := 57u8

def text_byte_at_sign : U8 := 64u8

def text_byte_upper_z : U8 := 90u8

def text_byte_backtick : U8 := 96u8

def text_byte_lower_z : U8 := 122u8

// The three punctuation marks that are identifier bytes, named for what they are
// so that a call site is not a number.

def text_byte_dot : U8 := 46u8

def text_byte_underscore : U8 := 95u8

def text_byte_quote : U8 := 39u8
