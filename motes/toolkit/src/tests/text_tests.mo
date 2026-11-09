/// Cursor-scan tests: which bytes an editor's cursor names.
///
/// EVERY EXPECTATION BELOW IS AN OFFSET THAT WAS COUNTED BY HAND over a fixture
/// whose bytes are written out in the comment beside it, and the counting is the
/// point rather than a chore. The scan's rule -- the byte at the offset, or the
/// byte before it -- reads as if it must be off by one somewhere, and the two
/// places it could be are both here as tests: a cursor just past an identifier's
/// last byte, which must find it, and a cursor on the first space of an indented
/// line, which must find NOTHING rather than the identifier that ended the line
/// above. Those two pull in opposite directions, so a version that gets one right
/// by luck is very likely to get the other wrong.
///
/// The consequence tests are here for the same reason and are marked as such:
/// `.` being an identifier byte means `I64.add` is one run and `café` ends at the
/// `é`. Neither is a bug being pinned -- both are the reference's character set
/// and both resolve to nothing, which is the honest answer for a cursor that is
/// not on a name -- but a later reader who finds them odd should find the
/// reasoning next to the assertion rather than have to rederive it.
///
/// Field reads go through the typed accessor defs below (`tt_*`), never inline in
/// a `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `tt_` prefix is collision-avoiding: whole-program scope is shared
/// with every other mote's tests.
use toolkit::text {
    text_identifier_at, text_identifier_text, text_span_mk, text_span_start, text_span_stop,
    text_span_text,
}

// --- Accessors ---

/// The identifier's text, or `<none>` for "nothing here".
///
/// `<none>` cannot be produced by any name in any of these fixtures -- there is no
/// identifier spelled that way -- so an assertion that sees it knows the answer was
/// absent rather than silently comparing against a plausible identifier.
def tt_text (src : String) (offset : I64) : String :=
    match text_identifier_text src offset {
        Option.none => "<none>",
        Option.some s => s,
    }

/// The span's start, or `-1` for "nothing here", which is the sentinel the two
/// bounds tests compare against rather than a position any input can produce.
def tt_start (src : String) (offset : I64) : I64 :=
    match text_identifier_at src offset {
        Option.none => 0 - 1,
        Option.some sp => text_span_start sp,
    }

def tt_stop (src : String) (offset : I64) : I64 :=
    match text_identifier_at src offset {
        Option.none => 0 - 1,
        Option.some sp => text_span_stop sp,
    }

/// Whether the cursor answers nothing at all.
def tt_none (src : String) (offset : I64) : Bool :=
    I64.beq (tt_start src offset) (0 - 1) && I64.beq (tt_stop src offset) (0 - 1)

// --- Fixtures, with their bytes written out ---

/// `foo bar` -- the smallest source with two identifiers and a space between.
///             f0 o1 o2 _3 b4 a5 r6
def tt_two : String := "foo bar"

/// Two lines, the second indented, so the line-crossing case is expressible:
///   `def f : I64 := 1` then a newline then two spaces then `x`.
///   d0 e1 f2 _3 f4 _5 :6 _7 I8 69 410 _11 :12 =13 _14 1_15 \n16 _17 _18 x19
def tt_lines : String := "def f : I64 := 1\n  x"

/// A real line of Monad, so the scan is exercised on the shapes a user actually
/// puts a cursor on: a def header, a type, a dotted call, and an operand.
///   `def add (a : I64) : I64 :=` then a newline, two spaces, `I64.add a 1`.
///   d0 e1 f2 _3 a4 d5 d6 _7 (8 a9 _10 :11 _12 I13 614 415 )16 _17 :18 _19
///   I20 621 422 _23 :24 =25 \n26 _27 _28 I29 630 431 .32 a33 d34 d35 _36
///   a37 _38 139 \n40
def tt_code : String := "def add (a : I64) : I64 :=\n  I64.add a 1\n"

// --- One identifier, from every byte of it ---

/// Every byte OF an identifier answers with that identifier -- the first, a
/// middle one, the last, and the one past the end. The last two are the pair
/// worth having together: 2 is the byte a cursor-on-a-character client sends, and
/// 3 is the byte a cursor-between-characters client sends for the same visual
/// position.
#[test]
def test_every_byte_of_an_identifier_answers_with_it : Bool :=
    String.beq (tt_text tt_two 0) "foo"
        && String.beq (tt_text tt_two 1) "foo"
        && String.beq (tt_text tt_two 2) "foo"
        && String.beq (tt_text tt_two 3) "foo"
        && I64.beq (tt_start tt_two 2) 0
        && I64.beq (tt_stop tt_two 2) 3

/// The span is half-open on the identifier's own bounds, and the text sliced from
/// it is the identifier -- so the two accessors and the slicing agree, which is
/// what a caller sending a range to a client depends on.
#[test]
def test_the_span_is_half_open_and_slices_to_the_name : Bool :=
    I64.beq (tt_start tt_two 4) 4
        && I64.beq (tt_stop tt_two 4) 7
        && String.beq (text_span_text tt_two (text_span_mk (tt_start tt_two 4) (tt_stop tt_two 4))) "bar"

/// The step back onto the preceding identifier, in both of its reachable
/// shapes: the byte just past an identifier's end, and an offset past the end of
/// the whole source. The second is the clamp case -- clients do not send it, but
/// it arrives from arithmetic on client input, so it must be total.
#[test]
def test_a_cursor_just_past_an_identifier_finds_it : Bool :=
    String.beq (tt_text tt_two 7) "bar"
        && String.beq (tt_text tt_two 3) "foo"
        && I64.beq (tt_stop tt_two 3) 3

/// A cursor on a byte that is neither an identifier's nor a step back onto one
/// answers nothing. Offsets 8 and 9 are past `bar`'s end and onto a byte that does
/// not exist; 0 of the source below is a space with nothing before it.
#[test]
def test_a_cursor_on_a_non_identifier_answers_nothing : Bool :=
    tt_none " a" 0
        && String.beq (tt_text " a" 1) "a"
        && tt_none "abc" 4
        && tt_none "abc" 9

/// An empty source answers nothing at any offset, including the two offsets a
/// client can legally send for it -- 0, and 1 from an editor that puts the cursor
/// one past an empty line.
#[test]
def test_an_empty_source_answers_nothing : Bool :=
    tt_none "" 0 && tt_none "" 1

// --- The line-crossing case, in both directions ---

/// THE PIN. A cursor on the first space of an indented line -- the position a
/// client sends when the user has moved to the start of a line and pressed the
/// key -- must answer NOTHING, because the byte before it is the previous line's
/// terminator and a terminator is not an identifier byte. A scan that anchored on
/// "the previous identifier however far back" would answer `1` here, silently
/// jumping to a declaration on the line above.
#[test]
def test_a_cursor_on_an_indent_does_not_reach_the_previous_line : Bool :=
    tt_none tt_lines 17 && tt_none tt_lines 18

/// The other direction: a cursor at the END of a line finds that line's last
/// identifier, including on the terminator byte itself. The two tests together
/// are the whole rule -- the terminator belongs to the line it ends, and to
/// nothing else.
#[test]
def test_a_cursor_at_the_end_of_a_line_finds_that_line : Bool :=
    String.beq (tt_text tt_lines 15) "1"
        && String.beq (tt_text tt_lines 16) "1"
        && String.beq (tt_text tt_lines 19) "x"
        && String.beq (tt_text tt_lines 20) "x"
        && tt_none tt_lines 21

/// A type name, and the `)` that follows it: the closing paren is the commonest
/// byte a cursor lands on just after an identifier, and it is the same step-back
/// rule the space exercises.
#[test]
def test_a_type_name_and_the_paren_after_it : Bool :=
    String.beq (tt_text tt_code 13) "I64"
        && String.beq (tt_text tt_code 16) "I64"
        && I64.beq (tt_start tt_code 16) 13
        && I64.beq (tt_stop tt_code 16) 16

/// A `:` between two spaces, which is the case where the byte at the offset and
/// the byte before it are BOTH non-identifier bytes -- so the answer is nothing
/// even though identifiers sit two bytes either side: `I64` ends at 16, and the
/// next `I64` begins at 20. The rule takes one step back and no more, so a scan
/// that kept stepping back until it found an identifier byte would answer here,
/// and the honest answer is nothing.
#[test]
def test_a_colon_between_spaces_answers_nothing : Bool :=
    tt_none tt_code 18

/// The same one-step rule around a lone operator: `+` in `p.first + 1` answers
/// nothing, and so does the space after it -- the byte one back from that space is
/// the `+`, which is not an identifier byte. The `1` itself answers, as does the
/// offset one past its end.
#[test]
def test_a_lone_operator_answers_nothing : Bool :=
    tt_none "p.first + 1" 8
        && tt_none "p.first + 1" 9
        && String.beq (tt_text "p.first + 1" 10) "1"
        && String.beq (tt_text "p.first + 1" 11) "1"

// --- Consequence pins: what the character set makes of dotted and non-ASCII text ---

/// A qualified name is ONE run, because `.` is an identifier byte. A cursor on
/// any byte of `I64.add` -- including the dot and including the trailing segment
/// alone -- answers with all seven bytes. That is deliberate: only the resolver
/// knows which modules are in scope, so splitting a qualified name into a module
/// part and a name part is its job and not the scan's.
#[test]
def test_a_qualified_name_is_one_run : Bool :=
    String.beq (tt_text tt_code 29) "I64.add"
        && String.beq (tt_text tt_code 31) "I64.add"
        && String.beq (tt_text tt_code 33) "I64.add"
        && String.beq (tt_text tt_code 32) "I64.add"
        && String.beq (tt_text tt_code 36) "I64.add"
        && I64.beq (tt_stop tt_code 33) 36

/// The step back off a space lands on the qualified name's LAST byte and answers
/// the whole run, not just `add` -- the counterpart of the paren test one level
/// up, on a dotted name rather than a bare one.
#[test]
def test_the_space_after_a_qualified_name_answers_the_whole_run : Bool :=
    String.beq (tt_text tt_code 36) "I64.add"
        && I64.beq (tt_start tt_code 36) 29

/// `p.first` in expression position is the same shape as `I64.add` in call
/// position, and the cursor on its dot answers the whole access. A field access
/// is not resolved by this engine -- there are no field declarations in the span
/// table -- so the answer reaching the resolver is a name that resolves to
/// nothing, which is the honest outcome and not a wrong jump.
#[test]
def test_a_dotted_field_access_is_one_run : Bool :=
    String.beq (tt_text "p.first + 1" 4) "p.first"
        && String.beq (tt_text "p.first + 1" 0) "p.first"
        && String.beq (tt_text "p.first + 1" 7) "p.first"

/// `_` and digits are identifier bytes, so `x_1` is one run and so is `y2`.
#[test]
def test_underscores_and_digits_are_identifier_bytes : Bool :=
    String.beq (tt_text "x_1 := y2" 1) "x_1"
        && String.beq (tt_text "x_1 := y2" 3) "x_1"
        && String.beq (tt_text "x_1 := y2" 8) "y2"
        && tt_none "x_1 := y2" 4

/// `'` is an identifier byte, so a character literal reads as a single run. Pinned
/// as a consequence: the run's text is `'a'`, which no declaration is named, so
/// resolution finds nothing and hover shows nothing -- the honest answer for a
/// cursor on a literal.
#[test]
def test_a_character_literal_reads_as_one_run : Bool :=
    String.beq (tt_text "x = 'a'" 5) "'a'"
        && I64.beq (tt_start "x = 'a'" 5) 4
        && I64.beq (tt_stop "x = 'a'" 5) 7

/// A non-ASCII byte ends an identifier, and the two bytes of `é` are treated
/// differently for the reason the rule gives: the LEAD byte is the byte after the
/// identifier's end, so a cursor on it steps back onto `caf`, while the
/// CONTINUATION byte has no identifier before it that ends there -- the run
/// already closed one byte earlier -- and answers nothing.
///
/// The continuation case is the one that matters for safety: a cursor inside a
/// multi-byte character can never produce an offset pair that splits it, because
/// it produces nothing at all.
#[test]
def test_a_non_ascii_byte_ends_an_identifier : Bool :=
    String.beq (tt_text "café.mo" 2) "caf"
        && String.beq (tt_text "café.mo" 3) "caf"
        && tt_none "café.mo" 4
        && I64.beq (tt_stop "café.mo" 3) 3

/// The dot in a file extension is an identifier byte like any other, so `.mo` is
/// a run of its own. Pinned because it is a consequence a reader will want
/// explained rather than a case anyone chose: nothing is named `.mo`, so
/// resolving it finds nothing, and the alternative -- excluding a leading dot --
/// would need a rule about what a dot may start, which is the resolver's business
/// and not the scan's.
#[test]
def test_a_leading_dot_begins_a_run : Bool :=
    String.beq (tt_text "café.mo" 5) ".mo"
        && I64.beq (tt_start "café.mo" 5) 5
        && I64.beq (tt_stop "café.mo" 5) 8

/// A span built by hand slices out of whatever source it is handed, which is what
/// lets a caller send a range for text it is not currently scanning -- the
/// documentSymbol path, which has a span from the parser and a source from the
/// docstore.
#[test]
def test_a_hand_built_span_slices_the_source_it_is_given : Bool :=
    String.beq (text_span_text "hello world" (text_span_mk 6 11)) "world"
        && String.beq (text_span_text "hello world" (text_span_mk 0 0)) ""
