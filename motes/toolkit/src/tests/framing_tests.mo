/// Framing tests: the two cases that fail silently if they are wrong.
///
/// A framing bug does not announce itself. A reader that mishandles a split
/// header drops a message and produces a stream that desynchronizes one
/// request later, which reads as a client bug; a reader that searches for the
/// terminator instead of honouring `Content-Length` splits the first body
/// containing a blank line, which reads as a garbled request. Both leave the
/// server answering, so both cost an afternoon of looking at the wrong end of
/// the pipe. They are pinned here instead.
///
/// Everything is written against the pure reader (`framing_read`), so no
/// socket and no stdio native is involved -- which is the whole reason the
/// framing logic is a function over a buffer rather than a loop over a
/// descriptor.
///
/// Helper names carry an `fr_` prefix. The whole-program scope is shared with
/// every other mote's tests, and this repo has a documented history of two
/// same-named defs silently colliding with the failure flipping on load
/// order; `one_body_is`/`nth` would be exactly the kind of generic name that
/// collides next time a tool mote adds a test helper.
use toolkit::framing {
    FrameRead, FramingMode, content_length, frame_body, frame_reason, frame_rest,
    framing_header_lines, framing_needed, framing_read, is_need_more,
    newline_delimited,
}

// --- Fixtures and flat helpers ---
//
// Field and payload reads are routed through single-level-match helpers
// rather than nested inline, so no test def nests two differently-typed
// matches: a `#[test]` def that touches a struct field is the recorded
// self-hosted codegen hazard, and a nested match is the shape that turns it
// into a wrong return type.

/// A well-formed LSP frame around `body`.
def fr_lsp (body : String) : String :=
    String.concat "Content-Length: "
        (String.concat (I64.to_string (String.length body)) (String.concat "\r\n\r\n" body))

def fr_body_is (r : FrameRead) (expected : String) : Bool :=
    match frame_body r {
        Option.none => false,
        Option.some b => String.beq b expected,
    }

def fr_rest_is (r : FrameRead) (expected : String) : Bool :=
    match frame_rest r {
        Option.none => false,
        Option.some b => String.beq b expected,
    }

def fr_has_reason (r : FrameRead) : Bool :=
    match frame_reason r {
        Option.none => false,
        Option.some _s => true,
    }

def fr_nth (ss : List String) (i : I64) : String :=
    match ss {
        List.empty => "<none>",
        List.cons s rest => if I64.beq i 0 then s else fr_nth rest (I64.sub i 1),
    }

/// Count, and reverse, without leaving the prelude: `List.length` and
/// `List.reverse` are `std`s (`std/src/list.mo:65`), and this suite is
/// deliberately runnable against nothing but `init` -- which is also what
/// keeps `framing.mo` free of a `std` dependency it would never use again.
#[partial]
def fr_len (ss : List String) : I64 :=
    match ss {
        List.empty => 0,
        List.cons _s rest => I64.add 1 (fr_len rest),
    }

#[partial]
def fr_rev (ss : List String) (acc : List String) : List String :=
    match ss {
        List.empty => acc,
        List.cons s rest => fr_rev rest (List.cons s acc),
    }

/// Deliver `msg` one byte at a time, running the reader after each byte and
/// carrying the leftover forward the way the real loop must.
///
/// This is the header-split test in its strongest form: it exercises EVERY
/// split point of the message rather than a hand-picked one, and it asserts
/// the property that matters -- the message comes out exactly once, whole.
/// `bad_header` stops the fold without counting a frame, so a reader that
/// gave up part-way reports fewer frames than the test demands.
///
/// The leftover is fed back in (`rest`, not the old buffer) because a real
/// loop does that: a byte that completed a frame must not be re-read as the
/// start of the next one.
#[partial]
def fr_feed_bytes (msg : String) (i : I64) (n : I64) (buf : String) (frames : I64)
    (bodies : List String) : Pair I64 (List String) :=
    if I64.lt i n
    then
        let buf2 : String := String.concat buf (String.slice msg i 1) in
        match framing_read FramingMode.content_length buf2 {
            FrameRead.need_more => fr_feed_bytes msg (I64.add i 1) n buf2 frames bodies,
            FrameRead.bad_header _r => Pair.pair frames bodies,
            FrameRead.frame body rest =>
                fr_feed_bytes msg (I64.add i 1) n rest (I64.add frames 1) (List.cons body bodies),
        }
    else Pair.pair frames (fr_rev bodies List.empty)

/// Exactly one frame came out, and its body is `expected`.
#[partial]
def fr_one_body_is (p : Pair I64 (List String)) (expected : String) : Bool :=
    match p {
        Pair.pair frames bodies =>
            if I64.beq frames 1
            then
                match bodies {
                    List.empty => false,
                    List.cons b rest =>
                        match rest {
                            List.empty => String.beq b expected,
                            List.cons _b2 _r2 => false,
                        },
                }
            else false,
    }

/// A body containing a blank line, which is legal JSON and the exact thing a
/// terminator-searching reader gets wrong.
def fr_multiline_body : String := "{\"text\":\"a\r\n\r\nb\"}"

#[partial]
def fr_repeat (s : String) (n : I64) : String :=
    if I64.beq n 0
    then ""
    else
        if I64.lt n 64
        then fr_repeat_direct s n
        else
            let half : I64 := I64.div n 2 in
            String.concat (fr_repeat s half) (fr_repeat s (I64.sub n half))

/// Divide-and-conquer for the same reason as every other repeat in this
/// corpus: a naive linear recursion over 600 repetitions overflows the
/// interpreter's stack, and this fixture exists to be larger than the window.
#[partial]
def fr_repeat_direct (s : String) (n : I64) : String :=
    if I64.beq n 0
    then ""
    else String.concat s (fr_repeat_direct s (I64.sub n 1))

// --- One byte at a time ---

#[test]
def test_a_whole_frame_survives_being_fed_one_byte_at_a_time : Bool :=
    let msg : String := fr_lsp "{\"jsonrpc\":\"2.0\"}" in
    fr_one_body_is (fr_feed_bytes msg 0 (String.length msg) "" 0 List.empty) "{\"jsonrpc\":\"2.0\"}"

#[test]
def test_a_frame_with_a_blank_line_in_its_body_survives_byte_feeding : Bool :=
    let msg : String := fr_lsp fr_multiline_body in
    fr_one_body_is (fr_feed_bytes msg 0 (String.length msg) "" 0 List.empty) fr_multiline_body

/// Two frames arriving back-to-back, fed one byte at a time: the second must
/// not be lost to the first's leftover.
#[test]
def test_two_pipelined_frames_survive_byte_feeding : Bool :=
    let msg : String := String.concat (fr_lsp "{\"id\":1}") (fr_lsp "{\"id\":2}") in
    match fr_feed_bytes msg 0 (String.length msg) "" 0 List.empty {
        Pair.pair frames bodies =>
            I64.beq frames 2
                && String.beq (fr_nth bodies 0) "{\"id\":1}"
                && String.beq (fr_nth bodies 1) "{\"id\":2}",
    }

// --- Every split point ---

/// A complete buffer is a whole frame; every PROPER prefix of it is a request
/// for more. Asserted at every offset rather than at a sampled few.
#[test]
def test_every_proper_prefix_asks_for_more_and_the_whole_is_a_frame : Bool :=
    let msg : String := fr_lsp "hello" in
    fr_splits_ok msg 0

#[partial]
def fr_splits_ok (msg : String) (k : I64) : Bool :=
    if I64.lt k (String.length msg)
    then
        if Bool.not (is_need_more (framing_read FramingMode.content_length (String.slice msg 0 k)))
        then false
        else
            if fr_body_is (framing_read FramingMode.content_length msg) "hello"
            then fr_splits_ok msg (I64.add k 1)
            else false
    else true

// --- The header ---

#[test]
def test_a_complete_frame_in_one_buffer : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length (fr_lsp "{\"a\":1}") in
    fr_body_is r "{\"a\":1}" && fr_rest_is r ""

#[test]
def test_a_zero_length_body_is_a_frame_with_an_empty_body : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length "Content-Length: 0\r\n\r\n" in
    fr_body_is r "" && fr_rest_is r ""

/// The body is taken by LENGTH, not by searching for a terminator. A reader
/// that searched would cut this frame at the blank line inside the string and
/// hand the rest of it back as the next frame.
#[test]
def test_a_terminator_inside_the_body_does_not_end_the_frame : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length (fr_lsp fr_multiline_body) in
    fr_body_is r fr_multiline_body && fr_rest_is r ""

/// Spaces on either side of the value are part of no protocol but appear in
/// the wild, and the fold has to skip them rather than fail on them.
#[test]
def test_spaces_around_the_length_are_tolerated : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length "Content-Length:   5  \r\n\r\nhello" in
    fr_body_is r "hello"

#[test]
def test_a_frame_without_content_length_is_a_bad_header : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length "Content-Type: application/json\r\n\r\n{}" in
    fr_has_reason r && Bool.not (is_need_more r)

/// `Content-Length: 0x10` must NOT read as 0. A lenient fold stops at the
/// `x`, takes no bytes, and leaves the 16 bytes of body to be re-parsed as
/// the next frame's header -- the desynchronization this module exists to
/// prevent, reached through the front door.
#[test]
def test_a_non_digit_after_the_value_is_rejected_not_truncated : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length "Content-Length: 0x10\r\n\r\n0123456789abcdef" in
    fr_has_reason r && Bool.not (is_need_more r)

#[test]
def test_a_header_with_no_digits_is_a_bad_header : Bool :=
    let r : FrameRead := framing_read FramingMode.content_length "Content-Length:\r\n\r\n" in
    fr_has_reason r && Bool.not (is_need_more r)

/// Past the window there is no legal header to wait for, so waiting would
/// hang on a broken peer. This must report, not block.
#[test]
def test_a_header_past_the_window_is_rejected_rather_than_awaited : Bool :=
    let buf : String := fr_repeat "Content-Length: " 600 in
    let r : FrameRead := framing_read FramingMode.content_length buf in
    fr_has_reason r && Bool.not (is_need_more r) && I64.gt (String.length buf) 8192

// --- Header line splitting ---

#[test]
def test_header_lines_split_on_crlf_and_drop_the_carriage_return : Bool :=
    let lines : List String := framing_header_lines "Content-Length: 5\r\nContent-Type: x" in
    I64.beq (fr_len lines) 2
        && String.beq (fr_nth lines 0) "Content-Length: 5"
        && String.beq (fr_nth lines 1) "Content-Type: x"

#[test]
def test_a_single_header_region_is_one_line : Bool :=
    let lines : List String := framing_header_lines "Content-Length: 5" in
    I64.beq (fr_len lines) 1 && String.beq (fr_nth lines 0) "Content-Length: 5"

// --- MCP's newline-delimited framing ---

#[test]
def test_newline_delimited_splits_at_the_first_newline : Bool :=
    let r : FrameRead := framing_read FramingMode.newline_delimited "{\"a\":1}\n{\"b\":2}\n" in
    fr_body_is r "{\"a\":1}" && fr_rest_is r "{\"b\":2}\n"

#[test]
def test_newline_delimited_without_a_newline_asks_for_more : Bool :=
    is_need_more (framing_read FramingMode.newline_delimited "{\"a\":1}")

#[test]
def test_newline_delimited_drops_a_trailing_carriage_return : Bool :=
    fr_body_is (framing_read FramingMode.newline_delimited "{\"a\":1}\r\n") "{\"a\":1}"

// --- How much more is needed ---
//
// This is what makes the read loop one read per message instead of one per byte of
// it: `framing_needed` answers the outstanding byte count as soon as
// `Content-Length` has been read, and `Option.none` while the header itself is still
// arriving, which is the caller's signal to read a byte rather than a guess. Getting
// the first half wrong is invisible (the loop still works, just slowly), so it is
// pinned here rather than noticed later; getting the second half wrong would make a
// loop read a count that was invented.

/// The outstanding byte count, or -1 for "not known yet".
def fr_needed (mode : FramingMode) (buf : String) : I64 :=
    match framing_needed mode buf {
        Option.none => 0 - 1,
        Option.some n => n,
    }

#[test]
def test_needed_is_unknown_while_the_header_is_incomplete : Bool :=
    I64.beq (fr_needed FramingMode.content_length "Content-Len") (0 - 1)

/// "hello" with two of its five body bytes present.
#[test]
def test_needed_counts_the_body_bytes_still_outstanding : Bool :=
    I64.beq (fr_needed FramingMode.content_length "Content-Length: 5\r\n\r\nhe") 3

#[test]
def test_needed_is_the_whole_body_when_only_the_header_has_arrived : Bool :=
    I64.beq (fr_needed FramingMode.content_length "Content-Length: 5\r\n\r\n") 5

/// NEVER ZERO, and the floor is not cosmetic: `read_stdin_exact 0` answers the empty
/// string, which the server's loop reads as end of stream. A zero from here would end
/// a session in the middle of a message.
#[test]
def test_needed_is_never_zero_for_a_frame_that_is_already_complete : Bool :=
    I64.beq (fr_needed FramingMode.content_length (fr_lsp "{\"a\":1}")) 1

/// A newline-delimited frame has no declared length, so there is nothing to compute
/// and the caller reads until the newline arrives.
#[test]
def test_needed_is_unknown_for_newline_delimited : Bool :=
    I64.beq (fr_needed FramingMode.newline_delimited "{\"a\":1}") (0 - 1)
