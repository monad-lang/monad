/// Wire framing: turning an accumulated byte stream into whole messages,
/// for both protocols this toolkit's consumers speak.
///
/// LSP frames a message as `Content-Length: N\r\n\r\n` followed by exactly
/// N bytes of UTF-8 JSON. MCP frames it as one JSON value per line. The two
/// differ only in where a message ends, which is why they share one outcome
/// type rather than each growing their own reader.
///
/// THE READER IS A PURE FUNCTION OVER AN ACCUMULATED BUFFER, and that is not
/// a stylistic choice -- it is the whole reason this module exists. The
/// natural first implementation is a loop: `read a line`, `parse the headers
/// on it`, `read N more bytes`. It CANNOT survive a read that splits a
/// header. A stream hands back whatever it has, so `read` routinely returns
/// `"Content-Len"` with no newline anywhere in it, and a line-oriented reader
/// has no answer for "the buffer is a strict prefix of a header" -- it must
/// either block (never knowing how much more to ask for) or guess. The guess
/// that looks reasonable, treating the partial line as a whole line, drops a
/// message silently, and the failure shows up one request later as a
/// desynchronized stream that reads like a client bug.
///
/// Making the answer a VALUE removes the guess: `FrameRead.need_more` IS the
/// partial case, so the caller's loop is "append what arrived, ask again",
/// and there is nowhere for a partial frame to be lost. It also makes every
/// one of those cases testable without a socket, which is how the header-split
/// and terminator-inside-a-body tests below are written.
///
/// The second half of the same hazard is a `\r\n\r\n` INSIDE a JSON string
/// body -- entirely legal JSON, and a thing a client does the moment a user
/// types a blank line into a document. `content_length` mode therefore parses
/// the header first and then takes exactly the declared number of bytes; it
/// never searches the buffer for a terminator that a body could also match.
/// A reader that scanned for the terminator instead would split that message
/// in two, which is the same silent desynchronization by another route.
///
/// Case sensitivity of the header name: matched EXACTLY, as
/// `Content-Length:`. The LSP specification fixes that spelling and every
/// mainstream client emits it that way, so case folding would be code with no
/// caller. The choice is safe in the direction that matters -- a differently
/// cased header does not silently mis-parse, it comes back as
/// `FrameRead.bad_header`, which the server reports and logs.
///
/// HOW MUCH MORE TO ASK FOR IS ALSO A VALUE, in `framing_needed`, and it is
/// what keeps the caller's loop from costing a read per byte. The loop still
/// reads "append what arrived, ask again", but the native underneath reads to
/// a REQUESTED LENGTH rather than returning whatever is available, so a caller
/// that always asks for one byte turns a large message into hundreds of
/// syscalls while a caller that always asks for a large chunk blocks until the
/// peer fills it -- which for a request/response protocol is a deadlock.
/// `framing_needed` separates the two cases that the buffer state actually
/// distinguishes: `Option.none` while the header is still incomplete, and the
/// outstanding byte count once `Content-Length` is known, so the read is one
/// byte per header byte and then exactly the body in a single call.
///
/// It NEVER answers zero, and that is a correctness rule rather than a
/// rounding choice: an empty result IS the end-of-stream signal, so requesting
/// zero bytes would be indistinguishable from the peer closing the connection
/// and the caller would exit in the middle of a session. A frame that is
/// already complete therefore reports a floor of one, which the caller
/// re-examines before reading.
///
/// The reader loop itself lives with its consumer, `motes/lsp/src/server.mo`.

use toolkit::bytes {byte_cr, byte_lf, byte_space}

/// How far into a buffer a `Content-Length` header may extend before it is
/// treated as malformed rather than incomplete.
///
/// This is a bound on WORK, not a protocol limit, and it is why the header
/// scan can slice a window instead of converting the whole buffer: a real
/// header is under a hundred bytes, so a terminator past this point is a
/// broken peer (or something that is not speaking LSP at all), and reporting
/// `bad_header` immediately beats scanning a megabyte looking for one.
def header_window_max : I64 := 8192

/// The ten ASCII digits, in value order. `digit_value` indexes this.
def digit_chars : String := "0123456789"

def content_length_header : String := "Content-Length:"

/// Up to how large a `Content-Length` value is believed.
///
/// The accumulator folds digits into an `I64`, so without a cap a peer
/// declaring `Content-Length: 99999999999999999999` wraps the accumulator
/// around to a small or negative number and the frame is accepted with the
/// wrong length -- a desynchronization produced by a plausible typo rather
/// than an attack. Any real message is far under this.
def content_length_max : I64 := 100000000

/// Which framing a stream uses. The two are not negotiated; a server knows
/// which protocol it was started as.
///
/// The name is `FramingMode` rather than the obvious `Framing` on purpose, and
/// both halves of the reason are worth keeping. `motes/http/src/types.mo`
/// already declares a `Framing` -- a different type, about a response's body
/// length -- and it also names a constructor `content_length`, and it `open`s
/// it, so within any file that imports HTTP the bare name `content_length`
/// means HTTP's. Nothing compiles both motes today, which is why this is not
/// an error anywhere and why it would go unnoticed until it is not:
/// whole-program scope is shared, this repo has already lost an afternoon to
/// two same-named inductives that broke codegen elaboration, and the failure
/// flipped on module load order. The second half is that `mode` is what every
/// caller already calls this value, so the qualified name says what the type
/// is for rather than what module it happens to live in.
pub type FramingMode {
    content_length,
    newline_delimited,
}

/// The result of offering an accumulated buffer to `framing_read`.
///
/// `need_more` is a first-class answer rather than an error, because "the
/// buffer is a strict prefix of a frame" is the normal state of a stream that
/// has not finished delivering a message. `bad_header` is the opposite: the
/// frame ended where it should but its header is unusable, which no amount of
/// further reading fixes.
pub type FrameRead {
    need_more,
    frame (body : String) (rest : String),
    bad_header (reason : String),
}

// --- Byte-level helpers ---
//
// Everything here works on `List U8` from `String.to_list` rather than on
// `String.get`, for one reason: `String.get` is the O(1) byte read this would
// prefer, but it is not `pub` in `init/src/string.mo`, and reaching across
// motes for it draws a `cross_mote_package_private` warning on every check.
// The alternative is not `String.get_char`, which decodes the whole string
// into a `Vec<char>` on EVERY call and would make each of these loops
// quadratic (its own doc says so). The conversions here are bounded: the
// header scan converts at most `header_window_max` bytes, and the body is
// never converted at all -- its length comes from `String.length`.

def is_byte (o : Option U8) (b : U8) : Bool :=
    match o {
        Option.none => false,
        Option.some x => U8.beq x b,
    }

/// The digit `b` denotes, or -1 if it is not a digit.
///
/// A scan of `digit_chars` rather than `U8.sub b 48u8`, and the reason is
/// where the types stop. `U8.sub` IS `pub`, so the subtraction is available --
/// but it yields a `U8`, and there is no way to widen a `U8` into an `I64`
/// across a mote boundary: `U8` exposes `to_u64` and `to_u32` and neither is
/// `pub` (`init/src/number.mo:259`, `:262`). Indexing a ten-character string
/// answers the question directly, in the type the fold already accumulates.
///
/// (`U8.gt` IS `pub` where `U8.lt` is not, so a range test could have been
/// written here. It is not, because a range test gets no further than the
/// subtraction above -- the value still has to come out as an `I64`.)
#[partial]
def digit_value (b : U8) : I64 :=
    digit_value_go (String.to_list digit_chars) b 0

#[partial]
def digit_value_go (bs : List U8) (b : U8) (i : I64) : I64 :=
    match bs {
        List.empty => -1,
        List.cons x rest => if U8.beq x b then i else digit_value_go rest b (I64.add i 1),
    }

/// The index just past the first `\r\n\r\n` in `bs`, or -1 for none.
///
/// Written as one flat recursion carrying the three preceding bytes rather
/// than four nested matches, and the flattening is about how it compiles
/// rather than how it reads: the previous byte of the match is the only state
/// the search needs, so it travels as a parameter. `i` is the index of `b`,
/// which is why the answer is `i + 1` -- the position after the `\n` that
/// completes the terminator, which is also where the body begins.
#[partial]
def find_terminator (bs : List U8) (i : I64) (p1 : Option U8) (p2 : Option U8) (p3 : Option U8) : I64 :=
    match bs {
        List.empty => -1,
        List.cons b rest =>
            let hit : Bool :=
                is_byte p3 byte_cr && is_byte p2 byte_lf && is_byte p1 byte_cr && U8.beq b byte_lf
            in
            if hit
            then I64.add i 1
            else find_terminator rest (I64.add i 1) (Option.some b) p1 p2,
    }

/// The index of the first `\n` in `bs`, or `Option.none` for none.
#[partial]
def find_lf (bs : List U8) (i : I64) : Option I64 :=
    match bs {
        List.empty => Option.none,
        List.cons b rest =>
            if U8.beq b byte_lf then Option.some i else find_lf rest (I64.add i 1),
    }

/// Drop one trailing `\r` -- the carriage return of a line's `\r\n`.
def trim_cr (line : String) : String :=
    let n : I64 := String.length line in
    if I64.lt 0 n
    then
        if String.beq (String.slice line (n - 1) 1) "\r"
        then String.slice line 0 (n - 1)
        else line
    else line

// --- The `Content-Length` header ---

/// Reverse a list of header lines.
///
/// Local rather than `List.reverse`, and the reason is where the name lives:
/// `List.reverse` and `List.length` are defs in `std/src/list.mo`, and a
/// framing module that pulls in `std` for four lines of list reversal has
/// taken a dependency it will never use again. `init`'s `List` constructors
/// and `String` primitives are all this module needs, and keeping it that way
/// is what lets the tests below run against nothing but the prelude.
#[partial]
def framing_reverse_lines (ss : List String) (acc : List String) : List String :=
    match ss {
        List.empty => acc,
        List.cons s rest => framing_reverse_lines rest (List.cons s acc),
    }

/// Split a header region into its `\r\n`-separated lines.
///
/// Flat recursion carrying the current line's start index, for the same
/// reason `find_terminator` carries its previous byte: `start` is the only
/// state a split needs, and holding it explicitly keeps every arm a
/// single-level match. The region never contains a blank line -- it stops at
/// the `\r\n\r\n` that terminated it -- so an empty trailing element is not a
/// case here, and `trim_cr` handles the `\r` each line still carries.
#[partial]
pub def framing_header_lines (region : String) : List String :=
    header_lines_go region (String.to_list region) 0 0 List.empty

#[partial]
def header_lines_go (region : String) (bs : List U8) (i : I64) (start : I64) (acc : List String) : List String :=
    match bs {
        List.empty =>
            framing_reverse_lines (List.cons (trim_cr (String.slice region start (i - start))) acc) List.empty,
        List.cons b rest =>
            if U8.beq b byte_lf
            then
                header_lines_go region rest (I64.add i 1) (I64.add i 1)
                    (List.cons (trim_cr (String.slice region start (i - start))) acc)
            else header_lines_go region rest (I64.add i 1) start acc,
    }

/// The value of the `Content-Length` header, or `Option.none`.
///
/// Stops at the FIRST line carrying the name, including when that line's
/// value is unparseable. A file with the header twice is malformed, and
/// falling through to a second one would accept a message whose length two
/// parties disagree about -- which is the desynchronization this module is
/// built to avoid, arrived at from the other direction.
#[partial]
def find_content_length (lines : List String) : Option I64 :=
    match lines {
        List.empty => Option.none,
        List.cons l rest =>
            if String.starts_with content_length_header l
            then parse_len (String.drop (String.length content_length_header) l)
            else find_content_length rest,
    }

/// Every byte is a space.
#[partial]
def all_spaces (bs : List U8) : Bool :=
    match bs {
        List.empty => true,
        List.cons b rest => if U8.beq b byte_space then all_spaces rest else false,
    }

/// Read a decimal length out of everything after `Content-Length:`.
///
/// STRICT about what else the value may contain, which the caller's
/// consequences make non-negotiable rather than pedantic. Leading spaces are
/// skipped, then digits are folded, then only spaces may follow. A lenient
/// fold that stopped at the first non-digit would read `Content-Length: 0x10`
/// as 0 and take no bytes, leaving 16 bytes of body in the buffer to be
/// re-parsed as the next frame's header -- the desynchronization this module
/// exists to prevent, entered through a header nobody validated. So a
/// trailing non-digit is `Option.none`, and the caller reports it.
///
/// `started` distinguishes "no digit seen yet" from "the value so far is 0",
/// which is the one case a sentinel accumulator would get wrong:
/// `Content-Length: 0` is a legal empty body, and `Content-Length:` with
/// nothing after it is not a header at all.
///
/// The unconsumed tail travels out with the number so the caller can inspect
/// it: `Pair` rather than a second scan, because the fold already knows
/// exactly where the digits stopped.
#[partial]
def parse_len (value : String) : Option I64 :=
    match parse_len_go (String.to_list value) false 0 {
        Option.none => Option.none,
        Option.some p =>
            match p {
                Pair.pair n tail => if all_spaces tail then Option.some n else Option.none,
            },
    }

#[partial]
def parse_len_go (bs : List U8) (started : Bool) (acc : I64) : Option (Pair I64 (List U8)) :=
    match bs {
        List.empty => if started then Option.some (Pair.pair acc List.empty) else Option.none,
        List.cons b rest =>
            let d : I64 := digit_value b in
            if I64.lt d 0
            then
                if started
                then Option.some (Pair.pair acc bs)
                else parse_len_go rest false acc
            else
                if I64.gt acc content_length_max
                then Option.none
                else parse_len_go rest true (I64.add (I64.mul acc 10) d),
    }

// --- The two framings ---

/// Offer an accumulated buffer to the reader.
///
/// The contract every caller depends on: on `FrameRead.frame body rest`,
/// `rest` is the unconsumed remainder and MUST be fed back in, because a
/// client may pipeline. Dropping it loses every message that arrived in the
/// same read as this one -- a burst that a fast client produces routinely.
pub def framing_read (mode : FramingMode) (buf : String) : FrameRead :=
    match mode {
        FramingMode.content_length => read_content_length buf,
        FramingMode.newline_delimited => read_newline_delimited buf,
    }

#[partial]
def read_content_length (buf : String) : FrameRead :=
    let len : I64 := String.length buf in
    let window_len : I64 := if I64.lt len header_window_max then len else header_window_max in
    let window : String := String.slice buf 0 window_len in
    let after : I64 := find_terminator (String.to_list window) 0 Option.none Option.none Option.none in
    if I64.lt after 0
    then
        // No terminator anywhere in the window. Under the window size that is a
        // partial header and the answer is to wait; AT the window size the header
        // cannot grow into a legal one, so waiting would hang on a broken peer.
        if I64.lt len header_window_max
        then FrameRead.need_more
        else FrameRead.bad_header "no header terminator within the window"
    else frame_after_header buf after

/// Take the declared number of bytes after a located terminator.
///
/// `after` is the index just past the `\r\n\r\n`, so the header region is
/// exactly `[0, after - 4)` -- the four bytes of the terminator belong to
/// neither the header nor the body.
#[partial]
def frame_after_header (buf : String) (after : I64) : FrameRead :=
    let region : String := String.slice buf 0 (after - 4) in
    match find_content_length (framing_header_lines region) {
        Option.none => FrameRead.bad_header "missing or malformed Content-Length header",
        Option.some n =>
            if I64.lt (String.length buf) (I64.add after n)
            then FrameRead.need_more
            else
                FrameRead.frame
                    (String.slice buf after n)
                    (String.drop (I64.add after n) buf),
    }

/// A whole JSON value per line, which is MCP's framing.
///
/// The buffer is rescanned from the start on every call, so feeding this one
/// byte at a time is quadratic in the line's length. That is left alone
/// deliberately: unlike the header scan there is no bound to slice to, since
/// a legal message is however long it is, and the mode's messages are small
/// and arrive whole off a local pipe. A stream that never sends a newline
/// grows the buffer without limit, which is the protocol's own hazard -- MCP
/// messages may not contain a raw newline, so framing them is exactly what
/// this does and a peer that withholds one is the peer's bug.
#[partial]
def read_newline_delimited (buf : String) : FrameRead :=
    match find_lf (String.to_list buf) 0 {
        Option.none => FrameRead.need_more,
        Option.some i =>
            FrameRead.frame (trim_cr (String.slice buf 0 i)) (String.drop (I64.add i 1) buf),
    }

// --- How much more is needed ---

/// How many more bytes the buffer needs before it holds one whole frame, or
/// `Option.none` when that number is not yet known.
///
/// `framing_read` answering `need_more` covers two cases that cost a reader
/// very different numbers of reads, and telling them apart is the whole reason
/// this exists. A buffer whose HEADER is incomplete can only be extended by
/// reading more and asking again -- nothing in it says how long the header will
/// be -- so the honest read there is one byte, and the honest answer is
/// `Option.none`. A buffer whose header IS complete names exactly how many body
/// bytes are still outstanding, and the peer is going to send exactly that many,
/// so the reader can take them in ONE read. A stream loop that could not ask
/// this question would read a whole message one byte at a time, which is one
/// syscall per byte of every message the client sends.
///
/// NEVER ZERO, and the floor is not cosmetic: the caller's natural move is to
/// read exactly this many bytes, and `read_stdin_exact 0` returns the empty
/// string -- which is that native's end-of-stream signal. A zero here would make
/// a caller that has not reached the end of anything exit the loop. The floor is
/// 1 byte, which always either makes progress or reports the end truthfully.
///
/// `Option.none` for `newline_delimited`, deliberately: a line has no declared
/// length, so there is nothing to compute and a caller reads until the newline
/// arrives. It is also `Option.none` for a buffer that is already a frame or is
/// malformed, both of which `framing_read` answers on its own -- this is a
/// question a caller asks only after being told `need_more`.
#[partial]
pub def framing_needed (mode : FramingMode) (buf : String) : Option I64 :=
    match mode {
        FramingMode.content_length => needed_content_length buf,
        FramingMode.newline_delimited => Option.none,
    }

/// The same header scan `read_content_length` runs, stopping at the point where
/// the two cases diverge.
#[partial]
def needed_content_length (buf : String) : Option I64 :=
    let len : I64 := String.length buf in
    let window_len : I64 := if I64.lt len header_window_max then len else header_window_max in
    let window : String := String.slice buf 0 window_len in
    let after : I64 := find_terminator (String.to_list window) 0 Option.none Option.none Option.none in
    if I64.lt after 0
    then Option.none
    else needed_after_header buf after

#[partial]
def needed_after_header (buf : String) (after : I64) : Option I64 :=
    let region : String := String.slice buf 0 (after - 4) in
    match find_content_length (framing_header_lines region) {
        Option.none => Option.none,
        Option.some n =>
            let want : I64 := I64.sub (I64.add after n) (String.length buf) in
            if I64.lt want 1 then Option.some 1 else Option.some want,
    }

// --- Test-only helpers ---
//
// The outcome type carries two payloads on one constructor and a reason
// string on another, so a test cannot pattern-match its way to a body
// without nesting differently-typed arms. These flatten it instead.

/// The body of a completed frame, or `Option.none` for either other outcome.
pub def frame_body (r : FrameRead) : Option String :=
    match r {
        FrameRead.need_more => Option.none,
        FrameRead.frame body _rest => Option.some body,
        FrameRead.bad_header _reason => Option.none,
    }

/// What is left after a completed frame, or `Option.none` for either other
/// outcome.
pub def frame_rest (r : FrameRead) : Option String :=
    match r {
        FrameRead.need_more => Option.none,
        FrameRead.frame _body rest => Option.some rest,
        FrameRead.bad_header _reason => Option.none,
    }

/// The reason a header was rejected, or `Option.none` for either other
/// outcome.
pub def frame_reason (r : FrameRead) : Option String :=
    match r {
        FrameRead.need_more => Option.none,
        FrameRead.frame _body _rest => Option.none,
        FrameRead.bad_header reason => Option.some reason,
    }

pub def is_need_more (r : FrameRead) : Bool :=
    match r {
        FrameRead.need_more => true,
        FrameRead.frame _body _rest => false,
        FrameRead.bad_header _reason => false,
    }
