// Terminal UI Library - Input decoding (Phase 6)
//
// The pure half of event handling: `Input.decode` turns a byte string
// from stdin into a list of `Event`s, or as much of one as is complete.
// Everything here is a pure function of the buffer -- the tests feed
// wire strings and assert decoded events -- because the terminal-side
// state (how many bytes arrived in one chunk, whether more are coming)
// is the READER's business, not the decoder's.
//
// The split the two halves agree on: `decode` never guesses. A sequence
// that might still be completed by the next chunk (a lone ESC, a CSI
// the final byte of which has not arrived, a character split by a chunk
// boundary) is returned in the LEFTOVER, and the reader feeds it back
// prefixed to the next chunk. `Input.pending_escape` is the one thing
// the reader itself decides: an ESC still alone when a poll times out is
// the ESC key, because a terminal sends a whole escape sequence in one
// burst.
//
// Wire shapes handled: single printable and control bytes, UTF-8
// characters, CSI sequences (arrows, home/end, the `~` keypad table,
// SGR mouse reports), SS3 sequences (F1-F4, home/end) and ESC+char
// alt keys. Modifier parameters (`ESC [ 1;5 A`) are recognized and
// ignored -- the unmodified key is reported. Sequences that parse but
// name nothing this mote knows (legacy mouse encodings, kitty `u`
// reports) are consumed and dropped, never stalled on.
//
// Strings are walked BYTES-first: `Input.byte_at` gives a one-byte
// string when the byte is ASCII and "" at a multi-byte character, so
// every ASCII comparison (the whole escape-sequence grammar) is a plain
// string compare and UTF-8 needs no numeric byte access.

use lib::types { Event, Key, MouseButton, MouseEvent }
use lib::terminal { Terminal.poll, Terminal.size }
use std::io { IO.read_stdin_exact }

// ==================== byte and character probes ====================

/// The byte at `i` as a one-character string when it stands alone (an
/// ASCII byte); "" when `i` sits inside a multi-byte character or past
/// the end. Every ASCII byte of the escape grammar is a one-byte
/// string, which is what makes the whole decoder string compares.
def Input.byte_at (s : String) (i : I64) : String := String.slice s i 1

/// The character at byte offset `i` and its byte length, by probing
/// UTF-8's whole 1-4 byte range: the first probe that lands on a whole
/// character is the character (`String.slice` returns "" for any cut
/// that is not on a character boundary, and clamps at the end). A
/// length of 0 means no valid character starts at `i` -- either the
/// buffer ends mid-character (wait for the next chunk) or the bytes are
/// not UTF-8 at all (poison; the walk drops one byte).
def Input.char_at (s : String) (i : I64) : Pair String I64 :=
    if String.length (String.slice s i 1) > 0 then Pair.pair (String.slice s i 1) 1
    else if String.length (String.slice s i 2) > 0 then Pair.pair (String.slice s i 2) 2
    else if String.length (String.slice s i 3) > 0 then Pair.pair (String.slice s i 3) 3
    else if String.length (String.slice s i 4) > 0 then Pair.pair (String.slice s i 4) 4
    else Pair.pair "" 0

/// The value of a one-character digit string, else `none`.
def Input.digit_val (c : String) : Option I64 :=
    if c == "0" then Option.some 0
    else if c == "1" then Option.some 1
    else if c == "2" then Option.some 2
    else if c == "3" then Option.some 3
    else if c == "4" then Option.some 4
    else if c == "5" then Option.some 5
    else if c == "6" then Option.some 6
    else if c == "7" then Option.some 7
    else if c == "8" then Option.some 8
    else if c == "9" then Option.some 9
    else Option.none

// ==================== parameter parsing ====================

/// The digit run starting at `i`: its value and the offset just past
/// it. `none` when no digit sits at `i` (a CSI sequence with no
/// parameters, like `ESC [ A`, is legal).
def Input.parse_digits (s : String) (i : I64) : Pair (Option I64) I64 :=
    match Input.digit_val (Input.byte_at s i) {
        Option.none => Pair.pair Option.none i,
        Option.some d => Input.parse_digits_go s (i + 1) d
    }

#[terminating]
def Input.parse_digits_go (s : String) (i : I64) (acc : I64) : Pair (Option I64) I64 :=
    match Input.digit_val (Input.byte_at s i) {
        Option.none => Pair.pair (Option.some acc) i,
        Option.some d => Input.parse_digits_go s (i + 1) (acc * 10 + d)
    }

/// The offset of the first byte from `i` that is neither a digit nor
/// `;` -- the final byte of a CSI sequence. Parameters are exactly
/// digits and separators, so anything else terminates the sequence.
#[terminating]
def Input.skip_params (s : String) (i : I64) : I64 :=
    match Input.digit_val (Input.byte_at s i) {
        Option.some _ => Input.skip_params s (i + 1),
        Option.none =>
            if Input.byte_at s i == ";"
            then Input.skip_params s (i + 1)
            else i
    }

// ==================== key tables ====================

/// The `Key` for a lone control byte. Bytes 0x08/0x09/0x0d/0x7f are
/// handled by the walk itself (backspace/tab/enter/backspace), so this
/// table covers the rest of 0x01-0x1a: `ctrl` plus the letter the byte
/// spells with bit 0x40 set. Ctrl-h/i/m are therefore unreachable --
/// they ARE backspace/tab/enter on this wire, the same trade crossterm
/// makes.
def Input.control_key (c : String) : Option Key :=
    if c == "\u{1}" then Option.some (Key.ctrl "a")
    else if c == "\u{2}" then Option.some (Key.ctrl "b")
    else if c == "\u{3}" then Option.some (Key.ctrl "c")
    else if c == "\u{4}" then Option.some (Key.ctrl "d")
    else if c == "\u{5}" then Option.some (Key.ctrl "e")
    else if c == "\u{6}" then Option.some (Key.ctrl "f")
    else if c == "\u{7}" then Option.some (Key.ctrl "g")
    else if c == "\u{a}" then Option.some (Key.ctrl "j")
    else if c == "\u{b}" then Option.some (Key.ctrl "k")
    else if c == "\u{c}" then Option.some (Key.ctrl "l")
    else if c == "\u{e}" then Option.some (Key.ctrl "n")
    else if c == "\u{f}" then Option.some (Key.ctrl "o")
    else if c == "\u{10}" then Option.some (Key.ctrl "p")
    else if c == "\u{11}" then Option.some (Key.ctrl "q")
    else if c == "\u{12}" then Option.some (Key.ctrl "r")
    else if c == "\u{13}" then Option.some (Key.ctrl "s")
    else if c == "\u{14}" then Option.some (Key.ctrl "t")
    else if c == "\u{15}" then Option.some (Key.ctrl "u")
    else if c == "\u{16}" then Option.some (Key.ctrl "v")
    else if c == "\u{17}" then Option.some (Key.ctrl "w")
    else if c == "\u{18}" then Option.some (Key.ctrl "x")
    else if c == "\u{19}" then Option.some (Key.ctrl "y")
    else if c == "\u{1a}" then Option.some (Key.ctrl "z")
    else Option.none

/// The `Key` for a CSI `n ~` code: the vt-style keypad and function-key
/// reports. Two numbers sometimes mean one key (xterm's `1~` and
/// `7~` are both home), and there are no F13+ keys to report.
def Input.tilde_key (n : I64) : Option Key :=
    if n == 1 then Option.some Key.home
    else if n == 2 then Option.some Key.insert
    else if n == 3 then Option.some Key.delete
    else if n == 4 then Option.some Key.end
    else if n == 5 then Option.some Key.page_up
    else if n == 6 then Option.some Key.page_down
    else if n == 7 then Option.some Key.home
    else if n == 8 then Option.some Key.end
    else if n == 11 then Option.some (Key.function_key 1)
    else if n == 12 then Option.some (Key.function_key 2)
    else if n == 13 then Option.some (Key.function_key 3)
    else if n == 14 then Option.some (Key.function_key 4)
    else if n == 15 then Option.some (Key.function_key 5)
    else if n == 17 then Option.some (Key.function_key 6)
    else if n == 18 then Option.some (Key.function_key 7)
    else if n == 19 then Option.some (Key.function_key 8)
    else if n == 20 then Option.some (Key.function_key 9)
    else if n == 21 then Option.some (Key.function_key 10)
    else if n == 23 then Option.some (Key.function_key 11)
    else if n == 24 then Option.some (Key.function_key 12)
    else Option.none

/// The `MouseButton` for an SGR mouse button code (0 left, 1 middle,
/// 2 right -- the wire's own order, not a sort).
def Input.mouse_button (b : I64) : Option MouseButton :=
    if b == 0 then Option.some MouseButton.left
    else if b == 1 then Option.some MouseButton.middle
    else if b == 2 then Option.some MouseButton.right
    else Option.none

/// The `Event` for an SGR mouse report: `ESC [ < b ; col+1 ; row+1 M`
/// (press, drag or wheel) or `... m` (release). Button codes 0/1/2 are
/// presses, 32-34 are drags of the same buttons, 64/65 are the wheel,
/// and release keeps the press's button code with the `m` final.
/// Coordinates arrive 1-based; the mote's convention is 0-based.
def Input.mouse_event (b : I64) (col : I64) (row : I64) (release : Bool) : Option Event :=
    if release
    then match Input.mouse_button b {
        Option.some btn => Option.some (Event.mouse (MouseEvent.release btn row col)),
        Option.none => Input.mouse_press_event b col row
    }
    else Input.mouse_press_event b col row

def Input.mouse_press_event (b : I64) (col : I64) (row : I64) : Option Event :=
    if b == 64 then Option.some (Event.mouse (MouseEvent.scroll_up row col))
    else if b == 65 then Option.some (Event.mouse (MouseEvent.scroll_down row col))
    else if b == 32 || b == 33 || b == 34
    then match Input.mouse_button (b - 32) {
        Option.some btn => Option.some (Event.mouse (MouseEvent.drag btn row col)),
        Option.none => Option.none
    }
    else match Input.mouse_button b {
        Option.some btn => Option.some (Event.mouse (MouseEvent.press btn row col)),
        Option.none => Option.none
    }

// ==================== the walk ====================

/// Reverse an event list accumulated during the walk (`List.reverse`
/// is package-private in `init`, and this is the only list this file
/// needs turned around).
def Input.rev (l : List Event) (out : List Event) : List Event :=
    match l {
        empty => out,
        cons e t => Input.rev t (List.cons e out)
    }

/// Decode every complete event in `buf`. The second component is the
/// leftover: a trailing byte sequence too incomplete to name yet, which
/// the caller feeds back to the next call prefixed to the next chunk.
pub def Input.decode (buf : String) : Pair (List Event) String :=
    match Input.walk buf 0 List.empty {
        Pair.pair evs stop => Pair.pair evs (String.drop stop buf)
    }

/// Whether `leftover` is a bare ESC with nothing after it. The reader
/// resolves the one ambiguity `decode` refuses to: a terminal sends an
/// escape SEQUENCE in one burst, so an ESC still alone when a poll
/// times out is the ESC key.
pub def Input.pending_escape (leftover : String) : Bool :=
    String.length leftover == 1 && String.slice leftover 0 1 == "\u{1b}"

/// Walk `s` from byte offset `i`, accumulating events (reversed, so
/// the head is the most recent) and returning the offset where
/// decoding stopped: the end of the buffer, or the start of an
/// incomplete sequence, which `decode` keeps as the leftover.
#[terminating]
def Input.walk (s : String) (i : I64) (acc : List Event) : Pair (List Event) I64 :=
    if Bool.not (i < String.length s)
    then Pair.pair (Input.rev acc List.empty) i
    else
        let c := Input.byte_at s i in
        if c == "\u{1b}"
        then Input.escape_next s (i + 1) i acc
        else if c == "\r" || c == "\n"
        then Input.walk s (i + 1) (List.cons (Event.key Key.enter) acc)
        else if c == "\t"
        then Input.walk s (i + 1) (List.cons (Event.key Key.tab) acc)
        else if c == "\u{7f}" || c == "\u{8}"
        then Input.walk s (i + 1) (List.cons (Event.key Key.backspace) acc)
        // The `""` (mid-character) test MUST precede the NUL test: the
        // compiled runtime's strings are NUL-terminated `char*`, so a
        // `"\u{0}"` literal IS the empty string there and the tests
        // would be indistinguishable -- a mid-character `""` would be
        // swallowed by the NUL-drop branch and multi-byte input would
        // silently vanish. Interpreted, a real NUL byte slices to a
        // one-byte string that is not `""`, so this order drops NULs
        // exactly as before.
        else if c == ""
        then Input.utf8_next s i acc
        else if c == "\u{0}"
        then Input.walk s (i + 1) acc
        else match Input.control_key c {
            Option.some k => Input.walk s (i + 1) (List.cons (Event.key k) acc),
            Option.none => Input.walk s (i + 1) (List.cons (Event.key (Key.char c)) acc)
        }

/// A byte 0x80 or higher: a UTF-8 character (an ordinary `Key.char`,
/// one to four bytes wide), a partial character the next chunk may
/// finish, or poison. Poison is the only case with no ceiling: if four
/// bytes were not enough for a character, dropping one byte and
/// resynchronizing beats stalling.
#[terminating]
def Input.utf8_next (s : String) (i : I64) (acc : List Event) : Pair (List Event) I64 :=
    match Input.char_at s i {
        Pair.pair ch n =>
            if n > 0
            then Input.walk s (i + n) (List.cons (Event.key (Key.char ch)) acc)
            else if String.length s - i > 3
            then Input.walk s (i + 1) acc
            else Pair.pair (Input.rev acc List.empty) i
    }

/// An ESC at `i`; `k` is the offset after it. `esc_start` rides along
/// so an incomplete sequence can be left unconsumed from its very
/// first byte.
#[terminating]
def Input.escape_next (s : String) (k : I64) (esc_start : I64) (acc : List Event) : Pair (List Event) I64 :=
    if Bool.not (k < String.length s)
    then Pair.pair (Input.rev acc List.empty) esc_start
    else
        let c := Input.byte_at s k in
        if c == "["
        then Input.csi_walk s (k + 1) esc_start acc
        else if c == "O"
        then Input.ss3_walk s (k + 1) esc_start acc
        else if c == "\u{1b}"
        then Input.walk s k (List.cons (Event.key Key.escape) acc)
        else if c == ""
        then match Input.char_at s k {
            Pair.pair ch n =>
                if n > 0
                then Input.walk s (k + n) (List.cons (Event.key (Key.alt ch)) acc)
                else Pair.pair (Input.rev acc List.empty) esc_start
        }
        else Input.walk s (k + 1) (List.cons (Event.key (Key.alt c)) acc)

/// A CSI sequence (`ESC [`) with its first byte at `j`. Malformed or
/// incomplete reports stop the walk at `esc_start` -- the leftover
/// keeps the whole sequence until more bytes arrive or the reader
/// flushes it.
#[terminating]
def Input.csi_walk (s : String) (j : I64) (esc_start : I64) (acc : List Event) : Pair (List Event) I64 :=
    if Bool.not (j < String.length s)
    then Pair.pair (Input.rev acc List.empty) esc_start
    else match Input.csi_next s j {
        Pair.pair ev_o next_o =>
        match next_o {
            Option.none => Pair.pair (Input.rev acc List.empty) esc_start,
            Option.some next => match ev_o {
                Option.some ev => Input.walk s next (List.cons ev acc),
                Option.none => Input.walk s next acc
            }
        }
    }

/// An SS3 sequence (`ESC O` key) with its letter at `k`. Every SS3
/// letter this mote knows is one byte, so the whole sequence is always
/// complete once the letter is there; unknown letters are consumed
/// and dropped.
#[terminating]
def Input.ss3_walk (s : String) (k : I64) (esc_start : I64) (acc : List Event) : Pair (List Event) I64 :=
    if Bool.not (k < String.length s)
    then Pair.pair (Input.rev acc List.empty) esc_start
    else
        let c := Input.byte_at s k in
        let ev : Option Event :=
            if c == "P" then Option.some (Event.key (Key.function_key 1))
            else if c == "Q" then Option.some (Event.key (Key.function_key 2))
            else if c == "R" then Option.some (Event.key (Key.function_key 3))
            else if c == "S" then Option.some (Event.key (Key.function_key 4))
            else if c == "H" then Option.some (Event.key Key.home)
            else if c == "F" then Option.some (Event.key Key.end)
            else Option.none in
        match ev {
            Option.some e => Input.walk s (k + 1) (List.cons e acc),
            Option.none => Input.walk s (k + 1) acc
        }

/// One CSI sequence starting after the `ESC [` (offset `j`): its event
/// (`none` = consumed but not reported -- an unknown sequence is
/// dropped, never stalled on) and the offset past its final byte
/// (`none` = the buffer ends mid-sequence).
def Input.csi_next (s : String) (j : I64) : Pair (Option Event) (Option I64) :=
    if Input.byte_at s j == "<"
    then Input.mouse_next s (j + 1)
    else Input.key_next s j

/// A key CSI sequence (no `<`): skip the parameter bytes, then the
/// final byte names the key. The leading digits feed the `~` table;
/// every other final ignores them, which is what drops modifiers.
def Input.key_next (s : String) (j : I64) : Pair (Option Event) (Option I64) :=
    let fin := Input.skip_params s j in
    if Bool.not (fin < String.length s)
    then Pair.pair Option.none Option.none
    else
        let c := Input.byte_at s fin in
        if c == ""
        then Pair.pair Option.none Option.none
        else
            let ev : Option Event :=
                if c == "A" then Option.some (Event.key Key.up)
                else if c == "B" then Option.some (Event.key Key.down)
                else if c == "C" then Option.some (Event.key Key.right)
                else if c == "D" then Option.some (Event.key Key.left)
                else if c == "H" then Option.some (Event.key Key.home)
                else if c == "F" then Option.some (Event.key Key.end)
                else if c == "Z" then Option.some (Event.key Key.tab)
                else if c == "~" then Input.tilde_event s j
                else Option.none in
            Pair.pair ev (Option.some (fin + 1))

def Input.tilde_event (s : String) (j : I64) : Option Event :=
    match Input.parse_digits s j {
        Pair.pair n_o _ =>
        match n_o {
            Option.none => Option.none,
            Option.some n => match Input.tilde_key n {
                Option.some k => Option.some (Event.key k),
                Option.none => Option.none
            }
        }
    }

/// An SGR mouse report after `ESC [ <` (offset `k`): strictly
/// `b ; col ; row final`. Anything else on the wire is malformed --
/// stop and let the reader's flush resolve it.
def Input.mouse_next (s : String) (k : I64) : Pair (Option Event) (Option I64) :=
    match Input.parse_digits s k {
        Pair.pair b_o k2 =>
        match b_o {
            Option.none => Pair.pair Option.none Option.none,
            Option.some b =>
            if Bool.not (Input.byte_at s k2 == ";")
            then Pair.pair Option.none Option.none
            else match Input.parse_digits s (k2 + 1) {
                Pair.pair x_o k3 =>
                match x_o {
                    Option.none => Pair.pair Option.none Option.none,
                    Option.some x =>
                    if Bool.not (Input.byte_at s k3 == ";")
                    then Pair.pair Option.none Option.none
                    else match Input.parse_digits s (k3 + 1) {
                        Pair.pair y_o k4 =>
                        match y_o {
                            Option.none => Pair.pair Option.none Option.none,
                            Option.some y =>
                            let fin := Input.byte_at s k4 in
                            if fin == "M" || fin == "m"
                            then Pair.pair
                                (Input.mouse_event b (x - 1) (y - 1) (fin == "m"))
                                (Option.some (k4 + 1))
                            else Pair.pair Option.none Option.none
                        }
                    }
                }
            }
        }
    }

// ==================== the reader (pull model) ====================
//
// The plan's "event reader fiber" lands as a PULL producer instead: the
// app loop is the single scheduler, one `Input.produce` call is one
// poll/read/decode cycle, and the reader's state (undecoded bytes, the
// last observed size, whether stdin closed) is ordinary data threaded
// through the loop. That resolves the `Mailbox` open item for v1 -- no
// synchronized cross-fiber primitive exists in the stdlib and a native
// one buys nothing a pull cannot, because nothing else writes into a
// TUI's event graph.

/// The reader's state between polls. `closed` is set the first time a
/// read reports EOF (a poll says "readable" at EOF; the empty read is
/// what means closed), and a closed reader never yields events again.
pub struct InputReader {
    pending : String,
    last_rows : I64,
    last_cols : I64,
    closed : Bool
}

/// A reader that knows the terminal is `rows` x `cols` (so the first
/// `produce` does not mistake the current size for a resize) and has
/// consumed nothing.
pub def input_reader (rows : I64) (cols : I64) : InputReader :=
    { pending := "", last_rows := rows, last_cols := cols, closed := false }

/// Record `size` against the reader's last observation: the resize
/// event (one, on the change) and the reader that now knows it.
def Input.note_size (r : InputReader) (size : Pair I64 I64) : Pair (List Event) InputReader :=
    match size {
        Pair.pair rows cols =>
            if rows == r.last_rows && cols == r.last_cols
            then Pair.pair List.empty r
            else
                let nr : InputReader := { r with last_rows := rows, last_cols := cols } in
                Pair.pair (List.cons (Event.resize rows cols) List.empty) nr
    }

/// One poll/read/decode cycle. Waits up to `timeout_ms` for input;
/// when it arrives, reads and decodes until the buffer is drained (a
/// non-blocking poll between bytes). A resize is folded in front of
/// whatever input arrived. The timeout is the tick source -- it is how
/// an app's frame clock runs when no key is pressed -- and the one
/// other thing it yields is the ESC-key resolution: a lone ESC still
/// pending when no byte followed it is the escape key.
///
/// The caller threads the returned reader into the next call; on
/// `closed` it should stop the loop.
pub def Input.produce (r : InputReader) (timeout_ms : I64) : IO (Pair (List Event) InputReader) := do {
    let size <- Terminal.size;
    let sized : Pair (List Event) InputReader := Input.note_size r size;
    let out <- Input.produce_go sized timeout_ms;
    return out
}

def Input.produce_go (sized : Pair (List Event) InputReader) (timeout_ms : I64) : IO (Pair (List Event) InputReader) :=
    match sized {
        Pair.pair evs nr => do {
            let readable <- Terminal.poll timeout_ms;
            if Bool.not readable
            then Input.idle_cycle nr evs
            else Input.drain nr evs 256
        }
    }

/// The pending-turn cycle: everything `produce` does EXCEPT the read.
/// Soundness, not a style choice -- see tui.mo's header. While an async
/// turn runs, its modal overlay is the only stdin reader on the fiber's
/// thread, so the loop must not read the same fd: a second reader both
/// races the overlay for every byte and, having lost a poll wake, would
/// block the whole UI inside `read_stdin_exact` (a blocking read).
/// Bytes typed mid-turn therefore stay in the tty, and the first normal
/// `produce` after the turn drains them -- the same buffering the
/// synchronous loop already had. A readable-but-unread poll still
/// yields the tick (the frame clock keeps animating the spinner rather
/// than spinning a no-op cycle hot).
pub def Input.produce_poll_only (r : InputReader) (timeout_ms : I64) : IO (Pair (List Event) InputReader) := do {
    let size <- Terminal.size;
    let sized : Pair (List Event) InputReader := Input.note_size r size;
    let out <- Input.poll_only_go sized timeout_ms;
    return out
}

def Input.poll_only_go (sized : Pair (List Event) InputReader) (timeout_ms : I64) : IO (Pair (List Event) InputReader) :=
    match sized {
        Pair.pair evs nr => do {
            // Paces the cycle and observes resizes exactly as `produce`
            // would; the readable result is deliberately ignored (the
            // bytes belong to the turn fiber's reader).
            Terminal.poll timeout_ms;
            Input.idle_cycle nr evs
        }
    }

/// The timeout path: no input arrived, which IS the frame clock -- a
/// `tick` event rides the batch (apps that want no ticks poll with a
/// negative timeout and never get here). A pending lone ESC resolves
/// first and suppresses that cycle's tick: the escape key IS the
/// batch's event.
def Input.idle_cycle (r : InputReader) (evs : List Event) : IO (Pair (List Event) InputReader) := do {
    if Input.pending_escape r.pending
    then do {
        let nr : InputReader := { r with pending := "" };
        return (Pair.pair (List.append evs [Event.key Key.escape]) nr)
    }
    else return (Pair.pair (List.append evs [Event.tick]) r)
}

/// The readable path: read one byte at a time until the non-blocking
/// poll says nothing is left, decoding against `r.pending` as bytes
/// arrive. `budget` bounds a paste; EOF (an empty read) closes the
/// reader. The events accumulate in order after `evs`.
#[terminating]
def Input.drain (r : InputReader) (evs : List Event) (budget : I64) : IO (Pair (List Event) InputReader) :=
    if Bool.not (budget > 0)
    then do { return (Pair.pair evs r) }
    else do {
        let chunk <- IO.read_stdin_exact 1;
        if String.length chunk == 0
        then do {
            let nr : InputReader := { r with closed := true };
            return (Pair.pair evs nr)
        }
        else do {
            let readable <- Terminal.poll 0;
            match Input.decode (r.pending ++ chunk) {
                Pair.pair new_evs leftover => do {
                    let nr : InputReader := { r with pending := leftover };
                    if Bool.not readable
                    then return (Pair.pair (List.append evs new_evs) nr)
                    else Input.drain nr (List.append evs new_evs) (budget - 1)
                }
            }
        }
    }
