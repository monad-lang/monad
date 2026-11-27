/// The input side of the parser: what a parser consumes, and the class that
/// lets one grammar run over more than one representation.
///
/// A parser is `S -> ParseResult S A` for some cursor `S`; this module
/// defines the class `Input S` those cursors satisfy, and the two cursors the
/// tree uses: `Text` (a `String` suffix plus its absolute byte offset) and
/// `Bytes` (a window over a `Shared (Buf U8)`).
///
/// ## Why a cursor and not a bare suffix
///
/// The old parser threaded a raw `String` suffix, which made every position
/// question a `strlen`: `furthest_error` compared two `strlen`s per failed
/// alternative and `take_while` subtracted two per token, both O(remaining
/// input) in a compiled binary. A cursor carries its absolute `pos`, so
/// `input_offset` is a field read and every error-position comparison is O(1).
///
/// ## Why `Text` still holds a suffix
///
/// Compiled `String.drop n` is O(1)-ish (a pointer add), while `String.get s i`
/// for `i != 0` is O(i) (`memchr` for the terminator). So the cursor keeps the
/// *current suffix* — `s` is always the bytes starting at `pos` — and the scan
/// loops walk it one byte at a time. `end` is the absolute end of the region
/// being parsed (the source's byte length, or a bounded slice's end); it is
/// what makes `input_len` O(1). Invariant: `String.length s == end - pos` for
/// an unbounded cursor, and `String.length s >= end - pos` for a bounded one
/// (`input_slice`).
///
/// ## The bulk methods are the point
///
/// `input_scan` and `input_starts_with` are class methods so that the loop
/// lives in the INSTANCE: text walks a `String` pointer, bytes indexes a
/// `Buf`, and neither pays a dictionary call per byte. Everything a grammar
/// needs per token (`input_head`, `input_advance`, `input_text`) is O(1) or
/// O(token).
use std::buf {Buf}
use lib::char_preds {byte_at}

/// A cursor over text: `s` is the suffix at absolute byte `pos`, `end` is the
/// absolute end of the region. Construct with `Text.of_string` (a whole
/// source) or `Text.at_offset` (a position with no bytes behind it, as an
/// error carries).
pub struct Text {
    s : String,
    pos : I64,
    end : I64,
}

/// `String` is `Copy` and both integers are, so duplicating the cursor is
/// honest (pointer + two ints; no bytes are copied).
pub instance Copy Text {
    def copy (t : Text) : Pair Text Text := Pair.pair t t
}

/// A whole source as a text cursor: one `strlen`, at entry, and never again.
pub def Text.of_string (s : String) : Text :=
    let t : Text := { s := s, pos := 0, end := String.length s } in t

/// A position with nothing behind it. What an error built by a generic
/// combinator (`parse_error_at`) carries: the OFFSET is exact, the suffix is
/// empty, so diagnostics are right and resuming from such an error would
/// restart at end-of-input. Text combinators (`tag`, `many1`'s caller) build
/// their errors from a real cursor instead.
pub def Text.at_offset (off : I64) : Text :=
    let t : Text := { s := "", pos := off, end := off } in t

/// A zero-copy window over a binary buffer. `b` is the whole buffer, `pos`
/// the absolute offset of the cursor, `end` the absolute end of the region.
pub struct Bytes {
    b : Shared (Buf U8),
    pos : I64,
    end : I64,
}

/// `Shared` duplicates the read handle, not the buffer.
pub instance Copy Bytes {
    def copy (s : Bytes) : Pair Bytes Bytes := Pair.pair s s
}

/// The whole of `b` as a binary cursor.
pub def Bytes.of_buf (b : Shared (Buf U8)) : Bytes :=
    let s : Bytes := { b := b, pos := 0, end := Buf.length b } in s

/// A window `[from, to)` over the same buffer -- how a section's or a string
/// table's contents are re-parsed without copying.
pub def Bytes.at (s : Bytes) (from : I64) (to : I64) : Bytes :=
    let w : Bytes := { b := s.b, pos := from, end := to } in w

// ─── the class ───────────────────────────────────────────────────────

pub class Input (S : Type) {
    /// Bytes left in the region.
    def input_len (s : S) : I64
    /// Absolute byte offset of the cursor in its source.
    def input_offset (s : S) : I64
    /// The byte at the cursor, or `none` at end of region.
    def input_head (s : S) : Option U8
    /// The byte `n` bytes after the cursor. O(1) for `Bytes`; O(n) for
    /// `Text` (`String.get`'s `memchr`), so only fixed-width READERS use it.
    def input_byte_at (n : I64) (s : S) : Option U8
    /// Move the cursor forward `n` bytes, clamped to the region.
    def input_advance (n : I64) (s : S) : S
    /// A bounded cursor over the next `n` bytes, without moving. Zero copy,
    /// and an over-long `n` clamps.
    def input_slice (n : I64) (s : S) : S
    /// How many leading bytes satisfy `pred`. The loop lives in the
    /// instance, so it is one call per RUN, never one per byte.
    def input_scan (pred : U8 -> Bool) (s : S) : I64
    /// The next `n` bytes as a `String`, clamped. Text slices; bytes decode
    /// (lossily for invalid UTF-8, which only tags and error previews ever
    /// need).
    def input_text (n : I64) (s : S) : String
    /// Whether the next bytes are exactly `lit`. Text uses the
    /// `String.starts_with` native (no allocation); bytes compare a copy.
    def input_starts_with (lit : String) (s : S) : Bool
}

/// Total for every cursor: no bytes left.
pub def Input.at_end [Input S] {S : Type} (s : S) : Bool :=
    I64.beq (Input.input_len s) 0

// ─── Text instance ───────────────────────────────────────────────────

/// The remaining bytes under a cursor, clamped at zero (a cursor built from
/// inconsistent public fields cannot make this negative).
pub def Text.remaining (t : Text) : I64 :=
    if I64.lt t.pos t.end then t.end - t.pos else 0

/// The cursor's absolute byte offset -- a field read, which is what replaced
/// the `strlen` every position comparison used to pay.
pub def Text.offset (t : Text) : I64 := t.pos

/// The cursor's remaining bytes as a `String` -- for the call sites that
/// hand the remainder back to code that still speaks `String`.
pub def Text.rest (t : Text) : String :=
    String.slice t.s 0 (Text.remaining t)

/// `min n (Text.remaining t)`, floored at 0.
def text_clamp (t : Text) (n : I64) : I64 :=
    if I64.lt n 0 then 0
    else if I64.gt n (Text.remaining t) then Text.remaining t
    else n

/// Count leading bytes matching `pred`, walking the suffix a byte at a time.
///
/// Deliberately a flat `if`/`else` chain with the self-call as one arm's
/// whole body: `apply_self_tco` (`lang/codegen/emit.mo`) rewrites only
/// self-recursion, so any other shape costs a native stack frame per byte.
#[partial]
def scan_text_go (pred : U8 -> Bool) (s : String) (n : I64) (limit : I64) : I64 :=
    if not (I64.lt n limit)
    then n
    else if pred (byte_at s 0)
    then scan_text_go pred (String.drop 1 s) (n + 1) limit
    else n

pub instance Input Text {
    def input_len (t : Text) : I64 := Text.remaining t
    def input_offset (t : Text) : I64 := t.pos
    def input_head (t : Text) : Option U8 :=
        if not (I64.lt t.pos t.end) then Option.none else String.get t.s 0
    def input_byte_at (n : I64) (t : Text) : Option U8 :=
        if I64.lt n 0 then Option.none
        else if not (I64.lt n (Text.remaining t)) then Option.none
        else String.get t.s n
    def input_advance (n : I64) (t : Text) : Text :=
        let m : I64 := text_clamp t n in
        let r : Text := { s := String.drop m t.s, pos := t.pos + m, end := t.end } in r
    def input_slice (n : I64) (t : Text) : Text :=
        let m : I64 := text_clamp t n in
        let r : Text := { s := t.s, pos := t.pos, end := t.pos + m } in r
    def input_scan (pred : U8 -> Bool) (t : Text) : I64 :=
        scan_text_go pred t.s 0 (Text.remaining t)
    def input_text (n : I64) (t : Text) : String :=
        String.slice t.s 0 (text_clamp t n)
    def input_starts_with (lit : String) (t : Text) : Bool :=
        if I64.gt (String.length lit) (Text.remaining t) then false
        else String.starts_with lit t.s
}

// ─── Bytes instance ──────────────────────────────────────────────────

def bytes_remaining (s : Bytes) : I64 :=
    if I64.lt s.pos s.end then s.end - s.pos else 0

def bytes_clamp (s : Bytes) (n : I64) : I64 :=
    if I64.lt n 0 then 0
    else if I64.gt n (bytes_remaining s) then bytes_remaining s
    else n

/// Count leading bytes matching `pred`, indexing the buffer. `Buf.get_u8` is
/// bounds-checked and answers 0 out of range, so the loop needs no separate
/// end test beyond `limit`.
///
/// `limit` is an ABSOLUTE index and `n` is the count, so a cursor whose `pos`
/// is not 0 answers a COUNT -- the same contract as `scan_text_go` (and what
/// every caller, `bytes_while` included, assumes). Returning the index here
/// made a bounded span report its start offset as the run length, so a scan
/// over a string table turned every name into the rest of the table.
#[partial]
def scan_bytes_go (pred : U8 -> Bool) (b : Shared (Buf U8)) (i : I64) (limit : I64) (n : I64) : I64 :=
    if not (I64.lt i limit)
    then n
    else if pred (Buf.get_u8 b i)
    then scan_bytes_go pred b (i + 1) limit (n + 1)
    else n

/// The `[from, to)` bytes of the buffer as a cons list, reversed-accumulated
/// so the loop is self-tail-recursive.
#[partial]
def bytes_list_go (b : Shared (Buf U8)) (i : I64) (to : I64) (acc : List U8) : List U8 :=
    if not (I64.lt i to)
    then List.reverse acc
    else bytes_list_go b (i + 1) to (List.cons (Buf.get_u8 b i) acc)

/// The first `n` bytes of the cursor as a `String`.
pub def Bytes.text (s : Bytes) (n : I64) : String :=
    let m : I64 := bytes_clamp s n in
    String.from_list (bytes_list_go s.b s.pos (s.pos + m) List.empty)

pub instance Input Bytes {
    def input_len (s : Bytes) : I64 := bytes_remaining s
    def input_offset (s : Bytes) : I64 := s.pos
    def input_head (s : Bytes) : Option U8 :=
        if not (I64.lt s.pos s.end) then Option.none else Option.some (Buf.get_u8 s.b s.pos)
    def input_byte_at (n : I64) (s : Bytes) : Option U8 :=
        if I64.lt n 0 then Option.none
        else if not (I64.lt n (bytes_remaining s)) then Option.none
        else Option.some (Buf.get_u8 s.b (s.pos + n))
    def input_advance (n : I64) (s : Bytes) : Bytes :=
        let m : I64 := bytes_clamp s n in
        let r : Bytes := { b := s.b, pos := s.pos + m, end := s.end } in r
    def input_slice (n : I64) (s : Bytes) : Bytes :=
        let m : I64 := bytes_clamp s n in
        let r : Bytes := { b := s.b, pos := s.pos, end := s.pos + m } in r
    def input_scan (pred : U8 -> Bool) (s : Bytes) : I64 :=
        scan_bytes_go pred s.b s.pos (s.pos + bytes_remaining s) 0
    def input_text (n : I64) (s : Bytes) : String := Bytes.text s n
    def input_starts_with (lit : String) (s : Bytes) : Bool :=
        String.beq (Bytes.text s (String.length lit)) lit
}
